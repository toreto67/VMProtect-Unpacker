#include "static_iat.hxx"
#define WIN32_LEAN_AND_MEAN
#define NOMINMAX
#include <windows.h>
#include <winternl.h>
#include <intrin.h>
#include <unicorn/unicorn.h>
#include <Zydis/Zydis.h>
#include <algorithm>
#include <array>
#include <chrono>
#include <cctype>
#include <cmath>
#include <cstdio>
#include <cstring>
#include <fstream>
#include <map>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>

namespace
{
    using bytes = std::vector< std::uint8_t >;
    constexpr std::uint64_t teb = 0x7fd00000, peb = teb + 0x1000, ldr = teb + 0x2000;
    constexpr std::uint64_t stack = 0x70000000, heap = 0x400000000;
    constexpr std::uint64_t heap_size = 0x2000000;
    auto require( bool ok, const char* text ) -> void { if ( !ok ) throw std::runtime_error( text ); }
    auto check( uc_err e ) -> void { if ( e != UC_ERR_OK ) throw std::runtime_error( uc_strerror( e ) ); }
    auto fits( std::size_t n, std::uint64_t off, std::uint64_t len ) -> bool { return off <= n && len <= n - off; }
    template< typename T > auto get( const bytes& b, std::uint64_t off ) -> T
    {
        require( fits( b.size( ), off, sizeof( T ) ), "truncated PE data" );
        T v; std::memcpy( &v, b.data( ) + off, sizeof( v ) ); return v;
    }
    template< typename T > auto put( bytes& b, std::uint64_t off, T v ) -> void
    {
        require( fits( b.size( ), off, sizeof( T ) ), "PE write outside image" );
        std::memcpy( b.data( ) + off, &v, sizeof( v ) );
    }
    auto lower( std::string s ) -> std::string
    {
        for ( auto& c : s ) c = static_cast< char >( std::tolower( static_cast< unsigned char >( c ) ) );
        return s;
    }
    auto string_at( const bytes& b, std::uint64_t at ) -> std::string
    {
        std::string s;
        for ( unsigned i = 0; i < 4096; ++i )
        {
            auto c = get< char >( b, at + i );
            if ( !c ) return s;
            s += c;
        }
        throw std::runtime_error( "unterminated PE string" );
    }
    auto dll_basename( std::string name ) -> std::string
    {
        name = lower( std::move( name ) );
        auto slash = name.find_last_of( "\\/" );
        if ( slash != std::string::npos ) name.erase( 0, slash + 1 );
        if ( name.size( ) >= 4 && name.compare( name.size( ) - 4, 4, ".dll" ) == 0 )
            name.erase( name.size( ) - 4 );
        return name;
    }
    auto is_api_set_name( const std::string& name ) -> bool
    {
        return name.rfind( "api-ms-", 0 ) == 0 || name.rfind( "ext-ms-", 0 ) == 0;
    }
    auto host_api_set_map( ) -> const bytes&
    {
        static bytes map;
        static bool ready = false;
        if ( ready ) return map;
        PROCESS_BASIC_INFORMATION pbi{};
        ULONG ret{};
        using query_fn = LONG( WINAPI* )( HANDLE, ULONG, PVOID, ULONG, PULONG );
        auto query = reinterpret_cast< query_fn >( GetProcAddress( GetModuleHandleW( L"ntdll.dll" ), "NtQueryInformationProcess" ) );
        require( query && query( GetCurrentProcess( ), 0, &pbi, sizeof( pbi ), &ret ) == 0 && pbi.PebBaseAddress, "cannot locate host PEB" );
        auto* host_peb = reinterpret_cast< const std::uint8_t* >( pbi.PebBaseAddress );
        std::uint64_t map_va{};
        std::memcpy( &map_va, host_peb + 0x68, sizeof( map_va ) );
        require( map_va, "host ApiSetMap is missing" );
        auto* hdr = reinterpret_cast< const std::uint32_t* >( static_cast< std::uintptr_t >( map_va ) );
        require( hdr[ 0 ] >= 6 && hdr[ 1 ] >= 28 && hdr[ 1 ] <= 2u * 1024 * 1024, "unsupported host ApiSetMap" );
        map.assign( reinterpret_cast< const std::uint8_t* >( map_va ), reinterpret_cast< const std::uint8_t* >( map_va ) + hdr[ 1 ] );
        ready = true;
        return map;
    }
    auto utf16_ascii( const bytes& b, std::uint32_t off, std::uint32_t len ) -> std::string
    {
        require( !( len & 1 ) && fits( b.size( ), off, len ), "truncated ApiSetMap string" );
        std::string s;
        s.reserve( len / 2 );
        for ( std::uint32_t i = 0; i < len; i += 2 )
        {
            auto c = get< std::uint16_t >( b, off + i );
            require( c && c < 128, "unsupported ApiSetMap character" );
            s += static_cast< char >( c );
        }
        return lower( s );
    }
    auto api_set_hash( const std::string& name, std::uint32_t factor ) -> std::uint32_t
    {
        std::uint32_t h = 0;
        for ( unsigned char c : name )
            h = h * factor + c;
        return h;
    }
    auto lookup_api_set( const std::string& requested, const std::string& importer = {} ) -> std::string
    {
        auto name = dll_basename( requested );
        if ( !is_api_set_name( name ) ) return {};
        const auto& map = host_api_set_map( );
        auto version = get< std::uint32_t >( map, 0 );
        auto count = get< std::uint32_t >( map, 12 );
        auto entry_off = get< std::uint32_t >( map, 16 );
        auto hash_off = get< std::uint32_t >( map, 20 );
        auto factor = get< std::uint32_t >( map, 24 );
        require( version >= 6 && count && count <= 4096 && fits( map.size( ), hash_off, count * 8ull ) &&
            fits( map.size( ), entry_off, count * 24ull ), "invalid host ApiSetMap" );
        auto hyphen = name.rfind( '-' );
        auto key = hyphen == std::string::npos ? name : name.substr( 0, hyphen );
        auto hash = api_set_hash( key, factor );
        std::int32_t lo = 0, hi = static_cast< std::int32_t >( count ) - 1, idx = -1;
        while ( lo <= hi )
        {
            auto mid = lo + ( hi - lo ) / 2;
            auto h = get< std::uint32_t >( map, hash_off + static_cast< std::uint64_t >( mid ) * 8 );
            if ( h < hash ) lo = mid + 1;
            else if ( h > hash ) hi = mid - 1;
            else { idx = static_cast< std::int32_t >( get< std::uint32_t >( map, hash_off + static_cast< std::uint64_t >( mid ) * 8 + 4 ) ); break; }
        }
        if ( idx < 0 )
        {
            for ( std::uint32_t i = 0; i < count; ++i )
            {
                auto name_off = get< std::uint32_t >( map, entry_off + i * 24ull + 4 );
                auto hashed_len = get< std::uint32_t >( map, entry_off + i * 24ull + 12 );
                try
                {
                    if ( utf16_ascii( map, name_off, hashed_len ) == key ) { idx = static_cast< std::int32_t >( i ); break; }
                }
                catch ( const std::exception& ) {}
            }
        }
        require( idx >= 0 && static_cast< std::uint32_t >( idx ) < count, ( "unknown API set " + requested ).c_str( ) );
        auto rec = entry_off + static_cast< std::uint64_t >( idx ) * 24;
        auto value_off = get< std::uint32_t >( map, rec + 16 );
        auto value_count = get< std::uint32_t >( map, rec + 20 );
        require( value_count && fits( map.size( ), value_off, value_count * 20ull ), "empty API set host list" );
        auto value_host = [ & ]( std::uint32_t i ) -> std::string
        {
            auto off = get< std::uint32_t >( map, value_off + i * 20ull + 12 );
            auto len = get< std::uint32_t >( map, value_off + i * 20ull + 16 );
            if ( !len ) return {};
            auto host = utf16_ascii( map, off, len );
            if ( !host.empty( ) && host.find( '.' ) == std::string::npos ) host += ".dll";
            return host;
        };
        auto host = value_host( 0 );
        const auto parent = dll_basename( importer );
        if ( !parent.empty( ) && value_count > 1 )
        {
            for ( std::uint32_t i = 1; i < value_count; ++i )
            {
                auto name_off = get< std::uint32_t >( map, value_off + i * 20ull + 4 );
                auto name_len = get< std::uint32_t >( map, value_off + i * 20ull + 8 );
                if ( !name_len ) continue;
                try
                {
                    if ( dll_basename( utf16_ascii( map, name_off, name_len ) ) == parent )
                    {
                        auto mapped = value_host( i );
                        if ( !mapped.empty( ) ) host = std::move( mapped );
                        break;
                    }
                }
                catch ( const std::exception& ) {}
            }
        }
        if ( !parent.empty( ) && dll_basename( host ) == parent )
        {
            for ( std::uint32_t i = 0; i < value_count; ++i )
            {
                try
                {
                    auto mapped = value_host( i );
                    if ( !mapped.empty( ) && dll_basename( mapped ) != parent )
                    {
                        host = std::move( mapped );
                        break;
                    }
                }
                catch ( const std::exception& ) {}
            }
        }
        require( !host.empty( ), "empty API set host" );
        return host;
    }
    auto fallback_api_set_host( const std::string& requested ) -> std::string
    {
        auto name = dll_basename( requested );
        if ( name.find( "-crt-" ) != std::string::npos ) return "ucrtbase.dll";
        if ( name.find( "-core-com" ) != std::string::npos || name.find( "-downlevel-ole32" ) != std::string::npos )
            return "combase.dll";
        if ( name.find( "-ole32" ) != std::string::npos ) return "ole32.dll";
        return "kernelbase.dll";
    }
    auto resolve_module_name( std::string name, std::string importer = {} ) -> std::string
    {
        name = lower( std::move( name ) );
        auto slash = name.find_last_of( "\\/" );
        if ( slash != std::string::npos ) name.erase( 0, slash + 1 );
        require( !name.empty( ) && name.find_first_of( "/\\:" ) == std::string::npos && name.find( ".." ) == std::string::npos,
            "guest DLL path is not a basename" );
        if ( name.find( '.' ) == std::string::npos ) name += ".dll";
        if ( !is_api_set_name( name ) ) return name;
        try { return lookup_api_set( name, importer ); }
        catch ( const std::exception& )
        {
            auto host = fallback_api_set_host( name );
            if ( dll_basename( host ) == dll_basename( importer ) && dll_basename( importer ) == "kernel32" )
                return "kernelbase.dll";
            return host;
        }
    }
    auto crc32_ieee( std::uint32_t crc, const std::uint8_t* p, std::size_t n ) -> std::uint32_t
    {
        static std::uint32_t tab[ 256 ]{};
        static bool ready = false;
        if ( !ready )
        {
            for ( unsigned i = 0; i < 256; ++i )
            {
                auto x = i;
                for ( unsigned b = 0; b < 8; ++b )
                    x = ( x & 1 ) ? ( x >> 1 ) ^ 0xedb88320u : x >> 1;
                tab[ i ] = x;
            }
            ready = true;
        }
        for ( std::size_t i = 0; i < n; ++i )
            crc = tab[ ( crc ^ p[ i ] ) & 0xff ] ^ ( crc >> 8 );
        return crc;
    }
    auto masked_crc32_table( const bytes& b, std::uint64_t at ) -> bool
    {
        static constexpr std::uint32_t head[] = {
            0x00000000u, 0x77073096u, 0xee0e612cu, 0x990951bau,
            0x076dc419u, 0x706af48fu, 0xe963a535u, 0x9e6495a3u
        };
        if ( !fits( b.size( ), at, sizeof( head ) ) ) return false;
        auto key = get< std::uint32_t >( b, at );
        for ( unsigned i = 1; i < 8; ++i )
            if ( ( get< std::uint32_t >( b, at + i * 4 ) ^ key ) != head[ i ] ) return false;
        return true;
    }
    struct pe
    {
        std::uint32_t opt, section, size, headers, entry;
        std::uint64_t base;
        std::uint16_t count;
        std::array< IMAGE_DATA_DIRECTORY, 16 > dirs;
    };
    auto parse( const bytes& b ) -> pe
    {
        require( get< std::uint16_t >( b, 0 ) == IMAGE_DOS_SIGNATURE, "invalid DOS signature" );
        auto nt = get< std::uint32_t >( b, 0x3c );
        require( nt >= 64 && fits( b.size( ), nt, 24 ), "invalid NT header offset" );
        require( get< std::uint32_t >( b, nt ) == IMAGE_NT_SIGNATURE, "invalid NT signature" );
        auto opt = nt + 24;
        auto os = get< std::uint16_t >( b, nt + 20 );
        require( os >= sizeof( IMAGE_OPTIONAL_HEADER64 ) && fits( b.size( ), opt, os ), "invalid optional header" );
        require( get< std::uint16_t >( b, opt ) == IMAGE_NT_OPTIONAL_HDR64_MAGIC &&
            get< std::uint16_t >( b, nt + 4 ) == IMAGE_FILE_MACHINE_AMD64, "offline IAT initialization currently supports AMD64 PE files only" );
        pe p{};
        p.opt = opt; p.section = opt + os; p.count = get< std::uint16_t >( b, nt + 6 );
        p.size = get< std::uint32_t >( b, opt + 56 ); p.headers = get< std::uint32_t >( b, opt + 60 );
        p.entry = get< std::uint32_t >( b, opt + 16 ); p.base = get< std::uint64_t >( b, opt + 24 );
        require( p.count && p.count <= 96 && fits( b.size( ), p.section, p.count * 40 ), "invalid section table" );
        require( p.size && p.size <= 256u * 1024 * 1024 && p.headers <= p.size && p.headers <= b.size( ) && p.entry < p.size,
            "invalid image dimensions" );
        require( get< std::uint32_t >( b, opt + 108 ) >= 16, "missing PE data directories" );
        for ( unsigned i = 0; i < 16; ++i ) p.dirs[ i ] = get< IMAGE_DATA_DIRECTORY >( b, opt + 112 + i * 8 );
        return p;
    }
    auto mapped( const bytes& raw, const pe& p ) -> bytes
    {
        bytes b( ( static_cast< std::size_t >( p.size ) + 4095 ) & ~std::size_t( 4095 ) );
        std::memcpy( b.data( ), raw.data( ), p.headers );
        for ( unsigned i = 0; i < p.count; ++i )
        {
            auto s = get< IMAGE_SECTION_HEADER >( raw, p.section + i * 40 );
            if ( !s.SizeOfRawData ) continue;
            require( fits( raw.size( ), s.PointerToRawData, s.SizeOfRawData ) && fits( p.size, s.VirtualAddress, s.SizeOfRawData ), "section outside PE bounds" );
            std::memcpy( b.data( ) + s.VirtualAddress, raw.data( ) + s.PointerToRawData, s.SizeOfRawData );
        }
        return b;
    }
    auto read_file( const std::string& path ) -> bytes
    {
        std::ifstream f( path, std::ios::binary | std::ios::ate );
        require( !!f, ( "cannot read system DLL: " + path ).c_str( ) );
        auto n = f.tellg( );
        require( n > 0 && n <= 256 * 1024 * 1024, "invalid DLL size" );
        bytes b( static_cast< std::size_t >( n ) ); f.seekg( 0 );
        require( !!f.read( reinterpret_cast< char* >( b.data( ) ), n ), "cannot read DLL bytes" );
        return b;
    }
    auto relocate( bytes& image, const pe& header, std::uint64_t dest ) -> void
    {
        if ( dest == header.base ) return;
        auto dir = header.dirs[ IMAGE_DIRECTORY_ENTRY_BASERELOC ];
        if ( !dir.Size ) return;
        require( fits( image.size( ), dir.VirtualAddress, dir.Size ), "invalid relocation directory" );
        auto delta = static_cast< std::int64_t >( dest - header.base );
        auto at = std::uint64_t( dir.VirtualAddress );
        auto end = at + dir.Size;
        while ( at + sizeof( IMAGE_BASE_RELOCATION ) <= end )
        {
            auto block = get< IMAGE_BASE_RELOCATION >( image, at );
            if ( !block.SizeOfBlock ) break;
            require( block.SizeOfBlock >= sizeof( IMAGE_BASE_RELOCATION ) && at + block.SizeOfBlock <= end, "truncated relocation block" );
            auto count = ( block.SizeOfBlock - sizeof( IMAGE_BASE_RELOCATION ) ) / 2;
            for ( unsigned i = 0; i < count; ++i )
            {
                auto entry = get< std::uint16_t >( image, at + sizeof( IMAGE_BASE_RELOCATION ) + i * 2 );
                auto type = entry >> 12;
                auto offset = entry & 0xfff;
                if ( type == IMAGE_REL_BASED_ABSOLUTE ) continue;
                require( type == IMAGE_REL_BASED_DIR64, "unsupported relocation type" );
                auto loc = std::uint64_t( block.VirtualAddress ) + offset;
                put< std::uint64_t >( image, loc, static_cast< std::uint64_t >( static_cast< std::int64_t >( get< std::uint64_t >( image, loc ) ) + delta ) );
            }
            at += block.SizeOfBlock;
        }
    }
    struct checksum_site
    {
        std::uint64_t address{}, table{};
        int pointer_reg = UC_X86_REG_INVALID;
        int count_reg = UC_X86_REG_INVALID;
        int table_reg = UC_X86_REG_INVALID;
    };
    auto zydis_reg( ZydisRegister r ) -> int
    {
        switch ( r )
        {
        case ZYDIS_REGISTER_RAX: case ZYDIS_REGISTER_EAX: case ZYDIS_REGISTER_AX: case ZYDIS_REGISTER_AL: return UC_X86_REG_RAX;
        case ZYDIS_REGISTER_RCX: case ZYDIS_REGISTER_ECX: case ZYDIS_REGISTER_CX: case ZYDIS_REGISTER_CL: return UC_X86_REG_RCX;
        case ZYDIS_REGISTER_RDX: case ZYDIS_REGISTER_EDX: case ZYDIS_REGISTER_DX: case ZYDIS_REGISTER_DL: return UC_X86_REG_RDX;
        case ZYDIS_REGISTER_RBX: case ZYDIS_REGISTER_EBX: case ZYDIS_REGISTER_BX: case ZYDIS_REGISTER_BL: return UC_X86_REG_RBX;
        case ZYDIS_REGISTER_RSP: case ZYDIS_REGISTER_ESP: case ZYDIS_REGISTER_SP: return UC_X86_REG_RSP;
        case ZYDIS_REGISTER_RBP: case ZYDIS_REGISTER_EBP: case ZYDIS_REGISTER_BP: return UC_X86_REG_RBP;
        case ZYDIS_REGISTER_RSI: case ZYDIS_REGISTER_ESI: case ZYDIS_REGISTER_SI: return UC_X86_REG_RSI;
        case ZYDIS_REGISTER_RDI: case ZYDIS_REGISTER_EDI: case ZYDIS_REGISTER_DI: return UC_X86_REG_RDI;
        case ZYDIS_REGISTER_R8: case ZYDIS_REGISTER_R8D: case ZYDIS_REGISTER_R8W: case ZYDIS_REGISTER_R8B: return UC_X86_REG_R8;
        case ZYDIS_REGISTER_R9: case ZYDIS_REGISTER_R9D: case ZYDIS_REGISTER_R9W: case ZYDIS_REGISTER_R9B: return UC_X86_REG_R9;
        case ZYDIS_REGISTER_R10: case ZYDIS_REGISTER_R10D: case ZYDIS_REGISTER_R10W: case ZYDIS_REGISTER_R10B: return UC_X86_REG_R10;
        case ZYDIS_REGISTER_R11: case ZYDIS_REGISTER_R11D: case ZYDIS_REGISTER_R11W: case ZYDIS_REGISTER_R11B: return UC_X86_REG_R11;
        case ZYDIS_REGISTER_R12: case ZYDIS_REGISTER_R12D: case ZYDIS_REGISTER_R12W: case ZYDIS_REGISTER_R12B: return UC_X86_REG_R12;
        case ZYDIS_REGISTER_R13: case ZYDIS_REGISTER_R13D: case ZYDIS_REGISTER_R13W: case ZYDIS_REGISTER_R13B: return UC_X86_REG_R13;
        case ZYDIS_REGISTER_R14: case ZYDIS_REGISTER_R14D: case ZYDIS_REGISTER_R14W: case ZYDIS_REGISTER_R14B: return UC_X86_REG_R14;
        case ZYDIS_REGISTER_R15: case ZYDIS_REGISTER_R15D: case ZYDIS_REGISTER_R15W: case ZYDIS_REGISTER_R15B: return UC_X86_REG_R15;
        default: return UC_X86_REG_INVALID;
        }
    }
    struct dll
    {
        std::uint64_t base{};
        bytes image;
        IMAGE_DATA_DIRECTORY exports{};
        std::map< std::string, std::uint32_t > names;
        std::map< std::uint32_t, std::uint32_t > ordinals;
    };
    struct engine
    {
        uc_engine* uc{};
        ~engine( ) { if ( uc ) uc_close( uc ); }
    };
    class loader
    {
        engine vm;
        pe p;
        bytes image;
        std::map< std::string, dll > dlls;
        std::map< std::uint64_t, std::pair< std::string, std::string > > apis;
        std::map< std::uint32_t, std::uint64_t > syscalls;
        std::map< std::uint64_t, std::uint64_t > handles;
        std::vector< export_sym > exports;
        std::vector< std::pair< std::uint32_t, std::uint32_t > > original_code;
        std::vector< checksum_site > checksum_sites;
        std::uint64_t heap_next = heap + 0x1000, ticks = 1000000;
        std::uint64_t original_begin{}, original_end{};
        bool in_syscall = false, hidden = false, done = false;
        std::string failure;
        std::uint32_t oep{}, restored_entry{}, checksum_skips{};
        std::size_t restored_dwords{};

        auto reg( int r ) -> std::uint64_t { std::uint64_t v{}; check( uc_reg_read( vm.uc, r, &v ) ); return v; }
        auto reg( int r, std::uint64_t v ) -> void { check( uc_reg_write( vm.uc, r, &v ) ); }
        template< typename T > auto read( std::uint64_t a ) -> T { T v{}; check( uc_mem_read( vm.uc, a, &v, sizeof( v ) ) ); return v; }
        template< typename T > auto write( std::uint64_t a, T v ) -> void { check( uc_mem_write( vm.uc, a, &v, sizeof( v ) ) ); }
        auto w64( std::uint64_t a, std::uint64_t v ) -> void { write( a, v ); }
        auto w32( std::uint64_t a, std::uint32_t v ) -> void { write( a, v ); }
        auto zero( std::uint64_t a, std::size_t n ) -> void
        {
            require( n <= heap_size, "guest buffer exceeds limit" ); bytes b( n ); check( uc_mem_write( vm.uc, a, b.data( ), b.size( ) ) );
        }
        auto accessible( std::uint64_t a, std::uint64_t n ) -> bool
        {
            if ( n > heap_size || a + n < a ) return false;
            uc_mem_region* regions{}; std::uint32_t count{};
            if ( uc_mem_regions( vm.uc, &regions, &count ) != UC_ERR_OK ) return false;
            bool ok = false;
            for ( unsigned i = 0; i < count; ++i )
                if ( a >= regions[ i ].begin && a <= regions[ i ].end && n <= regions[ i ].end - a + 1 ) ok = true;
            uc_free( regions ); return ok;
        }
        auto text( std::uint64_t a, bool wide = false ) -> std::string
        {
            if ( !a ) return {};
            std::string s;
            for ( unsigned i = 0; i < 4096; ++i )
            {
                auto c = wide ? read< std::uint16_t >( a + i * 2 ) : read< std::uint8_t >( a + i );
                if ( !c ) return s;
                require( c < 128, "unsupported non-ASCII guest module name" ); s += static_cast< char >( c );
            }
            throw std::runtime_error( "unterminated guest string" );
        }
        auto allocate( std::uint64_t n ) -> std::uint64_t
        {
            require( n && n <= heap_size && heap_next + n + 15 <= heap + heap_size, "offline heap limit exceeded" );
            auto result = heap_next; heap_next += ( n + 15 ) & ~15ull; zero( result, static_cast< std::size_t >( n ) ); return result;
        }
        auto module_name( std::uint64_t base ) -> std::string
        {
            for ( const auto& kv : dlls ) if ( kv.second.base == base ) return kv.first;
            throw std::runtime_error( "unknown emulated DLL handle" );
        }
        using ntstatus_t = LONG;
        using nt_query5_fn = ntstatus_t ( NTAPI* )( HANDLE, ULONG, PVOID, ULONG, PULONG );
        using nt_set4_fn = ntstatus_t ( NTAPI* )( HANDLE, ULONG, PVOID, ULONG );
        auto host_ntdll( ) -> HMODULE
        {
            static auto m = GetModuleHandleW( L"ntdll.dll" );
            require( m, "host ntdll is missing" );
            return m;
        }
        auto host_proc( const char* name ) -> FARPROC
        {
            auto p = GetProcAddress( host_ntdll( ), name );
            if ( !p && name[ 0 ] == 'N' && name[ 1 ] == 't' )
            {
                std::string zw = name;
                zw[ 0 ] = 'Z'; zw[ 1 ] = 'w';
                p = GetProcAddress( host_ntdll( ), zw.c_str( ) );
            }
            return p;
        }
        auto host_handle( std::uint64_t guest ) -> HANDLE
        {
            if ( guest == ~std::uint64_t( 0 ) || guest == 0 ) return GetCurrentProcess( );
            if ( guest == ~std::uint64_t( 1 ) ) return GetCurrentThread( );
            auto it = handles.find( guest );
            if ( it != handles.end( ) && !it->second ) return GetCurrentProcess( );
            return GetCurrentProcess( );
        }
        auto rewrite_host_pointers( bytes& buf ) -> void
        {
            std::uint64_t host_peb = 0, host_teb = 0;
            PROCESS_BASIC_INFORMATION pbi{};
            ULONG ret{};
            using query_fn = LONG( WINAPI* )( HANDLE, ULONG, PVOID, ULONG, PULONG );
            auto query = reinterpret_cast< query_fn >( host_proc( "NtQueryInformationProcess" ) );
            if ( query && query( GetCurrentProcess( ), 0, &pbi, sizeof( pbi ), &ret ) == 0 )
                host_peb = reinterpret_cast< std::uint64_t >( pbi.PebBaseAddress );
            host_teb = reinterpret_cast< std::uint64_t >( NtCurrentTeb( ) );
            for ( std::size_t i = 0; i + 8 <= buf.size( ); i += 8 )
            {
                std::uint64_t v{};
                std::memcpy( &v, buf.data( ) + i, 8 );
                if ( host_peb && v == host_peb ) v = peb;
                else if ( host_teb && v >= ( host_teb & ~0xfffull ) && v < ( host_teb & ~0xfffull ) + 0x2000 )
                    v = teb + ( v - host_teb );
                else
                    continue;
                std::memcpy( buf.data( ) + i, &v, 8 );
            }
        }
        auto query_information( const std::string& api, HANDLE object, ULONG cls, std::uint64_t buf, ULONG len, std::uint64_t retlen ) -> void
        {
            constexpr std::uint64_t success = 0;
            constexpr std::uint64_t info_length_mismatch = 0xc0000004u;
            constexpr std::uint64_t access_violation = 0xc0000005u;
            constexpr std::uint64_t port_not_set = 0xc0000353u;
            if ( retlen && !accessible( retlen, 4 ) ) { result( access_violation ); return; }
            if ( api.find( "Process" ) != std::string::npos )
            {
                if ( cls == 7 || cls == 0x1e || cls == 0x1a )
                {
                    if ( len < 8 ) { if ( retlen ) w32( retlen, 8 ); result( info_length_mismatch ); return; }
                    if ( !accessible( buf, 8 ) ) { result( access_violation ); return; }
                    w64( buf, 0 );
                    if ( retlen ) w32( retlen, 8 );
                    result( cls == 0x1e ? port_not_set : success );
                    return;
                }
                if ( cls == 0x1f || cls == 12 )
                {
                    if ( len < 4 ) { if ( retlen ) w32( retlen, 4 ); result( info_length_mismatch ); return; }
                    if ( !accessible( buf, 4 ) ) { result( access_violation ); return; }
                    w32( buf, 1 );
                    if ( retlen ) w32( retlen, 4 );
                    result( success );
                    return;
                }
                if ( cls == 0 )
                {
                    if ( len < 48 ) { if ( retlen ) w32( retlen, 48 ); result( info_length_mismatch ); return; }
                    if ( !accessible( buf, 48 ) ) { result( access_violation ); return; }
                    zero( buf, 48 ); w64( buf + 8, peb ); w64( buf + 32, 0x1234 ); w64( buf + 40, 0x1111 );
                    if ( retlen ) w32( retlen, 48 );
                    result( success );
                    return;
                }
            }
            if ( api.find( "Thread" ) != std::string::npos )
            {
                if ( cls == 0x11 )
                {
                    if ( len < 1 ) { if ( retlen ) w32( retlen, 1 ); result( info_length_mismatch ); return; }
                    if ( !accessible( buf, 1 ) ) { result( access_violation ); return; }
                    write< std::uint8_t >( buf, hidden ? 1 : 0 );
                    if ( retlen ) w32( retlen, 1 );
                    result( success );
                    return;
                }
                if ( cls == 0 )
                {
                    if ( len < 0x30 ) { if ( retlen ) w32( retlen, 0x30 ); result( info_length_mismatch ); return; }
                    if ( !accessible( buf, 0x30 ) ) { result( access_violation ); return; }
                    zero( buf, 0x30 );
                    w32( buf, 0x103 );
                    w64( buf + 8, teb );
                    w64( buf + 0x10, 0x1234 );
                    w64( buf + 0x18, 0x5678 );
                    w64( buf + 0x20, 1 );
                    if ( retlen ) w32( retlen, 0x30 );
                    result( success );
                    return;
                }
            }
            auto fn = reinterpret_cast< nt_query5_fn >( host_proc( api.c_str( ) ) );
            if ( !fn )
            {
                if ( len && accessible( buf, len ) ) zero( buf, len );
                if ( retlen ) w32( retlen, len );
                result( success );
                return;
            }
            bytes scratch( len ? len : 1 );
            ULONG written = 0;
            auto status = fn( object, cls, scratch.data( ), len, &written );
            if ( status == static_cast< ntstatus_t >( 0xC0000004 ) )
            {
                if ( retlen ) w32( retlen, written );
                result( info_length_mismatch );
                return;
            }
            if ( status >= 0 && len && accessible( buf, len ) )
            {
                rewrite_host_pointers( scratch );
                check( uc_mem_write( vm.uc, buf, scratch.data( ), len ) );
            }
            if ( retlen ) w32( retlen, written ? written : len );
            result( static_cast< std::uint64_t >( static_cast< std::uint32_t >( status ) ) );
        }
        auto set_information( const std::string& api, HANDLE object, ULONG cls, std::uint64_t buf, ULONG len ) -> void
        {
            constexpr std::uint64_t success = 0;
            constexpr std::uint64_t info_length_mismatch = 0xc0000004u;
            constexpr std::uint64_t invalid_handle = 0xc0000008u;
            if ( api.find( "Thread" ) != std::string::npos && cls == 0x11 )
            {
                if ( len ) result( info_length_mismatch );
                else if ( argument( 0 ) != ~std::uint64_t( 1 ) && argument( 0 ) != ~std::uint64_t( 0 ) ) result( invalid_handle );
                else { hidden = true; result( success ); }
                return;
            }
            auto fn = reinterpret_cast< nt_set4_fn >( host_proc( api.c_str( ) ) );
            if ( !fn ) { result( success ); return; }
            bytes scratch( len );
            if ( len && accessible( buf, len ) )
                check( uc_mem_read( vm.uc, buf, scratch.data( ), len ) );
            auto status = fn( object, cls, len ? scratch.data( ) : nullptr, len );
            result( static_cast< std::uint64_t >( static_cast< std::uint32_t >( status ) ) );
        }
        auto load( std::string name, std::string importer = {} ) -> std::uint64_t
        {
            name = resolve_module_name( std::move( name ), std::move( importer ) );
            auto old = dlls.find( name ); if ( old != dlls.end( ) ) return old->second.base;
            require( dlls.size( ) < 256, "offline DLL limit exceeded" );
            char sysdir[ MAX_PATH ]; require( GetSystemDirectoryA( sysdir, MAX_PATH ) < MAX_PATH, "cannot locate System32" );
            auto raw = read_file( std::string( sysdir ) + "\\" + name ); auto header = parse( raw );
            dll d{}; d.base = 0x180000000ull + dlls.size( ) * 0x2000000ull; d.image = mapped( raw, header ); d.exports = header.dirs[ 0 ];
            relocate( d.image, header, d.base );
            require( d.image.size( ) <= 0x2000000, "DLL exceeds emulated address slot" );
            require( d.exports.Size && fits( d.image.size( ), d.exports.VirtualAddress, d.exports.Size ), "invalid DLL exports" );
            auto e = get< IMAGE_EXPORT_DIRECTORY >( d.image, d.exports.VirtualAddress );
            require( e.NumberOfFunctions <= 100000 && e.NumberOfNames <= 100000, "excessive DLL exports" );
            for ( unsigned i = 0; i < e.NumberOfNames; ++i )
            {
                auto index = get< std::uint16_t >( d.image, e.AddressOfNameOrdinals + std::uint64_t( i ) * 2 );
                require( index < e.NumberOfFunctions, "invalid export ordinal index" );
                d.names[ string_at( d.image, get< std::uint32_t >( d.image, e.AddressOfNames + std::uint64_t( i ) * 4 ) ) ] = e.Base + index;
            }
            for ( unsigned i = 0; i < e.NumberOfFunctions; ++i )
            {
                auto rva = get< std::uint32_t >( d.image, e.AddressOfFunctions + std::uint64_t( i ) * 4 );
                if ( !rva ) continue;
                require( rva < d.image.size( ), "invalid export RVA" ); d.ordinals[ e.Base + i ] = rva;
                if ( rva >= d.exports.VirtualAddress && rva - d.exports.VirtualAddress < d.exports.Size ) continue;
                std::vector< std::string > names;
                for ( const auto& kv : d.names ) if ( kv.second == e.Base + i ) names.push_back( kv.first );
                if ( names.empty( ) ) names.emplace_back( );
                for ( const auto& symbol : names )
                {
                    exports.push_back( { name, symbol, e.Base + i, d.base + rva } );
                    apis.emplace( d.base + rva, std::make_pair( name, symbol.empty( ) ? "#" + std::to_string( e.Base + i ) : symbol ) );
                }
                if ( name == "ntdll.dll" && fits( d.image.size( ), rva, 8 ) && get< std::uint32_t >( d.image, rva ) == 0xb8d18b4c )
                    syscalls[ get< std::uint32_t >( d.image, rva + 4 ) ] = d.base + rva;
            }
            auto result = d.base;
            auto& stored = dlls.emplace( name, std::move( d ) ).first->second;
            check( uc_mem_map_ptr( vm.uc, result, stored.image.size( ), UC_PROT_ALL, stored.image.data( ) ) );
            uc_hook api_hook{};
            check( uc_hook_add( vm.uc, &api_hook, UC_HOOK_BLOCK, reinterpret_cast< void* >( on_block ), this,
                result, result + stored.image.size( ) - 1 ) );
            std::printf( "offline: mapped %s\n", name.c_str( ) ); std::fflush( stdout ); return result;
        }
        auto find_export_ordinal( const dll& d, const std::string& symbol ) -> std::uint32_t
        {
            if ( !symbol.empty( ) && symbol[ 0 ] == '#' )
                return static_cast< std::uint32_t >( std::stoul( symbol.substr( 1 ) ) );
            auto it = d.names.find( symbol );
            if ( it != d.names.end( ) ) return it->second;
            auto want = lower( symbol );
            for ( const auto& kv : d.names )
                if ( lower( kv.first ) == want ) return kv.second;
            throw std::runtime_error( "missing export " + symbol );
        }
        auto resolve( const std::string& name, const std::string& symbol, unsigned depth = 0,
            std::set< std::pair< std::string, std::string > >* seen = nullptr, const std::string& importer = {} ) -> std::uint64_t
        {
            require( depth < 32, "export forwarder cycle" );
            std::set< std::pair< std::string, std::string > > local;
            auto& visited = seen ? *seen : local;
            auto base = load( name, importer );
            auto host = module_name( base );
            auto key = std::make_pair( host, lower( symbol ) );
            require( visited.insert( key ).second, "export forwarder cycle" );
            auto& d = dlls.at( host );
            auto ordinal = find_export_ordinal( d, symbol );
            auto it = d.ordinals.find( ordinal ); require( it != d.ordinals.end( ), "missing export ordinal" ); auto rva = it->second;
            if ( rva >= d.exports.VirtualAddress && rva - d.exports.VirtualAddress < d.exports.Size )
            {
                auto forward = string_at( d.image, rva );
                auto dot = forward.rfind( '.' );
                require( dot != std::string::npos && dot + 1 < forward.size( ), "invalid export forwarder" );
                auto target_mod = forward.substr( 0, dot );
                auto target_sym = forward.substr( dot + 1 );
                if ( !target_sym.empty( ) && target_sym[ 0 ] == '#' )
                    target_sym = "#" + std::to_string( std::stoul( target_sym.substr( 1 ) ) );
                return resolve( target_mod, target_sym, depth + 1, &visited, host );
            }
            return base + rva;
        }
        auto lists( ) -> void
        {
            std::vector< std::pair< std::string, std::pair< std::uint64_t, std::uint32_t > > > mods;
            mods.push_back( { "image.exe", { p.base, p.size } } );
            for ( auto name : { "ntdll.dll", "kernel32.dll", "kernelbase.dll" } )
                mods.push_back( { name, { dlls.at( name ).base, static_cast< std::uint32_t >( dlls.at( name ).image.size( ) ) } } );
            for ( const auto& kv : dlls ) if ( kv.first != "ntdll.dll" && kv.first != "kernel32.dll" && kv.first != "kernelbase.dll" )
                mods.push_back( { kv.first, { kv.second.base, static_cast< std::uint32_t >( kv.second.image.size( ) ) } } );
            for ( unsigned i = 0; i < mods.size( ); ++i )
            {
                auto node = ldr + 0x100 + i * 0x200; w64( node + 0x30, mods[ i ].second.first ); w32( node + 0x40, mods[ i ].second.second );
                auto& name = mods[ i ].first;
                for ( auto off : { 0x48, 0x58 } )
                {
                    write< std::uint16_t >( node + off, static_cast< std::uint16_t >( name.size( ) * 2 ) );
                    write< std::uint16_t >( node + off + 2, static_cast< std::uint16_t >( name.size( ) * 2 + 2 ) ); w64( node + off + 8, node + 0x100 );
                }
                for ( unsigned j = 0; j <= name.size( ); ++j ) write< std::uint16_t >( node + 0x100 + j * 2, j == name.size( ) ? 0 : name[ j ] );
            }
            for ( unsigned offset = 0; offset <= 0x20; offset += 0x10 )
            {
                std::vector< std::uint64_t > nodes{ ldr + 0x10 + offset };
                for ( unsigned i = 0; i < mods.size( ); ++i ) nodes.push_back( ldr + 0x100 + i * 0x200 + offset );
                for ( unsigned i = 0; i < nodes.size( ); ++i ) { w64( nodes[ i ], nodes[ ( i + 1 ) % nodes.size( ) ] ); w64( nodes[ i ] + 8, nodes[ ( i + nodes.size( ) - 1 ) % nodes.size( ) ] ); }
            }
        }
        auto result( std::uint64_t value ) -> void
        {
            reg( UC_X86_REG_RAX, value ); if ( in_syscall ) return;
            auto sp = reg( UC_X86_REG_RSP ); reg( UC_X86_REG_RIP, read< std::uint64_t >( sp ) ); reg( UC_X86_REG_RSP, sp + 8 );
        }
        auto argument( unsigned index ) -> std::uint64_t
        {
            const int registers[] = { UC_X86_REG_RCX, UC_X86_REG_RDX, UC_X86_REG_R8, UC_X86_REG_R9 };
            return index < 4 ? reg( registers[ index ] ) : read< std::uint64_t >( reg( UC_X86_REG_RSP ) + 8 + index * 8 );
        }
        auto dispatch( const std::string& n ) -> void;
        auto block( std::uint64_t address, std::uint32_t size ) -> void;
        static auto on_block( uc_engine*, std::uint64_t address, std::uint32_t size, void* user ) -> void
        {
            auto& self = *static_cast< loader* >( user );
            try { self.block( address, size ); } catch ( const std::exception& ex ) { self.failure = ex.what( ); uc_emu_stop( self.vm.uc ); }
        }
        static auto on_clock( uc_engine*, std::uint64_t address, std::uint32_t size, void* user ) -> void
        {
            auto& s = *static_cast< loader* >( user );
            try
            {
                const auto opcode = s.read< std::uint16_t >( address );
                if ( !( size == 2 && opcode == 0x310f ) &&
                    !( size == 3 && opcode == 0x010f && s.read< std::uint8_t >( address + 2 ) == 0xf9 ) ) return;
                s.ticks += 1000; s.reg( UC_X86_REG_RAX, s.ticks & 0xffffffff ); s.reg( UC_X86_REG_RDX, s.ticks >> 32 );
                if ( size == 3 ) s.reg( UC_X86_REG_RCX, 0 ); s.reg( UC_X86_REG_RIP, address + size );
            }
            catch ( const std::exception& ex ) { s.failure = ex.what( ); uc_emu_stop( s.vm.uc ); }
        }
        static auto on_syscall( uc_engine*, void* user ) -> void
        {
            auto& s = *static_cast< loader* >( user );
            try
            {
                auto num = static_cast< std::uint32_t >( s.reg( UC_X86_REG_RAX ) ); auto it = s.syscalls.find( num );
                auto next = s.reg( UC_X86_REG_RIP ) + 2, flags = s.reg( UC_X86_REG_EFLAGS );
                s.in_syscall = true; s.reg( UC_X86_REG_RCX, s.reg( UC_X86_REG_R10 ) );
                if ( it != s.syscalls.end( ) )
                    s.dispatch( s.apis.at( it->second ).second );
                else
                {
                    std::printf( "offline: unknown syscall 0x%x stubbed\n", num );
                    std::fflush( stdout );
                    s.result( 0 );
                }
                s.in_syscall = false; s.reg( UC_X86_REG_RCX, next ); s.reg( UC_X86_REG_R11, flags );
            }
            catch ( const std::exception& ex ) { s.failure = ex.what( ); uc_emu_stop( s.vm.uc ); }
        }
        static auto on_unmapped( uc_engine*, uc_mem_type, std::uint64_t address, int, std::int64_t, void* user ) -> bool
        {
            auto& s = *static_cast< loader* >( user );
            s.failure = "unmapped guest access at " + std::to_string( address );
            uc_emu_stop( s.vm.uc );
            return false;
        }
        static auto on_cpuid( uc_engine*, void* user ) -> int
        {
            auto& s = *static_cast< loader* >( user );
            try
            {
                auto leaf = s.reg( UC_X86_REG_EAX ), sub = s.reg( UC_X86_REG_ECX );
                int values[ 4 ]{};
                __cpuidex( values, static_cast< int >( leaf ), static_cast< int >( sub ) );
                const int regs[ 4 ] = { UC_X86_REG_EAX, UC_X86_REG_EBX, UC_X86_REG_ECX, UC_X86_REG_EDX };
                for ( unsigned i = 0; i < 4; ++i )
                {
                    auto v = static_cast< std::uint64_t >( static_cast< std::uint32_t >( values[ i ] ) );
                    if ( leaf == 1 && regs[ i ] == UC_X86_REG_ECX ) v &= ~( 1ull << 31 );
                    if ( leaf >= 0x40000000 && leaf < 0x50000000 ) v = 0;
                    s.reg( regs[ i ], v );
                }
            }
            catch ( const std::exception& ex ) { s.failure = ex.what( ); uc_emu_stop( s.vm.uc ); }
            return 1;
        }
    public:
        loader( const bytes& packed, const bytes& decompressed );
        auto run( std::uint32_t timeout_ms ) -> runtime_image;
    };

    auto loader::dispatch( const std::string& n ) -> void
    {
        constexpr std::uint64_t success = 0;
        constexpr std::uint64_t info_length_mismatch = 0xc0000004u;
        constexpr std::uint64_t invalid_handle = 0xc0000008u;
        constexpr std::uint64_t access_violation = 0xc0000005u;
        constexpr std::uint64_t object_name_not_found = 0xc0000034u;
        constexpr std::uint64_t port_not_set = 0xc0000353u;
        const auto a0 = argument( 0 ), a1 = argument( 1 ), a2 = argument( 2 ), a3 = argument( 3 );
        std::printf( "offline: %s a0=0x%llx a1=0x%llx a2=0x%llx a3=0x%llx\n", n.c_str( ),
            static_cast< unsigned long long >( a0 ), static_cast< unsigned long long >( a1 ),
            static_cast< unsigned long long >( a2 ), static_cast< unsigned long long >( a3 ) );
        std::fflush( stdout );

        if ( n == "GetProcAddress" || n == "GetProcAddressForCaller" ||
            n == "LdrGetProcedureAddress" || n == "LdrGetProcedureAddressForCaller" )
        {
            const auto module = module_name( a0 );
            const bool ldr = n.rfind( "LdrGetProcedureAddress", 0 ) == 0;
            std::string symbol;
            if ( !ldr )
                symbol = a1 <= 0xffff ? "#" + std::to_string( a1 ) : text( a1 );
            else
                symbol = a1 ? text( read< std::uint64_t >( a1 + 8 ) ) : "#" + std::to_string( a2 );
            auto address = resolve( module, symbol );
            if ( ldr )
            {
                const auto out = n == "LdrGetProcedureAddressForCaller" ? argument( 4 ) : a3;
                require( accessible( out, 8 ), "invalid LdrGetProcedureAddress result pointer" );
                w64( out, address ); address = success;
            }
            result( address ); return;
        }
        if ( n == "LoadLibraryA" || n == "LoadLibraryW" || n == "LoadLibraryExA" || n == "LoadLibraryExW" || n == "LdrLoadDll" )
        {
            const bool native = n == "LdrLoadDll";
            const bool wide = native || n == "LoadLibraryW" || n == "LoadLibraryExW";
            auto ptr = native ? read< std::uint64_t >( a2 + 8 ) : a0;
            auto address = load( text( ptr, wide ), "image.exe" ); lists( );
            if ( native )
            {
                require( accessible( a3, 8 ), "invalid LdrLoadDll result pointer" );
                w64( a3, address ); address = success;
            }
            result( address ); return;
        }
        if ( n == "GetModuleHandleA" || n == "GetModuleHandleW" )
        {
            if ( !a0 ) { result( p.base ); return; }
            auto name = resolve_module_name( text( a0, n == "GetModuleHandleW" ) );
            auto found = dlls.find( name );
            std::printf( "offline: module lookup %s -> 0x%llx\n", name.c_str( ),
                static_cast< unsigned long long >( found == dlls.end( ) ? 0 : found->second.base ) );
            result( found == dlls.end( ) ? 0 : found->second.base ); return;
        }
        if ( n == "RtlAllocateHeap" || n == "HeapAlloc" )
        {
            result( allocate( ( std::max )( std::uint64_t( 1 ), a2 ) ) ); return;
        }
        if ( n == "RtlFreeHeap" || n == "HeapFree" )
        {
            result( 1 ); return;
        }
        if ( n == "GetProcessHeap" || n == "RtlGetProcessHeap" )
        {
            result( heap ); return;
        }
        if ( n == "VirtualAlloc" || n == "VirtualAllocEx" )
        {
            const auto size = n == "VirtualAlloc" ? a1 : a2;
            result( allocate( ( std::max )( std::uint64_t( 1 ), size ) ) ); return;
        }
        if ( n == "VirtualFree" || n == "VirtualFreeEx" || n == "VirtualProtect" || n == "VirtualProtectEx" )
        {
            if ( n.find( "Protect" ) != std::string::npos )
            {
                const auto old = n == "VirtualProtect" ? a3 : argument( 4 );
                if ( old && accessible( old, 4 ) ) w32( old, PAGE_EXECUTE_READWRITE );
            }
            result( 1 ); return;
        }
        if ( n == "NtAllocateVirtualMemory" )
        {
            if ( !accessible( a1, 8 ) || !accessible( a3, 8 ) ) { result( access_violation ); return; }
            auto size = read< std::uint64_t >( a3 );
            auto address = read< std::uint64_t >( a1 );
            if ( !address ) address = allocate( ( std::max )( std::uint64_t( 1 ), size ) );
            w64( a1, address ); w64( a3, ( size + 0xfff ) & ~0xfffull ); result( success ); return;
        }
        if ( n == "NtFreeVirtualMemory" || n == "NtProtectVirtualMemory" || n == "NtFlushInstructionCache" )
        {
            if ( n == "NtProtectVirtualMemory" )
            {
                if ( !accessible( a1, 8 ) || !accessible( a2, 8 ) ) { result( access_violation ); return; }
                auto address = read< std::uint64_t >( a1 );
                auto length = read< std::uint64_t >( a2 );
                auto page = address & ~0xfffull;
                auto rounded = ( ( address + ( std::max )( length, std::uint64_t( 1 ) ) + 0xfff ) & ~0xfffull ) - page;
                w64( a1, page ); w64( a2, rounded );
                auto old = argument( 4 ); if ( old && accessible( old, 4 ) ) w32( old, PAGE_EXECUTE_READ );
            }
            result( success ); return;
        }
        if ( n == "NtOpenSection" )
        {
            require( accessible( a0, 8 ) && accessible( a2 + 16, 8 ), "invalid NtOpenSection arguments" );
            auto object = read< std::uint64_t >( a2 + 16 );
            require( object && accessible( object + 8, 8 ), "invalid NtOpenSection object name" );
            auto name = text( read< std::uint64_t >( object + 8 ), true );
            auto slash = name.find_last_of( "\\/" ); if ( slash != std::string::npos ) name.erase( 0, slash + 1 );
            auto handle = 0x100ull + handles.size( ); handles[ handle ] = load( name ); w64( a0, handle );
            std::printf( "offline: NtOpenSection %s -> 0x%llx\n", name.c_str( ), static_cast< unsigned long long >( handle ) );
            result( success ); return;
        }
        if ( n == "NtMapViewOfSection" )
        {
            auto it = handles.find( a0 );
            if ( it == handles.end( ) || !it->second ) { result( invalid_handle ); return; }
            if ( !accessible( a2, 8 ) ) { result( access_violation ); return; }
            w64( a2, it->second );
            const auto view_size = argument( 6 );
            if ( view_size && accessible( view_size, 8 ) )
            {
                auto mapped_size = dlls.at( module_name( it->second ) ).image.size( );
                auto requested = read< std::uint64_t >( view_size );
                w64( view_size, requested ? requested : mapped_size );
            }
            result( success ); return;
        }
        if ( n == "NtUnmapViewOfSection" || n == "NtClose" || n == "NtDelayExecution" || n == "NtYieldExecution" )
        {
            result( success ); return;
        }
        if ( n == "NtQueryInformationProcess" || n == "NtQueryInformationThread" || n == "NtQueryInformationToken" ||
            n == "NtQueryInformationJobObject" || n == "NtQueryInformationFile" || n == "NtQueryObject" ||
            n == "NtQueryVirtualMemory" || n == "NtQuerySection" || n == "NtQueryInformationEnlistment" )
        {
            query_information( n, host_handle( a0 ), static_cast< ULONG >( a1 ), a2, static_cast< ULONG >( a3 ), argument( 4 ) );
            return;
        }
        if ( n == "NtSetInformationProcess" || n == "NtSetInformationThread" || n == "NtSetInformationToken" ||
            n == "NtSetInformationJobObject" || n == "NtSetInformationFile" || n == "NtSetInformationObject" )
        {
            set_information( n, host_handle( a0 ), static_cast< ULONG >( a1 ), a2, static_cast< ULONG >( a3 ) );
            return;
        }
        if ( n == "NtOpenFile" )
        {
            try
            {
                if ( accessible( a2 + 16, 8 ) )
                {
                    auto object = read< std::uint64_t >( a2 + 16 );
                    if ( object && accessible( object + 8, 8 ) )
                    {
                        auto name = text( read< std::uint64_t >( object + 8 ), true );
                        std::printf( "offline: NtOpenFile %s\n", name.c_str( ) );
                        std::fflush( stdout );
                    }
                }
            }
            catch ( ... ) {}
            result( object_name_not_found ); return;
        }
        if ( n == "NtCreateDebugObject" )
        {
            if ( !accessible( a0, 8 ) ) { result( access_violation ); return; }
            auto handle = 0x100ull + handles.size( ); handles[ handle ] = 0; w64( a0, handle ); result( success ); return;
        }
        if ( n == "NtQuerySystemInformation" || n == "NtQuerySystemInformationEx" || n == "RtlGetNativeSystemInformation" )
        {
            const auto cls = a0;
            const auto buf = a1;
            const auto len = a2;
            const auto retlen = a3;
            auto need = 0u;
            if ( cls == 0 || cls == 0x3e || cls == 0x72 ) need = 0x40;
            else if ( cls == 2 ) need = 0x138;
            else if ( cls == 3 ) need = 0x30;
            else if ( cls == 0x0b ) need = 0x128;
            else if ( cls == 0x23 ) need = 2;
            else if ( cls == 0x32 ) need = 8;
            else if ( cls == 0x5a ) need = 8;
            else
            {
                if ( retlen && accessible( retlen, 4 ) ) w32( retlen, 0 );
                result( 0xc0000003u );
                return;
            }
            if ( retlen && !accessible( retlen, 4 ) ) { result( access_violation ); return; }
            if ( len < need )
            {
                if ( retlen ) w32( retlen, need );
                result( info_length_mismatch );
                return;
            }
            if ( !accessible( buf, need ) ) { result( access_violation ); return; }
            zero( buf, need );
            if ( cls == 0 || cls == 0x3e || cls == 0x72 )
            {
                w32( buf + 0x04, 156250 );
                w32( buf + 0x08, 0x1000 );
                w32( buf + 0x0c, 0x200000 );
                w32( buf + 0x10, 1 );
                w32( buf + 0x14, 0x1fffff );
                w32( buf + 0x18, 0x10000 );
                w64( buf + 0x20, 0x10000 );
                w64( buf + 0x28, 0x00007ffffffeffffull );
                w64( buf + 0x30, 1 );
                write< std::uint8_t >( buf + 0x38, 1 );
            }
            else if ( cls == 2 )
            {
                w64( buf, ticks );
            }
            else if ( cls == 3 )
            {
                w64( buf, ticks );
                w64( buf + 8, 0x01d0000000000000ull );
            }
            else if ( cls == 0x0b )
            {
                w32( buf, 1 );
                w64( buf + 0x08, 0xfffff80000000000ull );
                w64( buf + 0x10, 0xfffff80000000000ull );
                w32( buf + 0x18, 0x800000 );
                w32( buf + 0x1c, 0 );
                write< std::uint16_t >( buf + 0x20, 0 );
                write< std::uint16_t >( buf + 0x22, 0 );
                write< std::uint16_t >( buf + 0x24, 0 );
                write< std::uint16_t >( buf + 0x26, 0x18 );
                const char path[] = "\\SystemRoot\\system32\\ntoskrnl.exe";
                for ( unsigned i = 0; i < sizeof( path ); ++i )
                    write< std::uint8_t >( buf + 0x28 + i, static_cast< std::uint8_t >( path[ i ] ) );
            }
            else if ( cls == 0x23 )
            {
                write< std::uint8_t >( buf, 0 );
                write< std::uint8_t >( buf + 1, 1 );
            }
            else if ( cls == 0x32 || cls == 0x5a )
            {
                w64( buf, 0xffff800000000000ull );
            }
            if ( retlen ) w32( retlen, need );
            result( success );
            return;
        }
        if ( n == "GetSystemInfo" || n == "GetNativeSystemInfo" )
        {
            if ( !accessible( a0, 48 ) ) { result( 0 ); return; }
            zero( a0, 48 );
            write< std::uint16_t >( a0, 9 );
            w32( a0 + 4, 0x1000 );
            w64( a0 + 8, 0x10000 );
            w64( a0 + 16, 0x00007ffffffeffffull );
            w64( a0 + 24, 1 );
            w32( a0 + 32, 1 );
            w32( a0 + 36, 2 );
            write< std::uint16_t >( a0 + 40, 6 );
            write< std::uint16_t >( a0 + 42, 0x8e0a );
            result( 0 );
            return;
        }
        if ( n == "QueryPerformanceCounter" || n == "QueryPerformanceFrequency" )
        {
            if ( !accessible( a0, 8 ) ) { result( 0 ); return; }
            w64( a0, n == "QueryPerformanceCounter" ? ( ticks += 1000 ) : 10000000 ); result( 1 ); return;
        }
        if ( n == "NtQueryPerformanceCounter" )
        {
            if ( !accessible( a0, 8 ) ) { result( access_violation ); return; }
            w64( a0, ticks += 1000 ); if ( a1 && accessible( a1, 8 ) ) w64( a1, 10000000 ); result( success ); return;
        }
        if ( n == "GetTickCount" || n == "timeGetTime" ) { result( ( ticks += 1000 ) / 10000 ); return; }
        if ( n == "GetTickCount64" ) { result( ( ticks += 1000 ) / 10000 ); return; }
        if ( n == "Sleep" || n == "SleepEx" ) { ticks += a0 * 10000; result( n == "SleepEx" ? 0 : success ); return; }
        if ( n == "IsDebuggerPresent" ) { result( 0 ); return; }
        if ( n == "CheckRemoteDebuggerPresent" )
        {
            if ( a1 && accessible( a1, 4 ) ) w32( a1, 0 ); result( 1 ); return;
        }
        if ( n == "GetCurrentProcess" ) { result( ~std::uint64_t( 0 ) ); return; }
        if ( n == "GetCurrentThread" ) { result( ~std::uint64_t( 1 ) ); return; }
        if ( n == "GetCurrentProcessId" ) { result( 0x1234 ); return; }
        if ( n == "GetCurrentThreadId" ) { result( 0x5678 ); return; }
        if ( n == "RtlGetCurrentPeb" ) { result( peb ); return; }
        if ( n == "NtRaiseHardError" )
        {
            const auto response = argument( 5 );
            if ( response && accessible( response, 4 ) ) w32( response, 0 );
            std::printf( "offline: NtRaiseHardError status=0x%llx params=%llu mask=0x%llx\n",
                static_cast< unsigned long long >( a0 ), static_cast< unsigned long long >( a1 ),
                static_cast< unsigned long long >( a2 ) );
            for ( unsigned i = 0; i < ( std::min )( a1, 8ull ); ++i )
            {
                if ( !a3 || !accessible( a3 + i * 8, 8 ) ) continue;
                const auto param = read< std::uint64_t >( a3 + i * 8 );
                std::printf( "offline: harderror param %u = 0x%llx\n", i, static_cast< unsigned long long >( param ) );
                if ( ( a2 & ( 1ull << i ) ) && param && accessible( param + 8, 8 ) )
                {
                    const auto str = read< std::uint64_t >( param + 8 );
                    try { std::printf( "offline: harderror unicode %u = %s\n", i, text( str, true ).c_str( ) ); }
                    catch ( ... ) {}
                }
            }
            std::fflush( stdout );
            result( 0xc0000001u ); return;
        }
        if ( n == "ExitProcess" || n == "RtlExitUserProcess" || n == "NtTerminateProcess" )
        {
            restored_dwords = 0;
            for ( const auto& item : original_code )
                if ( read< std::uint32_t >( p.base + item.first ) == item.second ) ++restored_dwords;
            std::printf( "offline: terminate at 0x%llx restored %zu/%zu\n",
                static_cast< unsigned long long >( reg( UC_X86_REG_RIP ) ), restored_dwords, original_code.size( ) );
            std::fflush( stdout );
            if ( restored_dwords * 4 >= original_code.size( ) )
            {
                oep = restored_entry; done = true; check( uc_emu_stop( vm.uc ) ); return;
            }
            throw std::runtime_error( "the protected loader requested process termination" );
        }

        if ( n == "CoInitialize" || n == "CoInitializeEx" )
        {
            result( 0 ); return;
        }
        if ( n == "CoUninitialize" )
        {
            result( 0 ); return;
        }
        if ( n == "CoTaskMemAlloc" )
        {
            result( allocate( ( std::max )( std::uint64_t( 1 ), a0 ) ) ); return;
        }
        if ( n == "CoTaskMemFree" )
        {
            result( 0 ); return;
        }
        if ( n == "CoCreateInstance" || n == "CoCreateInstanceEx" || n == "CoGetClassObject" )
        {
            const auto out = n == "CoCreateInstance" ? argument( 4 ) : ( n == "CoGetClassObject" ? argument( 4 ) : a3 );
            if ( out && accessible( out, 8 ) ) w64( out, 0 );
            result( 0x80004001ull ); return;
        }

        if ( n.rfind( "Nt", 0 ) == 0 || n.rfind( "Zw", 0 ) == 0 || n.rfind( "Rtl", 0 ) == 0 )
        {
            if ( n.find( "Query" ) != std::string::npos && n.find( "Information" ) != std::string::npos )
            {
                query_information( n, host_handle( a0 ), static_cast< ULONG >( a1 ), a2, static_cast< ULONG >( a3 ), argument( 4 ) );
                return;
            }
            if ( n.find( "Set" ) != std::string::npos && n.find( "Information" ) != std::string::npos )
            {
                set_information( n, host_handle( a0 ), static_cast< ULONG >( a1 ), a2, static_cast< ULONG >( a3 ) );
                return;
            }
            std::printf( "offline: stub %s -> STATUS_SUCCESS\n", n.c_str( ) );
            std::fflush( stdout );
            result( success );
            return;
        }
        std::printf( "offline: stub win32 %s -> TRUE\n", n.c_str( ) );
        std::fflush( stdout );
        result( 1 );
    }

    auto loader::block( std::uint64_t address, std::uint32_t size ) -> void
    {
        if ( address >= p.base && address - p.base < p.size )
        {
            const auto rva = static_cast< std::uint32_t >( address - p.base );
            auto it = std::lower_bound( original_code.begin( ), original_code.end( ), rva,
                [ ]( const auto& item, std::uint32_t value ) { return item.first < value; } );
            if ( it != original_code.end( ) && it->first == rva && read< std::uint32_t >( address ) == it->second )
            {
                oep = restored_entry ? restored_entry : rva; done = true; check( uc_emu_stop( vm.uc ) ); return;
            }
            if ( address >= original_begin && address < original_end )
            {
                restored_dwords = 0;
                for ( const auto& item : original_code )
                    if ( read< std::uint32_t >( p.base + item.first ) == item.second ) ++restored_dwords;
                if ( restored_dwords * 2 >= original_code.size( ) )
                {
                    std::printf( "offline: original section restored at 0x%llx (%zu/%zu)\n",
                        static_cast< unsigned long long >( address ), restored_dwords, original_code.size( ) );
                    std::fflush( stdout );
                    oep = restored_entry ? restored_entry : rva; done = true; check( uc_emu_stop( vm.uc ) ); return;
                }
            }
            auto site = std::find_if( checksum_sites.begin( ), checksum_sites.end( ),
                [ address ]( const checksum_site& item ) { return item.address == address; } );
            if ( site != checksum_sites.end( ) && site->pointer_reg != UC_X86_REG_INVALID &&
                site->count_reg != UC_X86_REG_INVALID )
            {
                auto ptr = reg( site->pointer_reg );
                auto count = reg( site->count_reg );
                auto table = site->table_reg != UC_X86_REG_INVALID ? reg( site->table_reg ) : site->table;
                if ( count > 1 && count <= heap_size && accessible( ptr, count - 1 ) && accessible( table, 16 ) )
                {
                    std::uint32_t words[ 4 ]{};
                    check( uc_mem_read( vm.uc, table, words, sizeof( words ) ) );
                    auto key = words[ 0 ];
                    if ( ( words[ 1 ] ^ key ) == 0x77073096u && ( words[ 2 ] ^ key ) == 0xee0e612cu && ( words[ 3 ] ^ key ) == 0x990951bau )
                    {
                        bytes buf( static_cast< std::size_t >( count - 1 ) );
                        check( uc_mem_read( vm.uc, ptr, buf.data( ), buf.size( ) ) );
                        auto crc = crc32_ieee( static_cast< std::uint32_t >( reg( UC_X86_REG_ESI ) ), buf.data( ), buf.size( ) );
                        reg( UC_X86_REG_ESI, crc );
                        reg( site->pointer_reg, ptr + count - 1 );
                        reg( site->count_reg, 1 );
                        ++checksum_skips;
                        if ( checksum_skips <= 8 )
                        {
                            std::printf( "offline: checksum skip %u site=0x%llx count=%llu ptr=0x%llx table=0x%llx\n",
                                checksum_skips, static_cast< unsigned long long >( address ),
                                static_cast< unsigned long long >( count ), static_cast< unsigned long long >( ptr ),
                                static_cast< unsigned long long >( table ) );
                            std::fflush( stdout );
                        }
                    }
                    else if ( checksum_skips < 8 )
                    {
                        std::printf( "offline: checksum miss 0x%llx count=%llu ptr=0x%llx table=0x%llx key=0x%x\n",
                            static_cast< unsigned long long >( address ), static_cast< unsigned long long >( count ),
                            static_cast< unsigned long long >( ptr ), static_cast< unsigned long long >( table ), key );
                        std::fflush( stdout );
                    }
                }
                else if ( checksum_skips < 8 )
                {
                    std::printf( "offline: checksum idle 0x%llx count=%llu ptr=0x%llx table=0x%llx\n",
                        static_cast< unsigned long long >( address ), static_cast< unsigned long long >( count ),
                        static_cast< unsigned long long >( ptr ), static_cast< unsigned long long >( table ) );
                    std::fflush( stdout );
                }
            }
        }

        auto api = apis.find( address );
        if ( api != apis.end( ) ) { dispatch( api->second.second ); return; }
        ( void )size;
    }

    loader::loader( const bytes& packed, const bytes& decompressed ) : p( parse( packed ) ), image( mapped( packed, p ) )
    {
        auto restored_header = parse( decompressed );
        require( restored_header.base == p.base && restored_header.size == p.size, "decompressed image does not match packed image" );
        auto restored = mapped( decompressed, restored_header );

        IMAGE_SECTION_HEADER entry_section{}; bool found_entry = false;
        for ( unsigned i = 0; i < restored_header.count; ++i )
        {
            auto section = get< IMAGE_SECTION_HEADER >( decompressed, restored_header.section + i * 40 );
            auto span = ( std::max )( section.Misc.VirtualSize, section.SizeOfRawData );
            if ( restored_header.entry >= section.VirtualAddress && restored_header.entry - section.VirtualAddress < span )
            {
                entry_section = section; found_entry = true; break;
            }
        }
        require( found_entry && ( entry_section.Characteristics & IMAGE_SCN_MEM_EXECUTE ), "decompressed entry point is not executable" );
        auto begin = entry_section.VirtualAddress;
        auto end = ( std::min )( std::uint64_t( p.size ), std::uint64_t( begin ) + ( std::max )( entry_section.Misc.VirtualSize, entry_section.SizeOfRawData ) );
        original_begin = p.base + begin;
        original_end = p.base + end;
        restored_entry = restored_header.entry;
        for ( auto rva = begin; rva + 4 <= end; ++rva )
        {
            auto expected = get< std::uint32_t >( restored, rva );
            if ( expected && expected != get< std::uint32_t >( image, rva ) ) original_code.emplace_back( rva, expected );
        }
        require( !original_code.empty( ), "no restored entry-point code was found" );

        check( uc_open( UC_ARCH_X86, UC_MODE_64, &vm.uc ) );
        check( uc_mem_map_ptr( vm.uc, p.base, image.size( ), UC_PROT_ALL, image.data( ) ) );
        check( uc_mem_map( vm.uc, stack, 0x200000, UC_PROT_ALL ) ); check( uc_mem_map( vm.uc, heap, heap_size, UC_PROT_ALL ) );
        check( uc_mem_map( vm.uc, teb, 0x100000, UC_PROT_ALL ) ); check( uc_mem_map( vm.uc, 0x7ffe0000, 0x10000, UC_PROT_ALL ) );

        {
            const auto* host = reinterpret_cast< const std::uint8_t* >( 0x7ffe0000ull );
            check( uc_mem_write( vm.uc, 0x7ffe0000, host, 0x1000 ) );
            write< std::uint8_t >( 0x7ffe02d4, 0 );
            auto major = read< std::uint32_t >( 0x7ffe026c );
            auto minor = read< std::uint32_t >( 0x7ffe0270 );
            auto build = read< std::uint32_t >( 0x7ffe0260 );
            w32( peb + 0x118, major ); w32( peb + 0x11c, minor ); w32( peb + 0x120, build );
        }
        w64( teb + 0x30, teb ); w64( teb + 0x60, peb ); w64( teb + 8, stack + 0x200000 ); w64( teb + 16, stack );
        w64( peb + 0x10, p.base ); w64( peb + 0x18, ldr ); w64( peb + 0x20, teb + 0x80000 ); w64( peb + 0x30, heap );
        write< std::uint8_t >( peb + 2, 0 ); write< std::uint8_t >( peb + 3, 0 );
        w32( peb + 0x68, 0 ); w32( peb + 0xbc, 0 );
        w32( heap + 0x70, 2 ); w32( heap + 0x74, 0 );
        reg( UC_X86_REG_GS_BASE, teb ); reg( UC_X86_REG_RSP, stack + 0x1ff008 ); reg( UC_X86_REG_EFLAGS, 0x202 );

        load( "ntdll.dll" ); load( "kernel32.dll" ); load( "kernelbase.dll" );
        auto imports = p.dirs[ IMAGE_DIRECTORY_ENTRY_IMPORT ];
        if ( imports.Size )
        {
            require( fits( image.size( ), imports.VirtualAddress, imports.Size ), "invalid packed import directory" );
            auto limit = std::uint64_t( imports.VirtualAddress ) + imports.Size;
            for ( auto at = std::uint64_t( imports.VirtualAddress ); at + sizeof( IMAGE_IMPORT_DESCRIPTOR ) <= limit; at += sizeof( IMAGE_IMPORT_DESCRIPTOR ) )
            {
                auto desc = get< IMAGE_IMPORT_DESCRIPTOR >( image, at );
                if ( !desc.Name && !desc.FirstThunk && !desc.OriginalFirstThunk ) break;
                auto module = lower( string_at( image, desc.Name ) ); load( module );
                auto source = desc.OriginalFirstThunk ? desc.OriginalFirstThunk : desc.FirstThunk;
                require( source && desc.FirstThunk, "invalid packed import thunk" );
                for ( std::uint64_t index = 0; index < 100000; ++index )
                {
                    auto thunk_rva = std::uint64_t( source ) + index * 8, iat_rva = std::uint64_t( desc.FirstThunk ) + index * 8;
                    auto thunk = get< std::uint64_t >( image, thunk_rva ); if ( !thunk ) break;
                    std::string symbol;
                    if ( IMAGE_SNAP_BY_ORDINAL64( thunk ) ) symbol = "#" + std::to_string( IMAGE_ORDINAL64( thunk ) );
                    else symbol = string_at( image, thunk + 2 );
                    w64( p.base + iat_rva, resolve( module, symbol, 0, nullptr, "image.exe" ) );
                }
            }
        }
        lists( );
        ZydisDecoder decoder{};
        require( ZYAN_SUCCESS( ZydisDecoderInit( &decoder, ZYDIS_MACHINE_MODE_LONG_64, ZYDIS_STACK_WIDTH_64 ) ), "cannot initialize Zydis" );
        for ( std::size_t i = 0; i + 32 <= image.size( ); ++i )
        {
            if ( !masked_crc32_table( image, i ) ) continue;
            auto key = get< std::uint32_t >( image, i );
            auto hi = ( std::min )( image.size( ), i + 0x1000 );
            checksum_site best{};
            auto best_dist = 0ull;
            for ( auto at = i + 32; at + 6 <= hi; ++at )
            {
                auto xor_at = std::size_t( -1 );
                if ( image[ at ] == 0x81 && image[ at + 1 ] == 0xf6 && get< std::uint32_t >( image, at + 2 ) == key )
                    xor_at = at;
                else if ( at + 7 <= hi && image[ at ] == 0x48 && image[ at + 1 ] == 0x81 && image[ at + 2 ] == 0xf6 &&
                    get< std::uint32_t >( image, at + 3 ) == key )
                    xor_at = at;
                if ( xor_at == std::size_t( -1 ) ) continue;
                auto scan = ( std::min )( image.size( ), xor_at + 96 );
                for ( auto j = xor_at; j + 6 <= scan; ++j )
                {
                    std::int64_t target = -1;
                    if ( image[ j ] == 0x75 )
                        target = static_cast< std::int64_t >( j ) + 2 + static_cast< std::int8_t >( image[ j + 1 ] );
                    else if ( image[ j ] == 0x0f && image[ j + 1 ] == 0x85 )
                        target = static_cast< std::int64_t >( j ) + 6 + static_cast< std::int32_t >( get< std::uint32_t >( image, j + 2 ) );
                    if ( target < static_cast< std::int64_t >( i ) || target >= static_cast< std::int64_t >( xor_at ) ) continue;
                    auto dist = static_cast< std::uint64_t >( static_cast< std::int64_t >( j ) - target );
                    if ( dist <= best_dist ) continue;
                    checksum_site site{};
                    site.address = p.base + static_cast< std::uint64_t >( target );
                    site.table = p.base + i;
                    auto stop = static_cast< std::size_t >( j );
                    auto offset = static_cast< std::size_t >( target );
                    while ( offset < stop )
                    {
                        ZydisDecodedInstruction insn{};
                        ZydisDecodedOperand ops[ ZYDIS_MAX_OPERAND_COUNT ]{};
                        if ( !ZYAN_SUCCESS( ZydisDecoderDecodeFull( &decoder, image.data( ) + offset, stop - offset, &insn, ops ) ) )
                            break;
                        if ( insn.mnemonic == ZYDIS_MNEMONIC_DEC && ops[ 0 ].type == ZYDIS_OPERAND_TYPE_REGISTER )
                            site.count_reg = zydis_reg( ops[ 0 ].reg.value );
                        if ( insn.mnemonic == ZYDIS_MNEMONIC_MOVZX && ops[ 1 ].type == ZYDIS_OPERAND_TYPE_MEMORY )
                            site.pointer_reg = zydis_reg( ops[ 1 ].mem.base );
                        if ( insn.mnemonic == ZYDIS_MNEMONIC_MOV && ops[ 1 ].type == ZYDIS_OPERAND_TYPE_MEMORY &&
                            ops[ 1 ].mem.index != ZYDIS_REGISTER_NONE && ops[ 1 ].mem.scale == 4 )
                            site.table_reg = zydis_reg( ops[ 1 ].mem.base );
                        offset += insn.length;
                    }
                    if ( site.pointer_reg == UC_X86_REG_INVALID || site.count_reg == UC_X86_REG_INVALID ) continue;
                    best = site;
                    best_dist = dist;
                }
            }
            if ( best.address ) checksum_sites.push_back( best );
            i += 31;
        }
        std::sort( checksum_sites.begin( ), checksum_sites.end( ),
            [ ]( const checksum_site& a, const checksum_site& b ) { return a.address < b.address; } );
        checksum_sites.erase( std::unique( checksum_sites.begin( ), checksum_sites.end( ),
            [ ]( const checksum_site& a, const checksum_site& b ) { return a.address == b.address; } ), checksum_sites.end( ) );
        std::printf( "offline: checksum sites %zu\n", checksum_sites.size( ) );
        for ( const auto& site : checksum_sites )
            std::printf( "offline: checksum site 0x%llx table=0x%llx ptr_reg=%d count_reg=%d table_reg=%d\n",
                static_cast< unsigned long long >( site.address ), static_cast< unsigned long long >( site.table ),
                site.pointer_reg, site.count_reg, site.table_reg );
        std::fflush( stdout );
        uc_hook hook{};
        check( uc_hook_add( vm.uc, &hook, UC_HOOK_BLOCK, reinterpret_cast< void* >( on_block ), this, original_begin, original_end - 1 ) );
        for ( const auto& site : checksum_sites )
            check( uc_hook_add( vm.uc, &hook, UC_HOOK_CODE, reinterpret_cast< void* >( on_block ), this, site.address, site.address ) );
        for ( std::size_t i = 0; i + 1 < image.size( ); ++i )
        {
            auto width = std::size_t{};
            if ( image[ i ] == 0x0f && image[ i + 1 ] == 0x31 ) width = 2;
            else if ( i + 2 < image.size( ) && image[ i ] == 0x0f && image[ i + 1 ] == 0x01 && image[ i + 2 ] == 0xf9 ) width = 3;
            if ( !width ) continue;
            uc_hook time_hook{};
            check( uc_hook_add( vm.uc, &time_hook, UC_HOOK_CODE, reinterpret_cast< void* >( on_clock ), this,
                p.base + i, p.base + i ) );
        }
        check( uc_hook_add( vm.uc, &hook, UC_HOOK_INSN, reinterpret_cast< void* >( on_syscall ), this, 1, 0, UC_X86_INS_SYSCALL ) );
        check( uc_hook_add( vm.uc, &hook, UC_HOOK_INSN, reinterpret_cast< void* >( on_cpuid ), this, 1, 0, UC_X86_INS_CPUID ) );
        check( uc_hook_add( vm.uc, &hook, UC_HOOK_MEM_UNMAPPED, reinterpret_cast< void* >( on_unmapped ), this, 1, 0 ) );
    }

    auto loader::run( std::uint32_t timeout_ms ) -> runtime_image
    {
        require( timeout_ms, "offline loader timeout must be nonzero" );
        auto error = uc_emu_start( vm.uc, p.base + p.entry, 0, std::uint64_t( timeout_ms ) * 1000, 0 );
        if ( !failure.empty( ) ) throw std::runtime_error( failure );
        if ( error != UC_ERR_OK ) check( error );
        if ( !done )
        {
            char message[ 192 ];
            std::size_t matched = 0;
            for ( const auto& item : original_code )
                if ( read< std::uint32_t >( p.base + item.first ) == item.second ) ++matched;
            std::snprintf( message, sizeof( message ), "offline loader timed out at 0x%llx (%zu/%zu restored dwords matched)",
                static_cast< unsigned long long >( reg( UC_X86_REG_RIP ) ), matched, original_code.size( ) );
            throw std::runtime_error( message );
        }
        check( uc_mem_read( vm.uc, p.base, image.data( ), p.size ) );

        runtime_image out{}; out.bytes.assign( image.begin( ), image.begin( ) + p.size ); out.base = p.base; out.is64 = true; out.exports = exports;
        out.modules.push_back( { "image.exe", "", p.base, p.size } );
        for ( const auto& item : dlls ) out.modules.push_back( { item.first, "", item.second.base, static_cast< std::uint32_t >( item.second.image.size( ) ) } );
        put< std::uint32_t >( out.bytes, p.opt + 16, oep );
        std::printf( "offline: restored code at 0x%x, checksum skips %u\n", oep, checksum_skips );
        return out;
    }
}

auto initialize_static_imports( const std::vector< std::uint8_t >& packed,
    const std::vector< std::uint8_t >& decompressed, std::uint32_t timeout_ms ) -> runtime_image
{
    require( !packed.empty( ) && !decompressed.empty( ), "packed and decompressed images are required" );
    loader offline( packed, decompressed ); return offline.run( timeout_ms );
}
