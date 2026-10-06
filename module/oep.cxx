#include "oep.hxx"
#include "vmp.hxx"

#define WIN32_LEAN_AND_MEAN
#define NOMINMAX
#include <windows.h>
#include <winnt.h>

#include <cstring>
#include <vector>

namespace
{
    auto read_u16( const std::uint8_t* p ) -> std::uint16_t
    {
        std::uint16_t v;
        std::memcpy( &v, p, sizeof( v ) );
        return v;
    }

    auto read_u32( const std::uint8_t* p ) -> std::uint32_t
    {
        std::uint32_t v;
        std::memcpy( &v, p, sizeof( v ) );
        return v;
    }

    auto read_u64( const std::uint8_t* p ) -> std::uint64_t
    {
        std::uint64_t v;
        std::memcpy( &v, p, sizeof( v ) );
        return v;
    }

    auto write_u32( std::uint8_t* p, std::uint32_t v ) -> void
    {
        std::memcpy( p, &v, sizeof( v ) );
    }

    auto opt_off( const std::vector< std::uint8_t >& image ) -> std::uint32_t
    {
        if ( image.size( ) < 0x40 )
            return 0;
        const auto nt = read_u32( image.data( ) + 0x3c );
        if ( nt + 24 + 18 >= image.size( ) )
            return 0;
        return nt + 4 + static_cast< std::uint32_t >( sizeof( IMAGE_FILE_HEADER ) );
    }

    auto is_dll_image( const std::vector< std::uint8_t >& image ) -> bool
    {
        if ( image.size( ) < 0x40 )
            return false;
        const auto nt = read_u32( image.data( ) + 0x3c );
        if ( nt + 24 >= image.size( ) )
            return false;
        return ( read_u16( image.data( ) + nt + 4 + 18 ) & IMAGE_FILE_DLL ) != 0;
    }

    auto in_image( const std::vector< std::uint8_t >& image, std::uint32_t rva, std::uint32_t need ) -> bool
    {
        return rva < image.size( ) && image.size( ) - rva >= need;
    }

    auto rel32( const std::uint8_t* p, std::uint32_t rva, std::uint32_t insn_len ) -> std::uint32_t
    {
        const auto rel = static_cast< std::int32_t >( read_u32( p ) );
        return static_cast< std::uint32_t >( static_cast< std::int64_t >( rva ) + insn_len + rel );
    }

    struct range
    {
        std::uint32_t begin;
        std::uint32_t end;
    };

    auto exec_ranges( const std::vector< std::uint8_t >& image ) -> std::vector< range >
    {
        std::vector< range > out;
        if ( image.size( ) < 0x40 )
            return out;
        const auto nt = read_u32( image.data( ) + 0x3c );
        const auto file = nt + 4;
        if ( file + 20 >= image.size( ) )
            return out;
        const auto section_count = read_u16( image.data( ) + file + 2 );
        const auto opt_size = read_u16( image.data( ) + file + 16 );
        const auto section_off = file + static_cast< std::uint32_t >( sizeof( IMAGE_FILE_HEADER ) ) + opt_size;
        for ( std::uint16_t i = 0; i < section_count; ++i )
        {
            const auto off = section_off + i * 40u;
            if ( off + 40 > image.size( ) )
                break;
            if ( !( read_u32( image.data( ) + off + 36 ) & IMAGE_SCN_MEM_EXECUTE ) )
                continue;
            char nm[ 9 ]{};
            std::memcpy( nm, image.data( ) + off, 8 );
            if ( is_vm_section_name( nm ) )
                continue;
            const auto va = read_u32( image.data( ) + off + 12 );
            const auto vsize = read_u32( image.data( ) + off + 8 );
            const auto raw = read_u32( image.data( ) + off + 16 );
            const auto span = vsize > raw ? vsize : raw;
            if ( !span || va >= image.size( ) )
                continue;
            range r{};
            r.begin = va;
            r.end = static_cast< std::uint32_t >( ( std::min )( image.size( ), static_cast< std::size_t >( va ) + span ) );
            out.push_back( r );
        }
        return out;
    }

    auto executable( const std::vector< range >& ranges, std::uint32_t rva ) -> bool
    {
        for ( const auto& r : ranges )
        {
            if ( rva >= r.begin && rva < r.end )
                return true;
        }
        return false;
    }

    auto contains_u64( const std::uint8_t* p, std::size_t n, std::uint64_t v ) -> bool
    {
        if ( n < 8 )
            return false;
        for ( std::size_t i = 0; i + 8 <= n; ++i )
        {
            if ( read_u64( p + i ) == v )
                return true;
        }
        return false;
    }

    auto is_security_cookie64( const std::uint8_t* p, std::size_t n ) -> bool
    {
        if ( n < 32 )
            return false;
        return contains_u64( p, ( std::min )( n, static_cast< std::size_t >( 64 ) ), 0x00002B992DDFA232ull );
    }

    auto is_user_main64( const std::uint8_t* p, std::size_t n ) -> bool
    {
        if ( n < 16 )
            return false;
        for ( std::size_t i = 0; i + 5 < ( std::min )( n, static_cast< std::size_t >( 24 ) ); ++i )
        {
            if ( p[ i ] == 0x48 && p[ i + 1 ] == 0x33 && p[ i + 2 ] == 0xC4 )
                return true;
        }
        return false;
    }

    auto is_main_crt64( const std::uint8_t* p, std::size_t n ) -> bool
    {
        if ( n < 18 )
            return false;
        if ( p[ 0 ] != 0x48 || p[ 1 ] != 0x83 || p[ 2 ] != 0xEC || p[ 3 ] != 0x28 )
            return false;
        if ( p[ 4 ] != 0xE8 )
            return false;
        if ( p[ 9 ] != 0x48 || p[ 10 ] != 0x83 || p[ 11 ] != 0xC4 || p[ 12 ] != 0x28 )
            return false;
        if ( p[ 13 ] != 0xE8 && p[ 13 ] != 0xE9 )
            return false;
        if ( n >= 19 && p[ 18 ] != 0xCC && p[ 18 ] != 0x90 && p[ 18 ] != 0x00 )
            return false;
        return true;
    }

    auto is_security_cookie32( const std::uint8_t* p, std::size_t n ) -> bool
    {
        if ( n < 16 )
            return false;
        return contains_u64( p, ( std::min )( n, static_cast< std::size_t >( 48 ) ), 0x00002B992DDFA232ull )
            || ( n >= 8 && read_u32( p ) != 0 && p[ 0 ] == 0xA1 );
    }

    auto is_scrt_seh32( const std::uint8_t* p, std::size_t n ) -> bool
    {
        if ( n < 8 )
            return false;
        if ( p[ 0 ] != 0x55 || p[ 1 ] != 0x8B || p[ 2 ] != 0xEC )
            return false;
        return ( p[ 3 ] == 0x6A && p[ 4 ] == 0xFF && p[ 5 ] == 0x68 )
            || ( p[ 3 ] == 0x83 && p[ 4 ] == 0xEC );
    }

    auto window_has( const std::uint8_t* p, std::size_t n, const std::uint8_t* seq, std::size_t sn ) -> bool
    {
        if ( n < sn )
            return false;
        for ( std::size_t i = 0; i + sn <= n; ++i )
        {
            if ( std::memcmp( p + i, seq, sn ) == 0 )
                return true;
        }
        return false;
    }

    // MSVC x64 __scrt_common_main_seh (exe_common.inl):
    //   mov [rsp+8], rbx
    //   [optional mov [rsp+10], rsi]
    //   push rdi
    //   sub rsp, 20h/28h/30h
    //   mov ecx, 1                 ; __scrt_module_type::exe
    //   call __scrt_initialize_crt
    //   test al, al
    //   je fail
    //   ...
    //   mov [rip+disp], 1          ; initializing
    //   lea rdx, __xi_z / __xc_z
    //   lea rcx, __xi_a / __xc_a
    //   call _initterm_e / _initterm
    //   mov eax, 0FFh on initterm_e fail
    //   mov [rip+disp], 2          ; initialized
    auto score_scrt_seh64( const std::uint8_t* p, std::size_t n ) -> int
    {
        if ( n < 40 )
            return 0;
        auto i = 0u;
        if ( p[ 0 ] != 0x48 || p[ 1 ] != 0x89 || p[ 2 ] != 0x5C || p[ 3 ] != 0x24 || p[ 4 ] != 0x08 )
            return 0;
        i = 5;
        int score = 2;
        if ( n >= 10 && p[ 5 ] == 0x48 && p[ 6 ] == 0x89 && p[ 7 ] == 0x74 && p[ 8 ] == 0x24 && p[ 9 ] == 0x10 )
        {
            i = 10;
            ++score;
        }
        if ( i >= n || p[ i ] != 0x57 )
            return 0;
        ++i;
        ++score;
        if ( i + 4 > n || p[ i ] != 0x48 || p[ i + 1 ] != 0x83 || p[ i + 2 ] != 0xEC )
            return 0;
        const auto frame = p[ i + 3 ];
        if ( frame != 0x20 && frame != 0x28 && frame != 0x30 && frame != 0x38 )
            return 0;
        i += 4;
        ++score;
        if ( i + 10 > n )
            return 0;
        if ( p[ i ] != 0xB9 || p[ i + 1 ] != 0x01 || p[ i + 2 ] != 0x00 || p[ i + 3 ] != 0x00 || p[ i + 4 ] != 0x00 )
            return 0;
        i += 5;
        if ( p[ i ] != 0xE8 )
            return 0;
        i += 5;
        score += 4;
        if ( i + 2 <= n && p[ i ] == 0x84 && p[ i + 1 ] == 0xC0 )
        {
            i += 2;
            score += 3;
        }
        const auto body = p;
        const auto body_n = ( std::min )( n, static_cast< std::size_t >( 0x180 ) );
        const std::uint8_t initterm_fail[] = { 0xB8, 0xFF, 0x00, 0x00, 0x00 };
        const std::uint8_t xor_dil[] = { 0x40, 0x32, 0xFF };
        if ( window_has( body, body_n, initterm_fail, sizeof( initterm_fail ) ) )
            score += 4;
        if ( window_has( body, body_n, xor_dil, sizeof( xor_dil ) ) )
            score += 1;

        auto saw_state1 = false;
        auto saw_state2 = false;
        auto lea_pairs = 0;
        auto init_calls = 0;
        for ( std::size_t k = 0; k + 10 < body_n; ++k )
        {
            if ( body[ k ] == 0xC7 && body[ k + 1 ] == 0x05 )
            {
                const auto imm = read_u32( body + k + 6 );
                if ( imm == 1 )
                    saw_state1 = true;
                if ( imm == 2 )
                    saw_state2 = true;
            }
            if ( body[ k ] == 0x48 && body[ k + 1 ] == 0x8D && ( body[ k + 2 ] == 0x15 || body[ k + 2 ] == 0x0D ) )
            {
                if ( k + 12 < body_n && body[ k + 7 ] == 0x48 && body[ k + 8 ] == 0x8D
                    && ( body[ k + 9 ] == 0x0D || body[ k + 9 ] == 0x15 ) && body[ k + 14 ] == 0xE8 )
                {
                    ++lea_pairs;
                    ++init_calls;
                }
            }
        }
        if ( saw_state1 )
            score += 4;
        if ( saw_state2 )
            score += 4;
        score += ( std::min )( lea_pairs, 2 ) * 3;
        if ( init_calls )
            score += 2;
        return score;
    }

    // MSVC x64 _DllMainCRTStartup:
    //   mov [rsp+8], rbx
    //   mov [rsp+10], rsi
    //   push rdi
    //   sub rsp, 20h/28h
    //   mov rdi, r8 ; mov ebx, edx ; mov rsi, rcx
    //   cmp edx, 1  ; DLL_PROCESS_ATTACH
    //   jne skip
    //   call __security_init_cookie
    //   restore rcx/edx/r8 from rsi/ebx/rdi
    //   restore rbx/rsi, add rsp, pop rdi
    //   jmp/call dllmain_dispatch
    auto score_dll_crt64( const std::uint8_t* p, std::size_t n ) -> int
    {
        if ( n < 48 )
            return 0;
        if ( p[ 0 ] != 0x48 || p[ 1 ] != 0x89 || p[ 2 ] != 0x5C || p[ 3 ] != 0x24 || p[ 4 ] != 0x08 )
            return 0;
        auto i = 5u;
        int score = 1;
        if ( p[ 5 ] == 0x48 && p[ 6 ] == 0x89 && p[ 7 ] == 0x74 && p[ 8 ] == 0x24 && p[ 9 ] == 0x10 )
        {
            i = 10;
            score += 2;
        }
        if ( i >= n || p[ i ] != 0x57 )
            return 0;
        ++i;
        ++score;
        if ( i + 4 > n || p[ i ] != 0x48 || p[ i + 1 ] != 0x83 || p[ i + 2 ] != 0xEC )
            return 0;
        const auto frame = p[ i + 3 ];
        if ( frame != 0x20 && frame != 0x28 && frame != 0x30 )
            return 0;
        i += 4;
        ++score;

        auto saved_r8 = false;
        auto saved_edx = false;
        auto saved_rcx = false;
        auto cmp_reason = false;
        auto cookie_call = false;
        auto restored_args = 0;
        auto epilogue_jmp = false;
        const auto lim = ( std::min )( n, static_cast< std::size_t >( 0x80 ) );
        while ( i + 6 <= lim )
        {
            if ( p[ i ] == 0x49 && p[ i + 1 ] == 0x8B && p[ i + 2 ] == 0xF8 )
            {
                saved_r8 = true;
                i += 3;
                continue;
            }
            if ( p[ i ] == 0x8B && p[ i + 1 ] == 0xDA )
            {
                saved_edx = true;
                i += 2;
                continue;
            }
            if ( p[ i ] == 0x48 && p[ i + 1 ] == 0x8B && p[ i + 2 ] == 0xF1 )
            {
                saved_rcx = true;
                i += 3;
                continue;
            }
            if ( p[ i ] == 0x83 && p[ i + 1 ] == 0xFA && p[ i + 2 ] == 0x01 )
            {
                cmp_reason = true;
                i += 3;
                continue;
            }
            if ( p[ i ] == 0x75 && i + 2 < lim )
            {
                i += 2;
                continue;
            }
            if ( p[ i ] == 0x0F && p[ i + 1 ] == 0x85 && i + 6 <= lim )
            {
                i += 6;
                continue;
            }
            if ( p[ i ] == 0xE8 )
            {
                cookie_call = true;
                i += 5;
                continue;
            }
            if ( p[ i ] == 0x4C && p[ i + 1 ] == 0x8B && p[ i + 2 ] == 0xC7 )
            {
                ++restored_args;
                i += 3;
                continue;
            }
            if ( p[ i ] == 0x8B && p[ i + 1 ] == 0xD3 )
            {
                ++restored_args;
                i += 2;
                continue;
            }
            if ( p[ i ] == 0x48 && p[ i + 1 ] == 0x8B && p[ i + 2 ] == 0xCE )
            {
                ++restored_args;
                i += 3;
                continue;
            }
            if ( p[ i ] == 0x48 && p[ i + 1 ] == 0x8B && p[ i + 2 ] == 0x5C && p[ i + 3 ] == 0x24 )
            {
                i += 5;
                continue;
            }
            if ( p[ i ] == 0x48 && p[ i + 1 ] == 0x8B && p[ i + 2 ] == 0x74 && p[ i + 3 ] == 0x24 )
            {
                i += 5;
                continue;
            }
            if ( p[ i ] == 0x48 && p[ i + 1 ] == 0x83 && p[ i + 2 ] == 0xC4 )
            {
                i += 4;
                continue;
            }
            if ( p[ i ] == 0x5F )
            {
                ++i;
                continue;
            }
            if ( p[ i ] == 0xE9 || p[ i ] == 0xE8 )
            {
                epilogue_jmp = true;
                break;
            }
            if ( p[ i ] == 0xC3 )
            {
                epilogue_jmp = true;
                break;
            }
            break;
        }
        if ( saved_r8 )
            score += 3;
        if ( saved_edx )
            score += 3;
        if ( saved_rcx )
            score += 3;
        if ( cmp_reason )
            score += 5;
        if ( cookie_call )
            score += 3;
        score += ( std::min )( restored_args, 3 ) * 2;
        if ( epilogue_jmp )
            score += 2;
        if ( score_scrt_seh64( p, n ) >= 16 )
            return 0;
        return score;
    }

    auto is_scrt_seh64( const std::uint8_t* p, std::size_t n ) -> bool
    {
        return score_scrt_seh64( p, n ) >= 16;
    }

    auto is_dll_crt64( const std::uint8_t* p, std::size_t n ) -> bool
    {
        return score_dll_crt64( p, n ) >= 18;
    }

    auto valid_stub64( const std::vector< std::uint8_t >& image, const std::vector< range >& ranges, std::uint32_t rva ) -> bool
    {
        if ( !in_image( image, rva, 18 ) || !is_main_crt64( image.data( ) + rva, image.size( ) - rva ) )
            return false;
        if ( is_user_main64( image.data( ) + rva, image.size( ) - rva ) )
            return false;
        const auto call = rel32( image.data( ) + rva + 5, rva, 9 );
        const auto jmp = rel32( image.data( ) + rva + 14, rva, 18 );
        if ( call == jmp || call == rva || jmp == rva )
            return false;
        if ( !executable( ranges, call ) || !executable( ranges, jmp ) )
            return false;
        if ( !in_image( image, call, 32 ) || !in_image( image, jmp, 32 ) )
            return false;
        if ( is_user_main64( image.data( ) + jmp, image.size( ) - jmp ) )
            return false;
        if ( !is_security_cookie64( image.data( ) + call, image.size( ) - call ) )
            return false;
        return is_scrt_seh64( image.data( ) + jmp, image.size( ) - jmp );
    }

    auto valid_stub32( const std::vector< std::uint8_t >& image, const std::vector< range >& ranges, std::uint32_t rva ) -> bool
    {
        if ( !in_image( image, rva, 10 ) )
            return false;
        const auto* p = image.data( ) + rva;
        if ( p[ 0 ] != 0xE8 || p[ 5 ] != 0xE9 )
            return false;
        const auto call = rel32( p + 1, rva, 5 );
        const auto jmp = rel32( p + 6, rva, 10 );
        if ( call == jmp || !executable( ranges, call ) || !executable( ranges, jmp ) )
            return false;
        if ( !in_image( image, call, 16 ) || !in_image( image, jmp, 16 ) )
            return false;
        return is_scrt_seh32( image.data( ) + jmp, image.size( ) - jmp );
    }

    auto follow_jmps( const std::vector< std::uint8_t >& image, std::uint32_t rva ) -> std::uint32_t
    {
        auto cur = rva;
        for ( auto i = 0; i < 8; ++i )
        {
            if ( !in_image( image, cur, 5 ) )
                break;
            auto skip = 0u;
            while ( skip < 8 && in_image( image, cur + skip, 1 ) )
            {
                const auto b = image[ cur + skip ];
                if ( b == 0x90 || b == 0xCC )
                    ++skip;
                else
                    break;
            }
            if ( !in_image( image, cur + skip, 5 ) )
                break;
            const auto* p = image.data( ) + cur + skip;
            if ( p[ 0 ] == 0xE9 )
            {
                cur = rel32( p + 1, cur + skip, 5 );
                continue;
            }
            if ( p[ 0 ] == 0xEB && in_image( image, cur + skip, 2 ) )
            {
                cur = static_cast< std::uint32_t >( static_cast< std::int64_t >( cur + skip + 2 ) + static_cast< std::int8_t >( p[ 1 ] ) );
                continue;
            }
            break;
        }
        return cur;
    }

    struct hit
    {
        std::uint32_t rva;
        int score;
        bool aligned;
    };

    auto better( const hit& a, const hit& b ) -> bool
    {
        if ( a.score != b.score )
            return a.score > b.score;
        if ( a.aligned != b.aligned )
            return a.aligned;
        return a.rva < b.rva;
    }

    auto scan_crt64( const std::vector< std::uint8_t >& image, bool prefer_dll ) -> std::uint32_t
    {
        const auto ranges = exec_ranges( image );
        hit best_exe{ 0, 0, false };
        hit best_dll{ 0, 0, false };
        hit stub{ 0, 0, false };
        for ( const auto& r : ranges )
        {
            if ( r.end <= r.begin + 18 )
                continue;
            for ( auto rva = r.begin; rva + 18 <= r.end; ++rva )
            {
                if ( image[ rva ] != 0x48 && image[ rva ] != 0xE8 )
                    continue;
                if ( valid_stub64( image, ranges, rva ) )
                {
                    hit h{ rva, 100, ( rva & 0xF ) == 0 };
                    if ( better( h, stub ) )
                        stub = h;
                }
                if ( rva + 40 <= r.end )
                {
                    const auto seh = score_scrt_seh64( image.data( ) + rva, image.size( ) - rva );
                    if ( seh >= 16 )
                    {
                        hit h{ rva, seh, ( rva & 0xF ) == 0 };
                        if ( better( h, best_exe ) )
                            best_exe = h;
                    }
                    const auto dll = score_dll_crt64( image.data( ) + rva, image.size( ) - rva );
                    if ( dll >= 18 )
                    {
                        hit h{ rva, dll, ( rva & 0xF ) == 0 };
                        if ( better( h, best_dll ) )
                            best_dll = h;
                    }
                }
            }
        }
        if ( prefer_dll )
        {
            if ( best_dll.rva )
                return best_dll.rva;
            if ( best_exe.rva )
                return best_exe.rva;
            return stub.rva;
        }
        if ( best_exe.rva )
            return best_exe.rva;
        if ( stub.rva )
            return stub.rva;
        return best_dll.rva;
    }

    auto scan_stubs32( const std::vector< std::uint8_t >& image ) -> std::uint32_t
    {
        const auto ranges = exec_ranges( image );
        std::uint32_t aligned = 0;
        std::uint32_t any = 0;
        for ( const auto& r : ranges )
        {
            if ( r.end <= r.begin + 10 )
                continue;
            for ( auto rva = r.begin; rva + 10 <= r.end; ++rva )
            {
                if ( !valid_stub32( image, ranges, rva ) )
                    continue;
                if ( ( rva & 0xF ) == 0 )
                {
                    if ( !aligned )
                        aligned = rva;
                }
                else if ( !any )
                {
                    any = rva;
                }
            }
        }
        return aligned ? aligned : any;
    }
}

auto find_oep( const std::vector< std::uint8_t >& image, bool is64 ) -> std::uint32_t
{
    const auto opt = opt_off( image );
    if ( !opt )
        return 0;
    const auto current = read_u32( image.data( ) + opt + 16 );
    const auto ranges = exec_ranges( image );
    const auto landed = follow_jmps( image, current );
    const auto dll = is_dll_image( image );
    if ( is64 )
    {
        if ( in_image( image, landed, 40 ) )
        {
            if ( dll && is_dll_crt64( image.data( ) + landed, image.size( ) - landed ) )
                return landed;
            if ( is_scrt_seh64( image.data( ) + landed, image.size( ) - landed ) )
                return landed;
            if ( valid_stub64( image, ranges, landed ) )
                return landed;
        }
        if ( in_image( image, current, 40 ) )
        {
            if ( dll && is_dll_crt64( image.data( ) + current, image.size( ) - current ) )
                return current;
            if ( is_scrt_seh64( image.data( ) + current, image.size( ) - current ) )
                return current;
            if ( valid_stub64( image, ranges, current ) )
                return current;
        }
        const auto scanned = scan_crt64( image, dll );
        return scanned ? scanned : current;
    }
    if ( valid_stub32( image, ranges, landed ) )
        return landed;
    if ( valid_stub32( image, ranges, current ) )
        return current;
    const auto scanned = scan_stubs32( image );
    return scanned ? scanned : current;
}

auto apply_oep( std::vector< std::uint8_t >& image, std::uint32_t oep ) -> void
{
    const auto opt = opt_off( image );
    if ( !opt || !oep )
        return;
    write_u32( image.data( ) + opt + 16, oep );
}
