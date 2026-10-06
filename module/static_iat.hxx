#pragma once
#include "iat.hxx"

// Runs the loader in Unicorn with a synthetic OS. No guest API is called on the host.
auto initialize_static_imports( const std::vector< std::uint8_t >& packed,
    const std::vector< std::uint8_t >& decompressed, std::uint32_t timeout_ms = 180000 ) -> runtime_image;
