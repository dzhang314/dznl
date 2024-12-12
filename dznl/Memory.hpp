#ifndef DZNL_MEMORY_HPP_INCLUDED
#define DZNL_MEMORY_HPP_INCLUDED

#include "Macros.hpp"

namespace dznl {


using size_t = decltype(sizeof(0));


constexpr void *memcpy(void *dst, const void *src, size_t n) noexcept {
#if DZNL_HAS_BUILTIN(__builtin_memcpy)
    return __builtin_memcpy(dst, src, n);
#else
    char *dst_char = static_cast<char *>(dst);
    const char *src_char = static_cast<const char *>(src);
    for (size_t i = 0; i < n; ++i) { dst_char[i] = src_char[i]; }
    return dst;
#endif
}


template <typename DST_T, typename SRC_T>
constexpr DST_T bit_cast(const SRC_T &x) noexcept {
    static_assert(sizeof(DST_T) == sizeof(SRC_T));
#if DZNL_HAS_BUILTIN(__builtin_bit_cast)
    return __builtin_bit_cast(DST_T, x);
#else
    DST_T result;
    memcpy(&result, &x, sizeof(DST_T));
    return result;
#endif
}


} // namespace dznl

#endif // DZNL_MEMORY_HPP_INCLUDED