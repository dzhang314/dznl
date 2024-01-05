#ifndef DZNL_TYPE_TRAITS_HPP_INCLUDED
#define DZNL_TYPE_TRAITS_HPP_INCLUDED

namespace dznl {


template <typename T>
inline constexpr bool is_void = false;

template <>
inline constexpr bool is_void<void> = true;


} // namespace dznl

#endif // DZNL_TYPE_TRAITS_HPP_INCLUDED
