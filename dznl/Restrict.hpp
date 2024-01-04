#ifndef DZNL_RESTRICT_HPP_INCLUDED
#define DZNL_RESTRICT_HPP_INCLUDED

#if defined(__GNUC__)
#define DZNL_RESTRICT __restrict__
#elif defined(_MSC_VER)
#define DZNL_RESTRICT __restrict
#else
#define DZNL_RESTRICT
#endif

#endif // DZNL_RESTRICT_HPP_INCLUDED
