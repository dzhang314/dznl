#ifndef DZNL_RESTRICT_HPP_INCLUDED
#define DZNL_RESTRICT_HPP_INCLUDED

#ifdef __GNUC__
#define DZNL_RESTRICT __restrict__
#elif defined(_MSC_VER)
#define DZNL_RESTRICT __restrict
#else
#define DZNL_RESTRICT
#endif

#ifdef DZNL_REMOVE_CONST
#define DZNL_CONST
#else
#define DZNL_CONST const
#endif

#ifdef __has_builtin
#define DZNL_HAS_BUILTIN(x) __has_builtin(x)
#else
#define DZNL_HAS_BUILTIN(x) 0
#endif

#endif // DZNL_RESTRICT_HPP_INCLUDED
