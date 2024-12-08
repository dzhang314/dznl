#ifndef DZNL_TUPLE_HPP_INCLUDED
#define DZNL_TUPLE_HPP_INCLUDED

namespace dznl {


template <typename...>
struct Tuple;


template <>
struct Tuple<> {};


template <typename T1>
struct Tuple<T1> {
    T1 first;
};


template <typename T1, typename T2>
struct Tuple<T1, T2> {
    T1 first;
    T2 second;
};


template <typename T1, typename T2, typename T3>
struct Tuple<T1, T2, T3> {
    T1 first;
    T2 second;
    T3 third;
};


template <typename T1, typename T2, typename T3, typename T4>
struct Tuple<T1, T2, T3, T4> {
    T1 first;
    T2 second;
    T3 third;
    T4 fourth;
};


template <typename T1, typename T2, typename T3, typename T4, typename T5>
struct Tuple<T1, T2, T3, T4, T5> {
    T1 first;
    T2 second;
    T3 third;
    T4 fourth;
    T5 fifth;
};


template <
    typename T1,
    typename T2,
    typename T3,
    typename T4,
    typename T5,
    typename T6>
struct Tuple<T1, T2, T3, T4, T5, T6> {
    T1 first;
    T2 second;
    T3 third;
    T4 fourth;
    T5 fifth;
    T6 sixth;
};


template <
    typename T1,
    typename T2,
    typename T3,
    typename T4,
    typename T5,
    typename T6,
    typename T7>
struct Tuple<T1, T2, T3, T4, T5, T6, T7> {
    T1 first;
    T2 second;
    T3 third;
    T4 fourth;
    T5 fifth;
    T6 sixth;
    T7 seventh;
};


template <
    typename T1,
    typename T2,
    typename T3,
    typename T4,
    typename T5,
    typename T6,
    typename T7,
    typename T8>
struct Tuple<T1, T2, T3, T4, T5, T6, T7, T8> {
    T1 first;
    T2 second;
    T3 third;
    T4 fourth;
    T5 fifth;
    T6 sixth;
    T7 seventh;
    T8 eighth;
};


template <
    typename T1,
    typename T2,
    typename T3,
    typename T4,
    typename T5,
    typename T6,
    typename T7,
    typename T8,
    typename T9>
struct Tuple<T1, T2, T3, T4, T5, T6, T7, T8, T9> {
    T1 first;
    T2 second;
    T3 third;
    T4 fourth;
    T5 fifth;
    T6 sixth;
    T7 seventh;
    T8 eighth;
    T9 ninth;
};


} // namespace dznl

#endif // DZNL_TUPLE_HPP_INCLUDED
