#ifndef DZNL_CONTAINERS_HPP_INCLUDED
#define DZNL_CONTAINERS_HPP_INCLUDED

namespace dznl {


template <typename T1, typename T2>
struct Pair {
    T1 first;
    T2 second;
};


template <typename T1, typename T2, typename T3>
struct Triple {
    T1 first;
    T2 second;
    T3 third;
};


template <typename T1, typename T2, typename T3, typename T4>
struct Quadruple {
    T1 first;
    T2 second;
    T3 third;
    T4 fourth;
};


template <typename T1, typename T2, typename T3, typename T4, typename T5>
struct Quintuple {
    T1 first;
    T2 second;
    T3 third;
    T4 fourth;
    T5 fifth;
};


} // namespace dznl

#endif // DZNL_CONTAINERS_HPP_INCLUDED
