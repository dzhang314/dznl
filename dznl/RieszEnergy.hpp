#ifndef DZNL_RIESZ_ENERGY_HPP_INCLUDED
#define DZNL_RIESZ_ENERGY_HPP_INCLUDED

#include "Macros.hpp"
#include "NumericFunctions.hpp"

namespace dznl {


template <
    typename REAL_T,
    typename INDEX_T,
    typename ACCESSOR_T = DZNL_CONST REAL_T *DZNL_RESTRICT>
constexpr REAL_T riesz_energy(
    DZNL_CONST ACCESSOR_T &points,
    DZNL_CONST INDEX_T &num_points,
    DZNL_CONST INDEX_T &dimension
) noexcept {
    REAL_T result = zero<REAL_T>();
    for (INDEX_T j = zero<INDEX_T>(); j < num_points; ++j) {
        DZNL_CONST INDEX_T offset_j = j * dimension;
        DZNL_CONST ACCESSOR_T point_j = points + offset_j;
        for (INDEX_T i = zero<INDEX_T>(); i < j; ++i) {
            DZNL_CONST INDEX_T offset_i = i * dimension;
            DZNL_CONST ACCESSOR_T point_i = points + offset_i;
            REAL_T dist_sq = zero<REAL_T>();
            for (INDEX_T k = zero<INDEX_T>(); k < dimension; ++k) {
                DZNL_CONST REAL_T diff = point_i[k] - point_j[k];
                dist_sq += square(diff);
            }
            DZNL_CONST REAL_T dist = sqrt(dist_sq);
            DZNL_CONST REAL_T inv_dist = inv(dist);
            result += inv_dist;
        }
    }
    return result;
}


} // namespace dznl

#endif // DZNL_RIESZ_ENERGY_HPP_INCLUDED
