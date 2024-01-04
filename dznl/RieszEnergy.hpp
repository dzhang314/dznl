#ifndef DZNL_RIESZ_ENERGY_HPP_INCLUDED
#define DZNL_RIESZ_ENERGY_HPP_INCLUDED

#include "Macros.hpp"
#include "NumericFunctions.hpp"

namespace dznl {


template <typename REAL_T, typename INDEX_T>
constexpr REAL_T riesz_energy(
    const REAL_T *const DZNL_RESTRICT points,
    const INDEX_T num_points,
    const INDEX_T dimension
) noexcept {
    REAL_T result = zero<REAL_T>();
    for (INDEX_T j = one<INDEX_T>(); j < num_points; ++j) {
        for (INDEX_T i = zero<INDEX_T>(); i < j; ++i) {
            REAL_T dist_sq = zero<REAL_T>();
            for (INDEX_T k = zero<INDEX_T>(); k < dimension; ++k) {
                dist_sq += square(
                    points[i * dimension + k] - points[j * dimension + k]
                );
            }
            result += inv(sqrt(dist_sq));
        }
    }
    return result;
}


} // namespace dznl

#endif // DZNL_RIESZ_ENERGY_HPP_INCLUDED
