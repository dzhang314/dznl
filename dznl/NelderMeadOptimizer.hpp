#ifndef DZNL_NELDER_MEAD_OPTIMIZER_HPP_INCLUDED
#define DZNL_NELDER_MEAD_OPTIMIZER_HPP_INCLUDED

#include "FloatingPointProperties.hpp"
#include "NumericFunctions.hpp"
#include "Restrict.hpp"

namespace dznl {


template <
    typename REAL_T,
    typename INDEX_T,
    typename OBJECTIVE_FUNCTOR_T,
    typename CONSTRAINT_FUNCTOR_T>
class NelderMeadOptimizer {

    OBJECTIVE_FUNCTOR_T &objective_function;
    CONSTRAINT_FUNCTOR_T &constraint_function;
    REAL_T *DZNL_RESTRICT workspace;
    REAL_T objective_value;
    REAL_T last_step_length;
    INDEX_T dimension;
    bool has_terminated;

    constexpr INDEX_T vertex_offset(const INDEX_T &i) const noexcept {
        INDEX_T offset = dimension;
        ++offset;
        return offset * i;
    }

    constexpr bool
    vertices_in_order(const INDEX_T &i, const INDEX_T &j) const noexcept {
        return workspace[vertex_offset(i) + dimension] <=
               workspace[vertex_offset(j) + dimension];
    }

    constexpr void swap_vertices(const INDEX_T &i, const INDEX_T &j) noexcept {
        REAL_T *const DZNL_RESTRICT vertex_i = workspace + vertex_offset(i);
        REAL_T *const DZNL_RESTRICT vertex_j = workspace + vertex_offset(j);
        for (INDEX_T k = zero<INDEX_T>(); k <= dimension; ++k) {
            const REAL_T temp = vertex_i[k];
            vertex_i[k] = vertex_j[k];
            vertex_j[k] = temp;
        }
    }

    constexpr void insert_vertex(const INDEX_T &i) noexcept {
        for (INDEX_T j = i; !is_zero(j);) {
            const INDEX_T k = j;
            --j;
            if (vertices_in_order(j, k)) { break; }
            swap_vertices(j, k);
        }
    }

public:

    constexpr const REAL_T *current_point() const noexcept { return workspace; }

    static constexpr INDEX_T workspace_size(const INDEX_T &dimension) noexcept {
        const INDEX_T ONE = one<INDEX_T>();
        const INDEX_T TWO = ONE + ONE;
        return (dimension + TWO) * (dimension + ONE);
    }

    explicit constexpr NelderMeadOptimizer(
        OBJECTIVE_FUNCTOR_T &objective_function,
        CONSTRAINT_FUNCTOR_T &constraint_function,
        const REAL_T *const DZNL_RESTRICT initial_point,
        const INDEX_T &dimension,
        const REAL_T &initial_step_length,
        REAL_T *const DZNL_RESTRICT workspace,
    )
        : objective_function(objective_function)
        , constraint_function(constraint_function)
        , workspace(workspace)
        , objective_value(zero<REAL_T>())
        , last_step_length(initial_step_length)
        , dimension(dimension)
        , has_terminated(false) {

        // Copy `initial_point` into `workspace`.
        INDEX_T k = zero<INDEX_T>();
        for (INDEX_T i = zero<INDEX_T>(); i < dimension; ++i) {
            workspace[k++] = initial_point[i];
        }

        // Call `constraint_function` to check if `initial_point` is feasible.
        if (!constraint_function(workspace)) {
            // If not, immediately terminate iteration
            // by setting `has_terminated` flag.
            has_terminated = true;
            return;
        }

        // Call `objective_function` to compute objective value at constrained
        // `initial_point` and ensure returned value is not NaN.
        const REAL_T initial_value = objective_function(workspace);
        if (is_nan(initial_value)) {
            has_terminated = true;
            return;
        }
        workspace[k++] = initial_value;

        // Generate initial simplex by adding `initial_step_length`
        // to each coordinate of constrained `initial_point`.
        for (INDEX_T i = zero<INDEX_T>(); i < dimension; ++i) {
            REAL_T *const current_vertex = workspace + k;
            for (INDEX_T j = zero<INDEX_T>(); j < dimension; ++j) {
                workspace[k++] =
                    (i == j) ? workspace[i] + last_step_length : workspace[i];
            }

            // Call `constraint_function` to check if
            // each vertex of initial simplex is feasible.
            if (!constraint_function(current_vertex)) {
                // If not, immediately terminate iteration
                // by setting `has_terminated` flag.
                has_terminated = true;
                return;
                // TODO: Adaptive strategy to try other vertex locations.
            }

            // Call `objective_function` to compute objective value
            // at each constrained vertex of initial simplex.
            const REAL_T vertex_value = objective_function(current_vertex);
            if (is_nan(vertex_value)) {
                has_terminated = true;
                return;
                // TODO: Adaptive strategy to try other vertex locations.
            }
            workspace[k++] = vertex_value;
        }

        // Sort vertices of initial simplex in
        // ascending order of objective value.
    }


}; // class NelderMeadOptimizer


} // namespace dznl

#endif // DZNL_NELDER_MEAD_OPTIMIZER_HPP_INCLUDED
