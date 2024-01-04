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
    typename CONSTRAINT_FUNCTOR_T,
    typename ACCESSOR_T>
class NelderMeadOptimizer {

    OBJECTIVE_FUNCTOR_T &m_objective_function;
    CONSTRAINT_FUNCTOR_T &m_constraint_function;
    ACCESSOR_T m_workspace;
    INDEX_T m_dimension;
    bool m_has_terminated;

    constexpr INDEX_T vertex_offset(INDEX_T i) const noexcept {
        INDEX_T offset = m_dimension;
        ++offset;
        return offset * i;
    }

    constexpr bool
    vertices_in_order(const INDEX_T &i, const INDEX_T &j) noexcept {
        INDEX_T offset_i = vertex_offset(i) + m_dimension;
        INDEX_T offset_j = vertex_offset(j) + m_dimension;
        REAL_T &objective_i = m_workspace[offset_i];
        REAL_T &objective_j = m_workspace[offset_j];
        return (objective_i < objective_j) || (objective_i == objective_j);
    }

    constexpr void swap_vertices(const INDEX_T &i, const INDEX_T &j) noexcept {
        INDEX_T offset_i = vertex_offset(i);
        INDEX_T offset_j = vertex_offset(j);
        ACCESSOR_T vertex_i = m_workspace + offset_i;
        ACCESSOR_T vertex_j = m_workspace + offset_j;
        INDEX_T k = zero<INDEX_T>();
        while (k < m_dimension) {
            const REAL_T temp = vertex_i[k];
            vertex_i[k] = vertex_j[k];
            vertex_j[k] = temp;
            ++k;
        }
        const REAL_T temp = vertex_i[k];
        vertex_i[k] = vertex_j[k];
        vertex_j[k] = temp;
    }

    constexpr void insert_vertex(const INDEX_T &i) noexcept {
        INDEX_T ZERO = zero<INDEX_T>();
        for (INDEX_T j = i; ZERO < j;) {
            const INDEX_T k = j;
            --j;
            if (vertices_in_order(j, k)) { break; }
            swap_vertices(j, k);
        }
    }

public:

    constexpr const REAL_T *current_point() const noexcept {
        return m_workspace;
    }

    static constexpr INDEX_T workspace_size(INDEX_T dimension) noexcept {
        INDEX_T dimension_plus_one = ++dimension;
        ++dimension;
        return (++dimension) * dimension_plus_one;
    }

    explicit constexpr NelderMeadOptimizer(
        OBJECTIVE_FUNCTOR_T &objective_function,
        CONSTRAINT_FUNCTOR_T &constraint_function,
        const ACCESSOR_T &initial_point,
        const INDEX_T &dimension,
        const REAL_T &initial_step_length,
        const ACCESSOR_T &workspace
    )
        : m_objective_function(objective_function)
        , m_constraint_function(constraint_function)
        , m_workspace(workspace)
        , m_dimension(dimension)
        , m_has_terminated(false) {

        // Copy `initial_point` into `workspace`.
        ACCESSOR_T x = initial_point;
        for (INDEX_T i = zero<INDEX_T>(); i < m_dimension; ++i) {
            m_workspace[i] = x[i];
        }

        // Call `constraint_function` to check if `initial_point` is feasible.
        if (!m_constraint_function(m_workspace)) {
            // If not, immediately terminate iteration
            // by setting `has_terminated` flag.
            m_has_terminated = true;
            return;
        }

        // Call `objective_function` to compute objective value at constrained
        // `initial_point` and ensure returned value is not NaN.
        const REAL_T initial_value = m_objective_function(m_workspace);
        if (is_nan(initial_value)) {
            m_has_terminated = true;
            return;
        }
        m_workspace[m_dimension] = initial_value;

        // Generate initial simplex by adding `initial_step_length`
        // to each coordinate of constrained `initial_point`.
        INDEX_T k = m_dimension;
        ++k;
        for (INDEX_T i = zero<INDEX_T>(); i < m_dimension;) {
            ACCESSOR_T current_vertex = m_workspace + k;
            for (INDEX_T j = zero<INDEX_T>(); j < m_dimension; ++j) {
                m_workspace[k] = (i == j) ? x[j] + initial_step_length : x[j];
                ++k;
            }

            // Call `constraint_function` to check if
            // each vertex of initial simplex is feasible.
            if (!m_constraint_function(current_vertex)) {
                // If not, immediately terminate iteration
                // by setting `has_terminated` flag.
                m_has_terminated = true;
                return;
                // TODO: Adaptive strategy to try other vertex locations.
            }

            // Call `objective_function` to compute objective value
            // at each constrained vertex of initial simplex.
            const REAL_T vertex_value = m_objective_function(current_vertex);
            if (is_nan(vertex_value)) {
                m_has_terminated = true;
                return;
                // TODO: Adaptive strategy to try other vertex locations.
            }
            m_workspace[k] = vertex_value;
            ++k;
            insert_vertex(++i);
        }
    }

}; // class NelderMeadOptimizer


} // namespace dznl

#endif // DZNL_NELDER_MEAD_OPTIMIZER_HPP_INCLUDED
