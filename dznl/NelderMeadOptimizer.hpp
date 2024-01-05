#ifndef DZNL_NELDER_MEAD_OPTIMIZER_HPP_INCLUDED
#define DZNL_NELDER_MEAD_OPTIMIZER_HPP_INCLUDED

#include "FloatingPointProperties.hpp"
#include "Macros.hpp"
#include "NumericFunctions.hpp"
#include "Tuple.hpp"

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

    constexpr INDEX_T vertex_offset(DZNL_CONST INDEX_T &i) DZNL_CONST noexcept {
        INDEX_T offset = m_dimension;
        ++offset;
        return offset * i;
    }

    constexpr bool
    order_vertices(DZNL_CONST INDEX_T &i, DZNL_CONST INDEX_T &j) noexcept {
        DZNL_CONST INDEX_T offset_i = vertex_offset(i);
        DZNL_CONST INDEX_T offset_j = vertex_offset(j);
        DZNL_CONST ACCESSOR_T vertex_i = m_workspace + offset_i;
        DZNL_CONST ACCESSOR_T vertex_j = m_workspace + offset_j;
        DZNL_CONST REAL_T &objective_i = vertex_i[m_dimension];
        DZNL_CONST REAL_T &objective_j = vertex_j[m_dimension];
        if (objective_j < objective_i) {
            INDEX_T k = zero<INDEX_T>();
            while (k < m_dimension) {
                DZNL_CONST REAL_T temp = vertex_i[k];
                vertex_i[k] = vertex_j[k];
                vertex_j[k] = temp;
                ++k;
            }
            DZNL_CONST REAL_T temp = vertex_i[k];
            vertex_i[k] = vertex_j[k];
            vertex_j[k] = temp;
            return true;
        } else {
            return false;
        }
    }

    constexpr void insert_vertex(DZNL_CONST INDEX_T &i) noexcept {
        DZNL_CONST INDEX_T ZERO = zero<INDEX_T>();
        for (INDEX_T j = i; ZERO < j;) {
            DZNL_CONST INDEX_T k = j;
            --j;
            if (!order_vertices(j, k)) { break; }
        }
    }

    constexpr Tuple<bool, bool> try_coordinate_step(
        DZNL_CONST ACCESSOR_T &dst,
        DZNL_CONST ACCESSOR_T &src,
        DZNL_CONST INDEX_T &i,
        DZNL_CONST REAL_T &step_length,
        bool forward
    ) noexcept {
        for (INDEX_T j = zero<INDEX_T>(); j < m_dimension; ++j) {
            dst[j] = src[j];
        }
        DZNL_CONST REAL_T x = dst[i];
        DZNL_CONST REAL_T x_prime = forward ? x + step_length : x - step_length;
        if (x == x_prime) { return {false, false}; }
        dst[i] = x_prime;
        if (m_constraint_function(dst)) {
            DZNL_CONST REAL_T objective_value = m_objective_function(dst);
            if (!is_nan(objective_value)) {
                dst[m_dimension] = objective_value;
                return {true, true};
            }
        }
        return {true, false};
    }

    constexpr bool generate_initial_vertex(
        DZNL_CONST ACCESSOR_T &dst,
        DZNL_CONST ACCESSOR_T &src,
        DZNL_CONST INDEX_T &i,
        REAL_T step_length
    ) noexcept {
        DZNL_CONST REAL_T ONE = one<REAL_T>();
        DZNL_CONST REAL_T TWO = ONE + ONE;
        while (true) {
            const auto [forward_change, forward_success] =
                try_coordinate_step(dst, src, i, step_length, true);
            if (forward_success) { return true; }
            const auto [backward_change, backward_success] =
                try_coordinate_step(dst, src, i, step_length, false);
            if (backward_success) { return true; }
            if (!(forward_change || backward_change)) { return false; }
            step_length = step_length / TWO;
        }
    }

public:

    static constexpr INDEX_T workspace_size(INDEX_T dimension) noexcept {
        INDEX_T dimension_plus_one = dimension;
        ++dimension_plus_one;
        INDEX_T dimension_plus_one_squared =
            dimension_plus_one * dimension_plus_one;
        INDEX_T double_dimension = dimension + dimension;
        INDEX_T triple_dimension = double_dimension + dimension;
        return dimension_plus_one_squared + triple_dimension;
    }

    constexpr ACCESSOR_T current_point() DZNL_CONST noexcept {
        return m_workspace;
    }

    constexpr REAL_T current_objective_value() DZNL_CONST noexcept {
        return m_workspace[m_dimension];
    }

    explicit constexpr NelderMeadOptimizer(
        OBJECTIVE_FUNCTOR_T &objective_function,
        CONSTRAINT_FUNCTOR_T &constraint_function,
        DZNL_CONST ACCESSOR_T &initial_point,
        DZNL_CONST INDEX_T &dimension,
        DZNL_CONST REAL_T &initial_step_length,
        DZNL_CONST ACCESSOR_T &workspace
    ) noexcept
        : m_objective_function(objective_function)
        , m_constraint_function(constraint_function)
        , m_workspace(workspace)
        , m_dimension(dimension)
        , m_has_terminated(false) {

        // Copy initial point into beginning of workspace.
        ACCESSOR_T x = initial_point;
        for (INDEX_T i = zero<INDEX_T>(); i < m_dimension; ++i) {
            m_workspace[i] = x[i];
        }

        // Call constraint function to check feasibility of initial point.
        if (!m_constraint_function(m_workspace)) {
            // If initial point is infeasible, immediately terminate.
            m_has_terminated = true;
            return;
        }

        // Compute objective value at constrained initial point.
        DZNL_CONST REAL_T initial_value = m_objective_function(m_workspace);
        // If objective value is NaN, immediately terminate.
        if (is_nan(initial_value)) {
            m_has_terminated = true;
            return;
        }

        // Store objective value in workspace
        // immediately after constrained initial point.
        m_workspace[m_dimension] = initial_value;

        // Generate active simplex. The first (dimension + 1)^2 workspace
        // entries will contain vertices of the active simplex, each followed
        // immediately by its objective value.
        for (INDEX_T i = zero<INDEX_T>(); i < m_dimension;) {
            DZNL_CONST INDEX_T coordinate_index = i;
            ++i;
            DZNL_CONST INDEX_T offset_i = vertex_offset(i);
            DZNL_CONST ACCESSOR_T vertex_i = m_workspace + offset_i;
            const bool success = generate_initial_vertex(
                vertex_i, m_workspace, coordinate_index, initial_step_length
            );
            if (!success) {
                m_has_terminated = true;
                return;
            }
            insert_vertex(i);
        }
    }

    constexpr void step() noexcept {
        if (!m_has_terminated) {

            // Vertices of the active simplex are stored in increasing
            // order by objective value, so the worst vertex is last.
            INDEX_T worst_offset = vertex_offset(m_dimension);
            ACCESSOR_T worst_vertex = m_workspace + worst_offset;
            DZNL_CONST REAL_T worst_value = worst_vertex[m_dimension];

            // Compute centroid of all vertices except the worst.
            INDEX_T centroid_offset = worst_offset + m_dimension;
            ++centroid_offset;
            ACCESSOR_T centroid = m_workspace + centroid_offset;
            for (INDEX_T i = zero<INDEX_T>(); i < m_dimension; ++i) {
                centroid[i] = zero<REAL_T>();
            }
            REAL_T denominator = zero<REAL_T>();
            DZNL_CONST REAL_T ONE = one<REAL_T>();
            for (INDEX_T i = zero<INDEX_T>(); i < m_dimension; ++i) {
                INDEX_T current_offset = vertex_offset(i);
                ACCESSOR_T current_vertex = m_workspace + current_offset;
                for (INDEX_T j = zero<INDEX_T>(); j < m_dimension; ++j) {
                    centroid[j] = centroid[j] + current_vertex[j];
                }
                denominator = denominator + ONE;
            }
            for (INDEX_T i = zero<INDEX_T>(); i < m_dimension; ++i) {
                centroid[i] = centroid[i] / denominator;
            }

            // Compute reflection of worst vertex through centroid.
            INDEX_T reflected_offset = centroid_offset + m_dimension;
            ACCESSOR_T reflected_point = m_workspace + reflected_offset;
            for (INDEX_T i = zero<INDEX_T>(); i < m_dimension; ++i) {
                reflected_point[i] = twice(centroid[i]) - worst_vertex[i];
            }

            // Constrain reflected point and compute its objective value.
            bool reflected_feasible = false;
            REAL_T threshold_value = worst_value;
            if (m_constraint_function(reflected_point)) {
                DZNL_CONST REAL_T reflected_value =
                    m_objective_function(reflected_point);
                if (!is_nan(reflected_value)) {
                    reflected_feasible = true;
                    threshold_value = reflected_value;

                    // If the reflected point is feasible and better than
                    // the previous best vertex, try expanding the simplex.
                    DZNL_CONST REAL_T best_value = m_workspace[m_dimension];
                    if (reflected_value < best_value) {
                        INDEX_T expanded_offset =
                            reflected_offset + m_dimension;
                        ACCESSOR_T expanded_vertex =
                            m_workspace + expanded_offset;
                        for (INDEX_T i = zero<INDEX_T>(); i < m_dimension;
                             ++i) {
                            expanded_vertex[i] =
                                twice(reflected_point[i]) - centroid[i];
                        }

                        // Replace worst vertex with whichever is better
                        // between the reflected and expanded points.
                        if (m_constraint_function(expanded_vertex)) {
                            DZNL_CONST REAL_T expanded_value =
                                m_objective_function(expanded_vertex);
                            if (expanded_value < reflected_value) {
                                for (INDEX_T i = zero<INDEX_T>();
                                     i < m_dimension;
                                     ++i) {
                                    worst_vertex[i] = expanded_vertex[i];
                                }
                                worst_vertex[m_dimension] = expanded_value;
                                insert_vertex(m_dimension);
                                return;
                            }
                        }
                        for (INDEX_T i = zero<INDEX_T>(); i < m_dimension;
                             ++i) {
                            worst_vertex[i] = reflected_point[i];
                        }
                        worst_vertex[m_dimension] = reflected_value;
                        insert_vertex(m_dimension);
                        return;
                    }

                    // Otherwise, if the reflected point is feasible and better
                    // than the second-worst vertex, accept the reflected point
                    // without trying expansion.
                    --worst_offset;
                    DZNL_CONST REAL_T second_worst_value =
                        m_workspace[worst_offset];
                    if (reflected_value < second_worst_value) {
                        for (INDEX_T i = zero<INDEX_T>(); i < m_dimension;
                             ++i) {
                            worst_vertex[i] = reflected_point[i];
                        }
                        worst_vertex[m_dimension] = reflected_value;
                        insert_vertex(m_dimension);
                        return;
                    }
                }
            }

            // At this point, the reflected point is either infeasible or worse
            // than the second-worst vertex. If we accepted it, it would simply
            // be the worst vertex again, so we need to contract or shrink.

            const REAL_T TWO = ONE + ONE;
            const REAL_T HALF = ONE / TWO;

            if ((!reflected_feasible) || (threshold_value < worst_value)) {
                for (INDEX_T i = zero<INDEX_T>(); i < m_dimension; ++i) {
                    reflected_point[i] =
                        HALF * (reflected_point[i] + centroid[i]);
                }
                if (m_constraint_function(reflected_point)) {
                    const REAL_T contracted_value =
                        m_objective_function(reflected_point);
                    if (contracted_value < threshold_value) {
                        for (INDEX_T i = zero<INDEX_T>(); i < m_dimension;
                             ++i) {
                            worst_vertex[i] = reflected_point[i];
                        }
                        worst_vertex[m_dimension] = contracted_value;
                        insert_vertex(m_dimension);
                        return;
                    }
                }
            }

            for (INDEX_T i = zero<INDEX_T>(); i < m_dimension; ++i) {
                reflected_point[i] = HALF * (worst_vertex[i] + centroid[i]);
            }
            if (m_constraint_function(reflected_point)) {
                const REAL_T contracted_value =
                    m_objective_function(reflected_point);
                if (contracted_value < worst_value) {
                    for (INDEX_T i = zero<INDEX_T>(); i < m_dimension; ++i) {
                        worst_vertex[i] = reflected_point[i];
                    }
                    worst_vertex[m_dimension] = contracted_value;
                    insert_vertex(m_dimension);
                    return;
                }
            }

            for (INDEX_T i = zero<INDEX_T>(); i < m_dimension;) {
                ++i;
                INDEX_T offset_i = vertex_offset(i);
                ACCESSOR_T vertex_i = m_workspace + offset_i;
                for (INDEX_T j = zero<INDEX_T>(); j < m_dimension; ++j) {
                    vertex_i[j] = HALF * (vertex_i[j] + m_workspace[j]);
                }
                if (!m_constraint_function(vertex_i)) {
                    m_has_terminated = true;
                    return;
                }
                vertex_i[m_dimension] = m_objective_function(vertex_i);
            }

            for (INDEX_T i = zero<INDEX_T>(); i < m_dimension;) {
                ++i;
                insert_vertex(i);
            }
        }
    }

}; // class NelderMeadOptimizer


} // namespace dznl

#endif // DZNL_NELDER_MEAD_OPTIMIZER_HPP_INCLUDED
