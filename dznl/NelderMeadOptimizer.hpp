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
    typename ACCESSOR_T = REAL_T *DZNL_RESTRICT>
class NelderMeadOptimizer {

private: // =================================================== MEMBER VARIABLES

    OBJECTIVE_FUNCTOR_T &m_objective_function;
    CONSTRAINT_FUNCTOR_T &m_constraint_function;
    ACCESSOR_T m_workspace;
    INDEX_T m_dimension;
    bool m_has_terminated;

private: // ================================================== VERTEX REORDERING

    /**
     * @brief Return the offset of the `i`th vertex in the active simplex.
     *
     * Each vertex is an array of length `m_dimension + 1` consisting of
     * `m_dimension` coordinates followed by the value of the objective
     * function evaluated at those coordinates.
     */
    constexpr INDEX_T vertex_offset(DZNL_CONST INDEX_T &i) DZNL_CONST noexcept {
        INDEX_T vertex_size = m_dimension;
        ++vertex_size; // Each vertex is followed by its
                       // corresponding objective value.
        return vertex_size * i;
    }

    /**
     * @brief Swap two vertices in the active simplex.
     *
     * Coordinates and objective values of both vertices are swapped in-place.
     */
    constexpr void
    swap_vertices(DZNL_CONST ACCESSOR_T &v, DZNL_CONST ACCESSOR_T &w) noexcept {
        INDEX_T i = zero<INDEX_T>();
        for (; i < m_dimension; ++i) {
            DZNL_CONST REAL_T temp = v[i];
            v[i] = w[i];
            w[i] = temp;
        }
        DZNL_CONST REAL_T temp = v[i];
        v[i] = w[i];
        w[i] = temp;
    }

    /**
     * @brief Compare the objective values of two vertices in the active
     *        simplex and, if necessary, swap them so that the objective
     *        value of vertex `i` does not exceed that of vertex `j`.
     *
     * @return true if a swap occurred.
     * @return false if no swap occurred.
     */
    constexpr bool
    order_vertices(DZNL_CONST INDEX_T &i, DZNL_CONST INDEX_T &j) noexcept {
        DZNL_CONST INDEX_T offset_i = vertex_offset(i);
        DZNL_CONST INDEX_T offset_j = vertex_offset(j);
        DZNL_CONST ACCESSOR_T vertex_i = m_workspace + offset_i;
        DZNL_CONST ACCESSOR_T vertex_j = m_workspace + offset_j;
        const bool swapped = (vertex_j[m_dimension] < vertex_i[m_dimension]);
        if (swapped) { swap_vertices(vertex_i, vertex_j); }
        return swapped;
    }

    /**
     * @brief Assuming vertices `0` through `i - 1` are sorted in increasing
     *        order of objective value, move vertex `i` into sorted position.
     *
     * This method performs one step of the insertion sort algorithm.
     */
    constexpr void insert_vertex(DZNL_CONST INDEX_T &i) noexcept {
        DZNL_CONST INDEX_T ZERO = zero<INDEX_T>();
        for (INDEX_T j = i; ZERO < j;) {
            DZNL_CONST INDEX_T k = j;
            --j;
            if (!order_vertices(j, k)) { break; }
        }
    }

private: // ================================================= SIMPLEX GENERATION

    constexpr void copy_coordinates(
        DZNL_CONST ACCESSOR_T &dst, DZNL_CONST ACCESSOR_T &src
    ) noexcept {
        for (INDEX_T i = zero<INDEX_T>(); i < m_dimension; ++i) {
            dst[i] = src[i];
        }
    }

    constexpr Tuple<bool, bool> try_coordinate_step(
        DZNL_CONST ACCESSOR_T &dst,
        DZNL_CONST ACCESSOR_T &src,
        DZNL_CONST INDEX_T &i,
        DZNL_CONST REAL_T &step_length,
        bool forward
    ) noexcept {
        copy_coordinates(dst, src);
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
        DZNL_CONST REAL_T HALF = inv(TWO);
        while (true) {
            const auto [forward_change, forward_success] =
                try_coordinate_step(dst, src, i, step_length, true);
            if (forward_success) { return true; }
            const auto [backward_change, backward_success] =
                try_coordinate_step(dst, src, i, step_length, false);
            if (backward_success) { return true; }
            if (!(forward_change || backward_change)) { return false; }
            step_length *= HALF;
        }
    }

    constexpr bool
    generate_initial_simplex(DZNL_CONST REAL_T &initial_step_length) noexcept {
        for (INDEX_T i = zero<INDEX_T>(); i < m_dimension;) {
            DZNL_CONST INDEX_T coordinate_index = i;
            ++i;
            DZNL_CONST INDEX_T offset_i = vertex_offset(i);
            DZNL_CONST ACCESSOR_T vertex_i = m_workspace + offset_i;
            const bool success = generate_initial_vertex(
                vertex_i, m_workspace, coordinate_index, initial_step_length
            );
            if (!success) { return false; }
            insert_vertex(i);
        }
        return true;
    }

public: // =========================================================== ACCESSORS

    constexpr DZNL_CONST ACCESSOR_T &current_point() const noexcept {
        return m_workspace;
    }

    constexpr DZNL_CONST REAL_T &current_objective_value() const noexcept {
        return m_workspace[m_dimension];
    }

    constexpr bool has_terminated() const noexcept { return m_has_terminated; }

public: // =====================================================================

    static constexpr INDEX_T workspace_size(DZNL_CONST INDEX_T &dimension
    ) noexcept {
        INDEX_T dimension_plus_one = dimension;
        ++dimension_plus_one;
        DZNL_CONST INDEX_T dimension_plus_one_squared =
            dimension_plus_one * dimension_plus_one;
        DZNL_CONST INDEX_T double_dimension = dimension + dimension;
        DZNL_CONST INDEX_T triple_dimension = double_dimension + dimension;
        return dimension_plus_one_squared + triple_dimension;
    }

public: // ========================================================= CONSTRUCTOR

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

        // Ensure that `dimension` is positive.
        DZNL_CONST INDEX_T ZERO = zero<INDEX_T>();
        if (!(ZERO < m_dimension)) {
            m_has_terminated = true;
            return;
        }

        // Copy initial point into beginning of workspace.
        copy_coordinates(m_workspace, initial_point);

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
        if (!generate_initial_simplex(initial_step_length)) {
            m_has_terminated = true;
            return;
        }
    }

private: // ====================================================================

    constexpr void compute_centroid(DZNL_CONST ACCESSOR_T &centroid) noexcept {
        DZNL_CONST REAL_T ZERO = zero<REAL_T>();
        DZNL_CONST REAL_T ONE = one<REAL_T>();
        for (INDEX_T i = zero<INDEX_T>(); i < m_dimension; ++i) {
            centroid[i] = ZERO;
        }
        REAL_T denominator = zero<REAL_T>();
        for (INDEX_T i = zero<INDEX_T>(); i < m_dimension; ++i) {
            INDEX_T current_offset = vertex_offset(i);
            ACCESSOR_T current_vertex = m_workspace + current_offset;
            for (INDEX_T j = zero<INDEX_T>(); j < m_dimension; ++j) {
                centroid[j] += current_vertex[j];
            }
            denominator += ONE;
        }
        for (INDEX_T i = zero<INDEX_T>(); i < m_dimension; ++i) {
            centroid[i] /= denominator;
        }
    }

    constexpr void reflect(
        DZNL_CONST ACCESSOR_T &dst,
        DZNL_CONST ACCESSOR_T &x,
        DZNL_CONST ACCESSOR_T &y
    ) noexcept {
        for (INDEX_T i = zero<INDEX_T>(); i < m_dimension; ++i) {
            DZNL_CONST REAL_T twice_y = twice(y[i]);
            DZNL_CONST REAL_T reflection = twice_y - x[i];
            dst[i] = reflection;
        }
    }

public: // =====================================================================

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
            compute_centroid(centroid);

            // Compute reflection of worst vertex through centroid.
            INDEX_T reflected_offset = centroid_offset + m_dimension;
            ACCESSOR_T reflected_point = m_workspace + reflected_offset;
            reflect(reflected_point, worst_vertex, centroid);

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
                        ACCESSOR_T expanded_point =
                            m_workspace + expanded_offset;
                        reflect(expanded_point, centroid, reflected_point);

                        // Replace worst vertex with whichever is better
                        // between the reflected and expanded points.
                        if (m_constraint_function(expanded_point)) {
                            DZNL_CONST REAL_T expanded_value =
                                m_objective_function(expanded_point);
                            if (expanded_value < reflected_value) {
                                copy_coordinates(worst_vertex, expanded_point);
                                worst_vertex[m_dimension] = expanded_value;
                                insert_vertex(m_dimension);
                                return;
                            }
                        }
                        copy_coordinates(worst_vertex, reflected_point);
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
                        copy_coordinates(worst_vertex, reflected_point);
                        worst_vertex[m_dimension] = reflected_value;
                        insert_vertex(m_dimension);
                        return;
                    }
                }
            }

            // At this point, the reflected point is either infeasible or worse
            // than the second-worst vertex. If we accepted it, it would simply
            // be the worst vertex again, so we need to contract or shrink.

            DZNL_CONST REAL_T ONE = one<REAL_T>();
            DZNL_CONST REAL_T TWO = ONE + ONE;
            DZNL_CONST REAL_T HALF = inv(TWO);

            if ((!reflected_feasible) || (threshold_value < worst_value)) {
                for (INDEX_T i = zero<INDEX_T>(); i < m_dimension; ++i) {
                    reflected_point[i] += centroid[i];
                    reflected_point[i] *= HALF;
                }
                if (m_constraint_function(reflected_point)) {
                    DZNL_CONST REAL_T contracted_value =
                        m_objective_function(reflected_point);
                    if (contracted_value < threshold_value) {
                        copy_coordinates(worst_vertex, reflected_point);
                        worst_vertex[m_dimension] = contracted_value;
                        insert_vertex(m_dimension);
                        return;
                    }
                }
            }

            for (INDEX_T i = zero<INDEX_T>(); i < m_dimension; ++i) {
                centroid[i] += worst_vertex[i];
                centroid[i] *= HALF;
            }
            if (m_constraint_function(centroid)) {
                DZNL_CONST REAL_T contracted_value =
                    m_objective_function(centroid);
                if (contracted_value < worst_value) {
                    copy_coordinates(worst_vertex, centroid);
                    worst_vertex[m_dimension] = contracted_value;
                    insert_vertex(m_dimension);
                    return;
                }
            }

            bool made_change = false;
            for (INDEX_T i = zero<INDEX_T>(); i < m_dimension;) {
                ++i;
                INDEX_T offset_i = vertex_offset(i);
                ACCESSOR_T vertex_i = m_workspace + offset_i;
                for (INDEX_T j = zero<INDEX_T>(); j < m_dimension; ++j) {
                    DZNL_CONST REAL_T old = vertex_i[j];
                    vertex_i[j] += m_workspace[j];
                    vertex_i[j] *= HALF;
                    if (!(vertex_i[j] == old)) { made_change = true; }
                }
                if (!m_constraint_function(vertex_i)) {
                    m_has_terminated = true;
                    return;
                }
                DZNL_CONST REAL_T objective_i = m_objective_function(vertex_i);
                vertex_i[m_dimension] = objective_i;
            }
            if (!made_change) {
                m_has_terminated = true;
                return;
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
