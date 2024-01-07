#ifndef DZNL_NELDER_MEAD_OPTIMIZER_HPP_INCLUDED
#define DZNL_NELDER_MEAD_OPTIMIZER_HPP_INCLUDED

#include "FloatingPointProperties.hpp"
#include "Macros.hpp"
#include "NumericFunctions.hpp"
#include "OptimizerUtilities.hpp"
#include "Tuple.hpp"
#include "TypeTraits.hpp"

namespace dznl {


template <typename INDEX_T>
static constexpr INDEX_T nelder_mead_workspace_size(INDEX_T n) noexcept {
    DZNL_CONST INDEX_T two_n = n + n;
    DZNL_CONST INDEX_T three_n = two_n + n;
    ++n;
    DZNL_CONST INDEX_T n_plus_one_squared = n * n;
    return n_plus_one_squared + three_n;
}


/**
 * @brief Nelder-Mead derivative-free minimization algorithm.
 *
 * @tparam REAL_T is the numeric type used to represent the inputs and outputs
 *         of the objective function. `REAL_T` is normally a floating-point
 *         type, such as `float` or `double`.
 *
 * @tparam INDEX_T is the numeric type used to index the coordinates of the
 *         feasible region and the internal workspace array. To solve an
 *         `n`-dimensional optimization problem, `dznl::NelderMeadOptimizer`
 *         uses an internal workspace array of length `(n + 1)^2 + 3n`. Thus,
 *         `INDEX_T` must be able to represent the integers `0` through
 *         `(n + 1)^2 + 3n - 1`, inclusive. `INDEX_T` is normally an integral
 *         type, such as `int`, `unsigned int`, or `std::size_t`.
 *
 * @tparam OBJECTIVE_FUNCTOR_T is the type used to evaluate the objective
 *         function. It can either be a plain function type
 *         `REAL_T (OBJECTIVE_FUNCTOR_T)(const REAL_T *);` or a user-defined
 *         type that overloads `operator()` with a compatible interface.
 *
 * @tparam CONSTRAINT_FUNCTOR_T is the type of the object used to evaluate
 *         constraints. It can either be a plain function type
 *         `bool (CONSTRAINT_FUNCTOR_T)(REAL_T *);` or a user-defined type
 *         that overloads `operator()` with a compatible interface.
 *
 * @tparam ACCESSOR_T is the type of the object used to access the internal
 *         workspace array. It can either be a plain pointer type `REAL_T *`
 *         or a user-defined type that overloads `operator[]` with a
 */
template <
    typename OBJECTIVE_FUNCTOR_T,
    typename CONSTRAINT_FUNCTOR_T,
    typename REAL_T,
    typename INDEX_T,
    typename ACCESSOR_T>
class NelderMeadOptimizer {

private: // =================================================== MEMBER VARIABLES

    internal::IterativeOptimizerBase<
        OBJECTIVE_FUNCTOR_T,
        CONSTRAINT_FUNCTOR_T,
        REAL_T,
        INDEX_T,
        ACCESSOR_T>
        m_base;
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
        ++vertex_size;
        return vertex_size * i;
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
        if (vertex_j[m_dimension] < vertex_i[m_dimension]) {
            internal::swap_arrays(vertex_i, vertex_j, m_dimension, true);
            return true;
        } else {
            return false;
        }
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

    /**
     * @brief Sort the vertices of the active vertex in increasing order of
     *        objective value using the insertion sort algorithm.
     */
    constexpr void sort_active_simplex() noexcept {
        for (INDEX_T i = zero<INDEX_T>(); i < m_dimension;) {
            ++i;
            insert_vertex(i);
        }
    }

private: // =============================================== SIMPLEX MANIPULATION

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
            using internal::StepResult;
            internal::copy_array(dst, src, m_dimension);
            const auto forward_result = m_base.try_coordinate_step(
                dst[m_dimension], dst, i, step_length, true
            );
            if (forward_result == StepResult::FEASIBLE) { return true; }
            internal::copy_array(dst, src, m_dimension);
            const auto backward_result = m_base.try_coordinate_step(
                dst[m_dimension], dst, i, step_length, false
            );
            if (backward_result == StepResult::FEASIBLE) { return true; }
            if ((forward_result == StepResult::NO_CHANGE) &&
                (backward_result == StepResult::NO_CHANGE)) {
                return false;
            }
            step_length *= HALF;
        }
    }

    constexpr bool
    generate_initial_simplex(DZNL_CONST REAL_T &initial_step_length) noexcept {
        for (INDEX_T i = zero<INDEX_T>(); i < m_dimension;) {
            DZNL_CONST INDEX_T coordinate_index = i;
            ++i;
            DZNL_CONST INDEX_T offset = vertex_offset(i);
            DZNL_CONST ACCESSOR_T vertex = m_workspace + offset;
            const bool success = generate_initial_vertex(
                vertex, m_workspace, coordinate_index, initial_step_length
            );
            if (!success) { return false; }
        }
        sort_active_simplex();
        return true;
    }

    constexpr void compute_simplex_centroid(DZNL_CONST ACCESSOR_T &dst
    ) noexcept {
        DZNL_CONST REAL_T ZERO = zero<REAL_T>();
        DZNL_CONST REAL_T ONE = one<REAL_T>();
        for (INDEX_T i = zero<INDEX_T>(); i < m_dimension; ++i) {
            dst[i] = ZERO;
        }
        REAL_T denominator = zero<REAL_T>();
        for (INDEX_T i = zero<INDEX_T>(); i < m_dimension; ++i) {
            DZNL_CONST INDEX_T offset = vertex_offset(i);
            DZNL_CONST ACCESSOR_T vertex = m_workspace + offset;
            for (INDEX_T j = zero<INDEX_T>(); j < m_dimension; ++j) {
                dst[j] += vertex[j];
            }
            denominator += ONE;
        }
        for (INDEX_T i = zero<INDEX_T>(); i < m_dimension; ++i) {
            dst[i] /= denominator;
        }
    }

    constexpr bool shrink_simplex() noexcept {
        DZNL_CONST REAL_T ONE = one<REAL_T>();
        DZNL_CONST REAL_T TWO = ONE + ONE;
        DZNL_CONST REAL_T HALF = inv(TWO);
        bool made_change = false;
        for (INDEX_T i = zero<INDEX_T>(); i < m_dimension;) {
            ++i;
            DZNL_CONST INDEX_T offset = vertex_offset(i);
            DZNL_CONST ACCESSOR_T vertex = m_workspace + offset;
            for (INDEX_T j = zero<INDEX_T>(); j < m_dimension; ++j) {
                DZNL_CONST REAL_T old_coordinate = vertex[j];
                vertex[j] += m_workspace[j];
                vertex[j] *= HALF;
                if (!(vertex[j] == old_coordinate)) { made_change = true; }
            }
            const bool is_feasible =
                m_base.constrain_and_evaluate(vertex[m_dimension], vertex);
            if (!is_feasible) { return false; }
        }
        return made_change;
    }

public: // ========================================================= CONSTRUCTOR

    explicit constexpr NelderMeadOptimizer(
        OBJECTIVE_FUNCTOR_T *objective_function,
        CONSTRAINT_FUNCTOR_T *constraint_function,
        DZNL_CONST ACCESSOR_T &workspace,
        DZNL_CONST INDEX_T &dimension,
        DZNL_CONST REAL_T &initial_step_length
    ) noexcept
        : m_base(objective_function, constraint_function)
        , m_workspace(workspace)
        , m_dimension(dimension)
        , m_has_terminated(false) {

        // Ensure `dimension` is positive.
        DZNL_CONST INDEX_T ZERO = zero<INDEX_T>();
        if (!(ZERO < m_dimension)) {
            m_has_terminated = true;
            return;
        }

        // Call constraint function to check feasibility of initial point.
        // If so, compute objective value at constrained initial point.
        const bool is_feasible = m_base.constrain_and_evaluate(
            m_workspace[m_dimension], m_workspace
        );
        if (!is_feasible) {
            m_has_terminated = true;
            return;
        }

        // Generate active simplex. The first (dimension + 1)^2 workspace
        // entries will contain vertices of the active simplex, each followed
        // immediately by its objective value.
        if (!generate_initial_simplex(initial_step_length)) {
            m_has_terminated = true;
            return;
        }
    }

private: // ====================================== OPTIMIZATION HELPER FUNCTIONS

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

public: // ================================================= OPTIMIZER INTERFACE

    constexpr DZNL_CONST ACCESSOR_T &get_current_point() const noexcept {
        return m_workspace;
    }

    constexpr DZNL_CONST REAL_T &get_current_objective_value() const noexcept {
        return m_workspace[m_dimension];
    }

    constexpr bool step() noexcept {

        if (m_has_terminated) { return false; }

        // Vertices of the active simplex are stored in increasing
        // order by objective value, so the worst vertex is last.
        INDEX_T worst_offset = vertex_offset(m_dimension);
        ACCESSOR_T worst_vertex = m_workspace + worst_offset;
        DZNL_CONST REAL_T worst_value = worst_vertex[m_dimension];

        // Compute centroid of all vertices except the worst.
        INDEX_T centroid_offset = worst_offset + m_dimension;
        ++centroid_offset;
        ACCESSOR_T centroid = m_workspace + centroid_offset;
        compute_simplex_centroid(centroid);

        // Compute reflection of worst vertex through centroid.
        INDEX_T reflected_offset = centroid_offset + m_dimension;
        ACCESSOR_T reflected_point = m_workspace + reflected_offset;
        reflect(reflected_point, worst_vertex, centroid);

        // Constrain reflected point and compute its objective value.
        REAL_T reflected_value = worst_value;
        const bool reflected_is_feasible =
            m_base.constrain_and_evaluate(reflected_value, reflected_point);

        if (reflected_is_feasible) {
            // If the reflected point is feasible and better than
            // the previous best vertex, try expanding the simplex.
            if (reflected_value < m_workspace[m_dimension]) {
                INDEX_T expanded_offset = reflected_offset + m_dimension;
                ACCESSOR_T expanded_point = m_workspace + expanded_offset;
                reflect(expanded_point, centroid, reflected_point);

                // Replace worst vertex with whichever is better
                // between the reflected and expanded points.
                const bool expanded_is_better = m_base.replace_if_better(
                    worst_vertex[m_dimension], reflected_value, expanded_point
                );
                internal::copy_array(
                    worst_vertex,
                    expanded_is_better ? expanded_point : reflected_point,
                    m_dimension
                );
                if (!expanded_is_better) {
                    worst_vertex[m_dimension] = reflected_value;
                }
                insert_vertex(m_dimension);
                return true;
            }

            // Otherwise, if the reflected point is feasible and better
            // than the second-worst vertex, accept the reflected point
            // without trying expansion.
            --worst_offset;
            DZNL_CONST REAL_T second_worst_value = m_workspace[worst_offset];
            if (reflected_value < second_worst_value) {
                internal::copy_array(
                    worst_vertex, reflected_point, m_dimension
                );
                worst_vertex[m_dimension] = reflected_value;
                insert_vertex(m_dimension);
                return true;
            }
        }

        // At this point, the reflected point is either infeasible or worse
        // than the second-worst vertex. If we accepted it, it would simply
        // be the worst vertex again, so we need to contract or shrink.

        DZNL_CONST REAL_T ONE = one<REAL_T>();
        DZNL_CONST REAL_T TWO = ONE + ONE;
        DZNL_CONST REAL_T HALF = inv(TWO);

        if ((!reflected_is_feasible) || (reflected_value < worst_value)) {
            for (INDEX_T i = zero<INDEX_T>(); i < m_dimension; ++i) {
                reflected_point[i] += centroid[i];
                reflected_point[i] *= HALF;
            }
            const bool contracted_is_better = m_base.replace_if_better(
                worst_vertex[m_dimension], reflected_value, reflected_point
            );
            if (contracted_is_better) {
                internal::copy_array(
                    worst_vertex, reflected_point, m_dimension
                );
                insert_vertex(m_dimension);
                return true;
            }
        }

        for (INDEX_T i = zero<INDEX_T>(); i < m_dimension; ++i) {
            centroid[i] += worst_vertex[i];
            centroid[i] *= HALF;
        }
        const bool contracted_is_better =
            m_base.replace_if_better(worst_vertex[m_dimension], centroid);
        if (contracted_is_better) {
            internal::copy_array(worst_vertex, centroid, m_dimension);
            insert_vertex(m_dimension);
            return true;
        }

        if (!shrink_simplex()) {
            m_has_terminated = true;
            return false;
        }
        sort_active_simplex();
        return true;
    }

}; // class NelderMeadOptimizer


template <
    typename OBJECTIVE_FUNCTOR_T,
    typename ACCESSOR_T,
    typename INDEX_T,
    typename REAL_T>
constexpr NelderMeadOptimizer<
    OBJECTIVE_FUNCTOR_T,
    void,
    REAL_T,
    INDEX_T,
    ACCESSOR_T>
make_nelder_mead_optimizer(
    OBJECTIVE_FUNCTOR_T *objective_function,
    ACCESSOR_T workspace,
    INDEX_T dimension,
    REAL_T initial_step_length
) noexcept {
    return NelderMeadOptimizer<
        OBJECTIVE_FUNCTOR_T,
        void,
        REAL_T,
        INDEX_T,
        ACCESSOR_T>(
        objective_function, nullptr, workspace, dimension, initial_step_length
    );
}


template <
    typename OBJECTIVE_FUNCTOR_T,
    typename CONSTRAINT_FUNCTOR_T,
    typename ACCESSOR_T,
    typename INDEX_T,
    typename REAL_T>
constexpr NelderMeadOptimizer<
    OBJECTIVE_FUNCTOR_T,
    CONSTRAINT_FUNCTOR_T,
    REAL_T,
    INDEX_T,
    ACCESSOR_T>
make_nelder_mead_optimizer(
    OBJECTIVE_FUNCTOR_T *objective_function,
    CONSTRAINT_FUNCTOR_T *constraint_function,
    ACCESSOR_T workspace,
    INDEX_T dimension,
    REAL_T initial_step_length
) noexcept {
    return NelderMeadOptimizer<
        OBJECTIVE_FUNCTOR_T,
        CONSTRAINT_FUNCTOR_T,
        REAL_T,
        INDEX_T,
        ACCESSOR_T>(
        objective_function,
        constraint_function,
        workspace,
        dimension,
        initial_step_length
    );
}


} // namespace dznl

#endif // DZNL_NELDER_MEAD_OPTIMIZER_HPP_INCLUDED
