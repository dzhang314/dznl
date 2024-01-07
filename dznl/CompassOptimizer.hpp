#ifndef DZNL_COMPASS_OPTIMIZER_HPP_INCLUDED
#define DZNL_COMPASS_OPTIMIZER_HPP_INCLUDED

#include "Macros.hpp"
#include "OptimizerUtilities.hpp"

namespace dznl {


template <typename INDEX_T>
constexpr INDEX_T compass_workspace_size(INDEX_T n) noexcept {
    return n + n + n;
}


template <
    typename OBJECTIVE_FUNCTOR_T,
    typename CONSTRAINT_FUNCTOR_T,
    typename REAL_T,
    typename INDEX_T,
    typename ACCESSOR_T>
class CompassOptimizer {

    enum class StepDirection : char { NONE, FORWARD, BACKWARD };

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
    INDEX_T m_last_coordinate;
    REAL_T m_current_objective_value;
    REAL_T m_current_step_length;
    StepDirection m_last_direction;
    bool m_has_terminated;

public: // ========================================================= CONSTRUCTOR

    explicit constexpr CompassOptimizer(
        OBJECTIVE_FUNCTOR_T *objective_function,
        CONSTRAINT_FUNCTOR_T *constraint_function,
        DZNL_CONST ACCESSOR_T &workspace,
        DZNL_CONST INDEX_T &dimension,
        DZNL_CONST REAL_T &initial_step_length
    ) noexcept
        : m_base(objective_function, constraint_function)
        , m_workspace(workspace)
        , m_dimension(dimension)
        , m_last_coordinate(dimension)
        , m_current_objective_value(initial_step_length)
        , m_current_step_length(initial_step_length)
        , m_last_direction(StepDirection::NONE)
        , m_has_terminated(false) {

        DZNL_CONST INDEX_T ZERO = zero<INDEX_T>();
        if (!(ZERO < m_dimension)) {
            m_has_terminated = true;
            return;
        }

        const bool is_feasible = m_base.constrain_and_evaluate(
            m_current_objective_value, m_workspace
        );
        if (!is_feasible) {
            m_has_terminated = true;
            return;
        }
    }

public: // ================================================= OPTIMIZER INTERFACE

    constexpr bool step() noexcept {

        if (m_has_terminated) { return false; }

        DZNL_CONST INDEX_T test_offset = m_dimension + m_dimension;
        DZNL_CONST ACCESSOR_T best_point = m_workspace + m_dimension;
        DZNL_CONST ACCESSOR_T test_point = m_workspace + test_offset;

        REAL_T objective_value = m_current_objective_value;
        INDEX_T best_coordinate = zero<INDEX_T>();
        StepDirection best_direction = StepDirection::NONE;
        bool found_change = false;

        for (INDEX_T i = zero<INDEX_T>(); i < m_dimension; ++i) {

            using internal::StepResult;

            internal::copy_array(test_point, m_workspace, m_dimension);
            const StepResult forward_result = m_base.try_coordinate_step(
                objective_value, test_point, i, m_current_step_length, true
            );
            if (forward_result != StepResult::NO_CHANGE) {
                found_change = true;
            }
            if (forward_result == StepResult::FEASIBLE) {
                if (objective_value < m_current_objective_value) {
                    internal::copy_array(best_point, test_point, m_dimension);
                    m_current_objective_value = objective_value;
                    best_coordinate = i;
                    best_direction = StepDirection::FORWARD;
                }
            }

            internal::copy_array(test_point, m_workspace, m_dimension);
            const StepResult backward_result = m_base.try_coordinate_step(
                objective_value, test_point, i, m_current_step_length, false
            );
            if (backward_result != StepResult::NO_CHANGE) {
                found_change = true;
            }
            if (backward_result == StepResult::FEASIBLE) {
                if (objective_value < m_current_objective_value) {
                    internal::copy_array(best_point, test_point, m_dimension);
                    m_current_objective_value = objective_value;
                    best_coordinate = i;
                    best_direction = StepDirection::BACKWARD;
                }
            }
        }

        if (!found_change) {
            m_has_terminated = true;
            return false;
        }

        if (best_direction != StepDirection::NONE) {
            internal::copy_array(m_workspace, best_point, m_dimension);
            if ((best_coordinate == m_last_coordinate) &&
                (best_direction == m_last_direction)) {
                m_current_step_length += m_current_step_length;
            }
            m_last_coordinate = best_coordinate;
            m_last_direction = best_direction;
        } else {
            DZNL_CONST REAL_T ONE = one<REAL_T>();
            DZNL_CONST REAL_T TWO = ONE + ONE;
            DZNL_CONST REAL_T HALF = inv(TWO);
            m_current_step_length *= HALF;
        }
        return true;
    }

}; // class CompassOptimizer


template <
    typename OBJECTIVE_FUNCTOR_T,
    typename ACCESSOR_T,
    typename INDEX_T,
    typename REAL_T>
constexpr CompassOptimizer<
    OBJECTIVE_FUNCTOR_T,
    void,
    REAL_T,
    INDEX_T,
    ACCESSOR_T>
make_compass_optimizer(
    OBJECTIVE_FUNCTOR_T *objective_function,
    ACCESSOR_T workspace,
    INDEX_T dimension,
    REAL_T initial_step_length
) noexcept {
    return CompassOptimizer<
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
constexpr CompassOptimizer<
    OBJECTIVE_FUNCTOR_T,
    CONSTRAINT_FUNCTOR_T,
    REAL_T,
    INDEX_T,
    ACCESSOR_T>
make_compass_optimizer(
    OBJECTIVE_FUNCTOR_T *objective_function,
    CONSTRAINT_FUNCTOR_T *constraint_function,
    ACCESSOR_T workspace,
    INDEX_T dimension,
    REAL_T initial_step_length
) noexcept {
    return CompassOptimizer<
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

#endif // DZNL_COMPASS_OPTIMIZER_HPP_INCLUDED
