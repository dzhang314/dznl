#ifndef DZNL_OPTIMIZER_UTILITIES_HPP_INCLUDED
#define DZNL_OPTIMIZER_UTILITIES_HPP_INCLUDED

#include "FloatingPointProperties.hpp"
#include "Macros.hpp"
#include "NumericFunctions.hpp"
#include "TypeTraits.hpp"

namespace dznl::internal {


enum class StepResult : char { NO_CHANGE, INFEASIBLE, FEASIBLE };


template <
    typename OBJECTIVE_FUNCTOR_T,
    typename CONSTRAINT_FUNCTOR_T,
    typename REAL_T,
    typename INDEX_T,
    typename ACCESSOR_T>
class IterativeOptimizerBase {

private: // =================================================== MEMBER VARIABLES

    OBJECTIVE_FUNCTOR_T *const m_objective_function;
    CONSTRAINT_FUNCTOR_T *const m_constraint_function;

    IterativeOptimizerBase(const IterativeOptimizerBase &) = delete;
    IterativeOptimizerBase(IterativeOptimizerBase &&) = delete;
    IterativeOptimizerBase &operator=(const IterativeOptimizerBase &) = delete;
    IterativeOptimizerBase &operator=(IterativeOptimizerBase &&) = delete;

public: // ========================================================= CONSTRUCTOR

    explicit constexpr IterativeOptimizerBase(
        OBJECTIVE_FUNCTOR_T *objective_function,
        CONSTRAINT_FUNCTOR_T *constraint_function
    ) noexcept
        : m_objective_function(objective_function)
        , m_constraint_function(constraint_function) {}

public: // ========================================================== EVALUATION

    constexpr bool constrain_and_evaluate(
        REAL_T &dst, DZNL_CONST ACCESSOR_T &point
    ) const noexcept {
        if constexpr (!is_void<CONSTRAINT_FUNCTOR_T>) {
            if (!(*m_constraint_function)(point)) { return false; }
        }
        DZNL_CONST REAL_T objective_value = (*m_objective_function)(point);
        if (!is_nan(objective_value)) {
            dst = objective_value;
            return true;
        } else {
            return false;
        }
    }

    constexpr bool replace_if_better(
        REAL_T &previous_objective_value, DZNL_CONST ACCESSOR_T &point
    ) const noexcept {
        if constexpr (!is_void<CONSTRAINT_FUNCTOR_T>) {
            if (!(*m_constraint_function)(point)) { return false; }
        }
        DZNL_CONST REAL_T new_objective_value = (*m_objective_function)(point);
        // No NaN check is needed here, since this comparison
        // only succeeds if `new_objective_value` is not NaN.
        if (new_objective_value < previous_objective_value) {
            previous_objective_value = new_objective_value;
            return true;
        } else {
            return false;
        }
    }

    constexpr bool replace_if_better(
        REAL_T &dst,
        DZNL_CONST REAL_T &previous_objective_value,
        DZNL_CONST ACCESSOR_T &point
    ) const noexcept {
        if constexpr (!is_void<CONSTRAINT_FUNCTOR_T>) {
            if (!(*m_constraint_function)(point)) { return false; }
        }
        DZNL_CONST REAL_T new_objective_value = (*m_objective_function)(point);
        // No NaN check is needed here, since this comparison
        // only succeeds if `new_objective_value` is not NaN.
        if (new_objective_value < previous_objective_value) {
            dst = new_objective_value;
            return true;
        } else {
            return false;
        }
    }

public: // ============================================================ STEPPING

    constexpr StepResult try_coordinate_step(
        REAL_T &dst,
        DZNL_CONST ACCESSOR_T &point,
        DZNL_CONST INDEX_T &i,
        DZNL_CONST REAL_T &step_length,
        bool forward
    ) noexcept {
        DZNL_CONST REAL_T x = point[i];
        DZNL_CONST REAL_T x_prime = forward ? x + step_length : x - step_length;
        if (x == x_prime) { return StepResult::NO_CHANGE; }
        point[i] = x_prime;
        const bool is_feasible = constrain_and_evaluate(dst, point);
        return is_feasible ? StepResult::FEASIBLE : StepResult::INFEASIBLE;
    }

}; // class IterativeOptimizerBase


template <typename ACCESSOR_T, typename INDEX_T>
constexpr void copy_array(
    DZNL_CONST ACCESSOR_T &dst,
    DZNL_CONST ACCESSOR_T &src,
    DZNL_CONST INDEX_T &n,
    bool copy_one_extra = false
) noexcept {
    INDEX_T i = zero<INDEX_T>();
    for (; i < n; ++i) { dst[i] = src[i]; }
    if (copy_one_extra) { dst[i] = src[i]; }
}


template <typename ACCESSOR_T, typename INDEX_T>
constexpr void swap_arrays(
    DZNL_CONST ACCESSOR_T &x,
    DZNL_CONST ACCESSOR_T &y,
    DZNL_CONST INDEX_T &n,
    bool swap_one_extra = false
) noexcept {
    INDEX_T i = zero<INDEX_T>();
    for (; i < n; ++i) {
        DZNL_CONST auto temp = x[i];
        x[i] = y[i];
        y[i] = temp;
    }
    if (swap_one_extra) {
        DZNL_CONST auto temp = x[i];
        x[i] = y[i];
        y[i] = temp;
    }
}


} // namespace dznl::internal

#endif // DZNL_OPTIMIZER_UTILITIES_HPP_INCLUDED
