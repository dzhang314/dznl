#ifndef DZNL_GRADIENT_DESCENT_OPTIMIZER_HPP_INCLUDED
#define DZNL_GRADIENT_DESCENT_OPTIMIZER_HPP_INCLUDED

#include "NumericFunctions.hpp"
#include "Restrict.hpp"

namespace dznl {


template <
    typename REAL_T,
    typename INDEX_T,
    typename OBJECTIVE_FUNCTOR_T,
    typename GRADIENT_FUNCTOR_T,
    typename CONSTRAINT_FUNCTOR_T>
class GradientDescentOptimizer {

    OBJECTIVE_FUNCTOR_T &objective_function;
    GRADIENT_FUNCTOR_T &gradient_function;
    CONSTRAINT_FUNCTOR_T &constraint_function;
    REAL_T *DZNL_RESTRICT workspace;
    REAL_T objective_value;
    REAL_T last_step_length;
    INDEX_T dimension;
    bool has_terminated;

public:

    constexpr const REAL_T *current_point() const noexcept { return workspace; }

    constexpr const REAL_T *current_gradient() const noexcept {
        return workspace + dimension;
    }

    static constexpr INDEX_T workspace_size(const INDEX_T &dimension) noexcept {
        return dimension + dimension + dimension;
    }

    explicit constexpr GradientDescentOptimizer(
        OBJECTIVE_FUNCTOR_T &objective_function,
        GRADIENT_FUNCTOR_T &gradient_function,
        CONSTRAINT_FUNCTOR_T &constraint_function,
        const REAL_T *const DZNL_RESTRICT initial_point,
        const INDEX_T &dimension,
        const REAL_T &inital_step_length,
        REAL_T *const DZNL_RESTRICT workspace,
    )
        : objective_function(objective_function)
        , gradient_function(gradient_function)
        , constraint_function(constraint_function)
        , workspace(workspace)
        , objective_value(zero<REAL_T>())
        , last_step_length(inital_step_length)
        , dimension(dimension)
        , has_terminated(false) {

        // Copy `initial_point` into `workspace`.
        for (INDEX_T i = zero<INDEX_T>(); i < dimension; ++i) {
            workspace[i] = initial_point[i];
        }

        // Call `constraint_function` to check if `initial_point` is feasible.
        if (!constraint_function(workspace)) {
            // If not, immediately terminate iteration
            // by setting `has_terminated` flag.
            has_terminated = true;
            return;
        }

        // Call `objective_function` and `gradient_function` to compute
        // objective value and gradient at constrained `initial_point`.
        objective_value = objective_function(workspace);
        if (is_nan(objective_value)) {
            has_terminated = true;
            return;
        }
        gradient_function(workspace + dimension, workspace);
    }

    void step() noexcept {}


}; // class GradientDescentOptimizer


} // namespace dznl

#endif // DZNL_GRADIENT_DESCENT_OPTIMIZER_HPP_INCLUDED
