#ifndef DZNL_MPFR_QUADRATIC_LINE_SEARCHER_HPP_INCLUDED
#define DZNL_MPFR_QUADRATIC_LINE_SEARCHER_HPP_INCLUDED

// C++ standard library headers
#include <cstddef>    // for std::size_t
#include <functional> // for std::function
#include <stdexcept>  // for std::invalid_argument

// GNU MPFR multiprecision library headers
#include <mpfr.h>

// Project-specific headers
#include "MPFRVector.hpp"

namespace dznl {

    class MPFRQuadraticLineSearcher {
    private: // ========================================== INTERNAL TYPE ALIASES
        typedef std::function<void(mpfr_t, mpfr_t *, mpfr_prec_t, mpfr_rnd_t)>
                objective_function_t;

    private: // =============================================== MEMBER VARIABLES
        const std::size_t n;
        const objective_function_t f;
        const mpfr_prec_t precision;
        const mpfr_rnd_t rounding_mode;

        const MPFRVector &x0;
        MPFRVector xt;
        const MPFRVector &dx;

        const mpfr_t &f0;

        mpfr_t &best_objective_value;
        mpfr_t &best_step_size;

        mpfr_t f1;
        mpfr_t f2;
        mpfr_t step_size;
        mpfr_t next_step_size;
        mpfr_t numer;
        mpfr_t denom;

    public: // ===================================================== CONSTRUCTOR
        explicit MPFRQuadraticLineSearcher(
                mpfr_t &final_objective_value,
                mpfr_t &final_step_size,
                const objective_function_t &objective_function,
                const MPFRVector &initial_point,
                const mpfr_t &initial_objective_value,
                const MPFRVector &step_direction,
                mpfr_prec_t prec,
                mpfr_rnd_t rnd)
                : n(initial_point.size()),
                  f(objective_function),
                  precision(prec),
                  rounding_mode(rnd),
                  x0(initial_point),
                  xt(n, precision),
                  dx(step_direction),
                  f0(initial_objective_value),
                  best_objective_value(final_objective_value),
                  best_step_size(final_step_size) {
            if (initial_point.size() != step_direction.size()) {
                throw std::invalid_argument(
                        "dznl::QuadraticLineSearcher constructor received "
                        "initial point and step direction vectors of "
                        "different sizes");
            }
            mpfr_init2(f1, precision);
            mpfr_init2(f2, precision);
            mpfr_init2(step_size, precision);
            mpfr_init2(next_step_size, precision);
            mpfr_init2(numer, precision);
            mpfr_init2(denom, precision);
            mpfr_set(best_objective_value, initial_objective_value,
                     rounding_mode);
            mpfr_set_zero(best_step_size, 0);
        }

    public: // =========================================================== BIG 3
        MPFRQuadraticLineSearcher(const MPFRQuadraticLineSearcher &) = delete;

        MPFRQuadraticLineSearcher &
        operator=(const MPFRQuadraticLineSearcher &) = delete;

        ~MPFRQuadraticLineSearcher() {
            mpfr_clear(f1);
            mpfr_clear(f2);
            mpfr_clear(step_size);
            mpfr_clear(next_step_size);
            mpfr_clear(numer);
            mpfr_clear(denom);
        }

    private: // ===================================== LINE SEARCH HELPER METHODS
        void evaluate_objective_function(mpfr_t objective_value,
                                         mpfr_t t,
                                         bool *changed = nullptr) {
            const mpfr_rnd_t rnd = rounding_mode;
            xt.set_axpy(t, dx, x0, rnd);
            if (x0 == xt) {
                if (changed != nullptr) { *changed = false; }
                mpfr_set(objective_value, f0, rnd);
                return;
            } else {
                if (changed != nullptr) { *changed = true; }
            }
            f(objective_value, xt.data(), precision, rnd);
            if (mpfr_less_p(objective_value, best_objective_value)) {
                mpfr_set(best_objective_value, objective_value, rnd);
                mpfr_set(best_step_size, t, rnd);
            }
        }

    public: // ============================================= LINE SEARCH METHODS
        void search(mpfr_t initial_step_size, std::size_t max_increases = 4) {
            const mpfr_rnd_t rnd = rounding_mode;
            mpfr_set(step_size, initial_step_size, rnd);
            evaluate_objective_function(f1, step_size);
            if (mpfr_less_p(f1, f0)) {
                std::size_t num_increases = 0;
                while (true) {
                    mpfr_mul_2ui(next_step_size, step_size, 1, rnd);
                    evaluate_objective_function(f2, next_step_size);
                    if (mpfr_greaterequal_p(f2, f1)) {
                        break;
                    } else {
                        mpfr_swap(step_size, next_step_size);
                        mpfr_swap(f1, f2);
                        ++num_increases;
                        if (num_increases >= max_increases) { return; }
                    }
                }
                mpfr_mul_2ui(denom, f1, 1, rnd); // denom = 2*f1
                mpfr_sub(denom, denom, f2, rnd); // denom = 2*f1 - f2
                mpfr_sub(denom, denom, f0, rnd); // denom = 2*f1 - f2 - f0
                mpfr_mul_2ui(numer, f1, 2, rnd); // numer = 4*f1
                mpfr_sub(numer, numer, f2, rnd); // numer = 4*f1 - f2
                mpfr_mul_ui(f1, f0, 3, rnd);     // temporarily store f1' = 3*f0
                mpfr_sub(numer, numer, f1, rnd); // numer = 4*f1 - f2 - 3*f0
                mpfr_div_2ui(next_step_size, step_size, 1, rnd);
                mpfr_mul(next_step_size, next_step_size, numer, rnd);
                mpfr_div(next_step_size, next_step_size, denom, rnd);
                evaluate_objective_function(f2, next_step_size);
            } else {
                while (true) {
                    mpfr_div_2ui(next_step_size, step_size, 1, rnd);
                    bool changed;
                    evaluate_objective_function(f2, next_step_size, &changed);
                    if (!changed) { return; }
                    if (mpfr_less_p(f2, f0)) {
                        break;
                    } else {
                        mpfr_swap(step_size, next_step_size);
                        mpfr_swap(f1, f2);
                    }
                }
                mpfr_mul_2ui(f2, f2, 1, rnd);
                mpfr_sub(denom, f1, f2, rnd);
                mpfr_add(denom, denom, f0, rnd);
                mpfr_mul_2ui(f2, f2, 1, rnd);
                mpfr_sub(numer, f1, f2, rnd);
                mpfr_mul_ui(f1, f0, 3, rnd);
                mpfr_add(numer, numer, f1, rnd);
                mpfr_div_2ui(next_step_size, step_size, 2, rnd);
                mpfr_mul(next_step_size, next_step_size, numer, rnd);
                mpfr_div(next_step_size, next_step_size, denom, rnd);
                evaluate_objective_function(f2, next_step_size);
            }
        }

    }; // class MPFRQuadraticLineSearcher

} // namespace dznl

#endif // DZNL_MPFR_QUADRATIC_LINE_SEARCHER_HPP_INCLUDED
