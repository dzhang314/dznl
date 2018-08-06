#ifndef DZNL_AMOEBA_OPTIMIZER_HPP_INCLUDED
#define DZNL_AMOEBA_OPTIMIZER_HPP_INCLUDED

// C++ standard library headers
#include <algorithm> // for std::sort
#include <cstddef> // for std::size_t
#include <functional> // for std::function
#include <utility> // for std::pair
#include <vector>

namespace dznl {

    template <typename T>
    class AmoebaOptimizer {

    private: // =============================================== MEMBER VARIABLES

        const std::size_t n;
        std::function<T(const T *)> f;
        std::vector<std::pair<T, std::vector<T>>> x;

    public: // ===================================================== CONSTRUCTOR

        AmoebaOptimizer(
                const T *initial_point,
                std::size_t num_dimensions,
                T initial_step_size,
                std::function<T(const T *)> objective_function)
                : n(num_dimensions), f(std::move(objective_function)) {
            std::vector<T> y(n);
            for (std::size_t i = 0; i < n + 1; ++i) {
                for (std::size_t j = 0; j < n; ++j) {
                    y[j] = (i == j) ? initial_point[j] + initial_step_size
                                    : initial_point[j];
                }
                x.emplace_back(f(y.data()), y);
            }
        }

    private: // ======================================================= MUTATORS

        void sort() {
            std::sort(x.begin(), x.end(), [](
                    const std::pair<T, std::vector<T>> &p,
                    const std::pair<T, std::vector<T>> &q) {
                return p.first < q.first;
            });
        }

    public: // ======================================================= ACCESSORS

        T current_minimum(T *current_point) {
            sort();
            for (std::size_t i = 0; i < n; ++i) {
                current_point[i] = x[0].second[i];
            }
            return x[0].first;
        }

    private: // ======================================= GEOMETRIC HELPER METHODS

        std::vector<T> compute_centroid() const {
            std::vector<T> centroid(n, 0.0);
            for (std::size_t i = 0; i < n; ++i) {
                for (std::size_t j = 0; j < n; ++j) {
                    centroid[j] += x[i].second[j];
                }
            }
            for (std::size_t i = 0; i < n; ++i) { centroid[i] /= n; }
            return centroid;
        }

        std::vector<T> compute_reflection(
                const std::vector<T> &p,
                const std::vector<T> &q) const {
            std::vector<T> reflected_point(n);
            for (std::size_t i = 0; i < n; ++i) {
                reflected_point[i] = 2 * q[i] - p[i];
            }
            return reflected_point;
        }

        std::vector<T> compute_midpoint(
                const std::vector<T> &p,
                const std::vector<T> &q) const {
            std::vector<T> midpoint(n);
            for (std::size_t i = 0; i < n; ++i) {
                midpoint[i] = (p[i] + q[i]) / 2;
            }
            return midpoint;
        }

    public: // ============================================ OPTIMIZATION METHODS

        T step() {
            sort();
            const T &best_value = x[0].first;
            const std::vector<T> &best_point = x[0].second;
            const T &second_worst_value = x[n - 1].first;
            T &worst_value = x[n].first;
            std::vector<T> &worst_point = x[n].second;
            const std::vector<T> centroid = compute_centroid();
            const std::vector<T> reflected_point =
                    compute_reflection(worst_point, centroid);
            const T reflected_value = f(reflected_point.data());
            if (best_value <= reflected_value &&
                reflected_value < second_worst_value) {
                worst_value = reflected_value;
                worst_point = reflected_point;
                return best_value;
            } else if (reflected_value < best_value) {
                const std::vector<T> expanded_point =
                        compute_reflection(centroid, reflected_point);
                const T expanded_value = f(expanded_point.data());
                if (expanded_value < reflected_value) {
                    worst_value = expanded_value;
                    worst_point = expanded_point;
                    return expanded_value;
                } else {
                    worst_value = reflected_value;
                    worst_point = reflected_point;
                    return reflected_value;
                }
            } else if (reflected_value >= second_worst_value) {
                const std::vector<T> contracted_point =
                        compute_midpoint(worst_point, centroid);
                const T contracted_value = f(contracted_point.data());
                if (contracted_value < worst_value) {
                    worst_value = contracted_value;
                    worst_point = contracted_point;
                    return (contracted_value < best_value)
                           ? contracted_value : best_value;
                }
            }
            T best_shrunk_value = best_value;
            for (std::size_t i = 1; i < n + 1; ++i) {
                T &current_value = x[i].first;
                std::vector<T> &current_point = x[i].second;
                for (std::size_t j = 0; j < n; ++j) {
                    current_point[j] = (best_point[j] + current_point[j]) / 2;
                }
                current_value = f(current_point.data());
                if (current_value < best_shrunk_value) {
                    best_shrunk_value = current_value;
                }
            }
            return best_shrunk_value;
        }

    }; // class AmoebaOptimizer

} // namespace dznl

#endif // DZNL_AMOEBA_OPTIMIZER_HPP_INCLUDED
