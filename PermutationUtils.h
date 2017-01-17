#ifndef DZNL_PERMUTATION_UTILS_H
#define DZNL_PERMUTATION_UTILS_H

#include <algorithm>
#include <vector>
#include <set>
#include <stdexcept>

namespace dznl {

    template<typename T>
    bool is_invariant_permutation(const std::vector<T> &items,
                                  const std::vector<size_t> &indices) {
        if (items.size() != indices.size()) {
            throw std::invalid_argument(
                    "dznl::is_invariant_permutation received "
                            "items and indices of different sizes");
        }
        const size_t n = items.size();
        for (size_t i = 0; i < n; ++i) {
            if (items[i] != items[indices[i]]) {
                return false;
            }
        }
        return true;
    }

    template<typename T>
    std::vector<std::vector<size_t>>
    invariant_permutations(const std::vector<T> &items) {
        const size_t n = items.size();
        std::vector<std::vector<size_t>> inv_perms;
        std::vector<size_t> indices(n);
        for (size_t i = 0; i < n; ++i) {
            indices[i] = i;
        }
        do {
            if (is_invariant_permutation(items, indices)) {
                inv_perms.push_back(indices);
            }
        } while (std::next_permutation(indices.begin(), indices.end()));
        return inv_perms;
    }

} // namespace dznl

#endif // DZNL_PERMUTATION_UTILS_H
