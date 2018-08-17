#ifndef DZNL_MPFR_MATRIX_HPP_INCLUDED
#define DZNL_MPFR_MATRIX_HPP_INCLUDED

// C++ standard library headers
#include <cstddef> // for std::size_t
#include <vector>

// GNU MPFR multiprecision library headers
#include <mpfr.h>

namespace dznl {

    class MPFRMatrix {

    private: // =============================================== MEMBER VARIABLES

        std::size_t n;
        std::vector<mpfr_t> entries;
        mpfr_prec_t precision;

    public: // ===================================================== CONSTRUCTOR

        MPFRMatrix() = delete;

        explicit MPFRMatrix(std::size_t n, mpfr_prec_t prec) :
                n(n), entries(n * n), precision(prec) {
            for (mpfr_t &x : entries) { mpfr_init2(x, precision); }
        }

    public: // =========================================================== BIG 3

        MPFRMatrix(const MPFRMatrix &) = delete;

        MPFRMatrix &operator=(const MPFRMatrix &) = delete;

        ~MPFRMatrix() {
            for (mpfr_t &x : entries) { mpfr_clear(x); }
        }

    public: // ============================================== INDEXING OPERATORS

        mpfr_t *data() { return entries.data(); }

        const mpfr_t *data() const { return entries.data(); }

    public: // =================================================================

        void set_identity_matrix() {
            for (std::size_t i = 0, k = 0; i < n; ++i) {
                for (std::size_t j = 0; j < n; ++j, ++k) {
                    mpfr_set_si(entries[k], static_cast<long>(i == j),
                                MPFR_RNDN);
                }
            }
        }

    }; // class MPFRMatrix

} // namespace dznl

#endif // DZNL_MPFR_MATRIX_HPP_INCLUDED
