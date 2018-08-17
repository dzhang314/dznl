#ifndef DZNL_MPFR_VECTOR_HPP_INCLUDED
#define DZNL_MPFR_VECTOR_HPP_INCLUDED

// C++ standard library headers
#include <cstddef> // for std::size_t
#include <stdexcept> // for std::invalid_argument
#include <utility> // for std::swap
#include <vector>

// GNU MPFR multiprecision library headers
#include <mpfr.h>

// DZNL headers
#include "MPFRMatrix.hpp"

namespace dznl {

    class MPFRVector {

    private: // =============================================== MEMBER VARIABLES

        std::size_t size_;
        std::vector<mpfr_t> entries;
        mpfr_prec_t precision;

    public: // ===================================================== CONSTRUCTOR

        MPFRVector() = delete;

        explicit MPFRVector(std::size_t size, mpfr_prec_t prec) :
                size_(size), entries(size), precision(prec) {
            for (mpfr_t &x : entries) { mpfr_init2(x, precision); }
        }

    public: // =========================================================== BIG 3

        explicit MPFRVector(const MPFRVector &rhs) :
                size_(rhs.size_), entries(size_),
                precision(rhs.precision) {
            for (std::size_t i = 0; i < size_; ++i) {
                mpfr_init2(entries[i], precision);
                mpfr_set(entries[i], rhs.entries[i], MPFR_RNDN);
            }
        }

        MPFRVector &operator=(const MPFRVector &rhs) {
            MPFRVector copy(rhs);
            swap(copy); // copy-and-swap idiom
            return *this;
        }

        ~MPFRVector() {
            for (mpfr_t &x : entries) { mpfr_clear(x); }
        }

    public: // ======================================================= ACCESSORS

        std::size_t size() const { return size_; }

    public: // ======================================================== MUTATORS

        void swap(MPFRVector &rhs) noexcept {
            std::swap(size_, rhs.size_);
            entries.swap(rhs.entries);
            std::swap(precision, rhs.precision);
        }

    public: // ============================================== INDEXING OPERATORS

        mpfr_t &operator[](std::size_t i) { return entries[i]; }

        const mpfr_t &operator[](std::size_t i) const { return entries[i]; }

        mpfr_t *data() { return entries.data(); }

        const mpfr_t *data() const { return entries.data(); }

    public: // =================================================================

        // TODO: Should be an error to compare vectors with different sizes.
        // Add an optional assertion to check that size_ == rhs.size_.
        bool operator==(const MPFRVector &rhs) const {
            for (std::size_t i = 0; i < size_; ++i) {
                if (!mpfr_equal_p(entries[i], rhs.entries[i])) {
                    return false;
                }
            }
            return true;
        }

        void set_zero() {
            for (mpfr_t &x : entries) { mpfr_set_zero(x, 0); }
        }

        void scale(mpfr_srcptr coeff, mpfr_rnd_t rnd) {
            for (mpfr_t &x : entries) { mpfr_mul(x, coeff, x, rnd); }
        }

        void norm(mpfr_ptr dst, mpfr_rnd_t rnd) {
            mpfr_sqr(dst, entries[0], rnd);
            for (std::size_t i = 1; i < size_; ++i) {
                mpfr_fma(dst, entries[i], entries[i], dst, rnd);
            }
            mpfr_sqrt(dst, dst, rnd);
        }

        void negate_and_normalize(mpfr_ptr tmp, mpfr_rnd_t rnd) {
            norm(tmp, rnd);
            mpfr_si_div(tmp, -1, tmp, rnd);
            scale(tmp, rnd);
        }

        // TODO: What to do if input MPFRVectors have different sizes?
        void set_add(const MPFRVector &x, const MPFRVector &y,
                     mpfr_rnd_t rnd) {
            for (std::size_t i = 0; i < size_; ++i) {
                mpfr_add(entries[i], x.entries[i], y.entries[i], rnd);
            }
        }

        // TODO: What to do if input MPFRVectors have different sizes?
        void set_sub(const MPFRVector &x, const MPFRVector &y,
                     mpfr_rnd_t rnd) {
            for (std::size_t i = 0; i < size_; ++i) {
                mpfr_sub(entries[i], x.entries[i], y.entries[i], rnd);
            }
        }

        // TODO: What to do if input MPFRVectors have different sizes?
        void set_axpy(mpfr_t a, const MPFRVector &x, const MPFRVector &y,
                      mpfr_rnd_t rnd) {
            for (std::size_t i = 0; i < size_; ++i) {
                mpfr_fma(entries[i], a, x.entries[i], y.entries[i], rnd);
            }
        }

        // TODO: What to do if input MPFRVectors have different sizes?
        void set_axmy(mpfr_t a, const MPFRVector &x, const MPFRVector &y,
                      mpfr_rnd_t rnd) {
            for (std::size_t i = 0; i < size_; ++i) {
                mpfr_fms(entries[i], a, x.entries[i], y.entries[i], rnd);
            }
        }

        // TODO: What to do if input MPFRMatrix and MPFRVector have
        // incompatible sizes?
        void set_matrix_vector_multiply(
                const MPFRMatrix &mat, const MPFRVector &vec, mpfr_rnd_t rnd) {
            for (std::size_t i = 0, k = 0; i < size_; ++i) {
                mpfr_mul(entries[i], mat.data()[k], vec[0], rnd);
                ++k;
                for (std::size_t j = 1; j < size_; ++j, ++k) {
                    mpfr_fma(entries[i],
                             mat.data()[k], vec[j], entries[i], rnd);
                }
            }
        }

    }; // class MPFRVector

} // namespace dznl

#endif // DZNL_MPFR_VECTOR_HPP_INCLUDED
