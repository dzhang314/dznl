(set-logic QF_BVFP)
#include "Float16.inc"
#include "FloatDefs.inc"

(declare-const sa0 SIGN)
(declare-const sb0 SIGN)
(declare-const sc0 SIGN)
(declare-const sd0 SIGN)
(declare-const sa5 SIGN)
(declare-const sb5 SIGN)
(declare-const sc5 SIGN)
(declare-const sd5 SIGN)

(declare-const ra0 EXPONENT)
(declare-const rb0 EXPONENT)
(declare-const rc0 EXPONENT)
(declare-const rd0 EXPONENT)
(declare-const ra5 EXPONENT)
(declare-const rb5 EXPONENT)
(declare-const rc5 EXPONENT)
(declare-const rd5 EXPONENT)

(declare-const ma0 MANTISSA)
(declare-const mb0 MANTISSA)
(declare-const mc0 MANTISSA)
(declare-const md0 MANTISSA)
(declare-const ma5 MANTISSA)
(declare-const mb5 MANTISSA)
(declare-const mc5 MANTISSA)
(declare-const md5 MANTISSA)

(define-fun ea0 () INT (apply-bias ra0))
(define-fun eb0 () INT (apply-bias rb0))
(define-fun ec0 () INT (apply-bias rc0))
(define-fun ed0 () INT (apply-bias rd0))
(define-fun ea5 () INT (apply-bias ra5))
(define-fun eb5 () INT (apply-bias rb5))
(define-fun ec5 () INT (apply-bias rc5))
(define-fun ed5 () INT (apply-bias rd5))

(define-fun a0 () FLOAT (fp sa0 ra0 ma0))
(define-fun b0 () FLOAT (fp sb0 rb0 mb0))
(define-fun c0 () FLOAT (fp sc0 rc0 mc0))
(define-fun d0 () FLOAT (fp sd0 rd0 md0))
(define-fun a5 () FLOAT (fp sa5 ra5 ma5))
(define-fun b5 () FLOAT (fp sb5 rb5 mb5))
(define-fun c5 () FLOAT (fp sc5 rc5 mc5))
(define-fun d5 () FLOAT (fp sd5 rd5 md5))

(assert (not (fp.isSubnormal a0)))
(assert (not (fp.isSubnormal b0)))
(assert (not (fp.isSubnormal c0)))
(assert (not (fp.isSubnormal d0)))
(assert (not (fp.isSubnormal a5)))
(assert (not (fp.isSubnormal b5)))
(assert (not (fp.isSubnormal c5)))
(assert (not (fp.isSubnormal d5)))

(assert (not (fp.isInfinite a0)))
(assert (not (fp.isInfinite b0)))
(assert (not (fp.isInfinite c0)))
(assert (not (fp.isInfinite d0)))
(assert (not (fp.isInfinite a5)))
(assert (not (fp.isInfinite b5)))
(assert (not (fp.isInfinite c5)))
(assert (not (fp.isInfinite d5)))

(assert (not (fp.isNaN a0)))
(assert (not (fp.isNaN b0)))
(assert (not (fp.isNaN c0)))
(assert (not (fp.isNaN d0)))
(assert (not (fp.isNaN a5)))
(assert (not (fp.isNaN b5)))
(assert (not (fp.isNaN c5)))
(assert (not (fp.isNaN d5)))

(assert (or
    (bvsgt ea0 (bvadd ec0 PRECISION_INT))
    (and (= ea0 (bvadd ec0 PRECISION_INT)) (= mc0 ZERO_MANTISSA))
    (fp.isZero c0)))
(assert (or
    (bvsgt eb0 (bvadd ed0 PRECISION_INT))
    (and (= eb0 (bvadd ed0 PRECISION_INT)) (= md0 ZERO_MANTISSA))
    (fp.isZero d0)))

; a1, b1 = two_sum(a0, b0)
(define-fun a1 () FLOAT (two-sum a0 b0))
(define-fun b1 () FLOAT (two-sum-err a0 b0))

; c1, d1 = two_sum(c0, d0)
(define-fun c1 () FLOAT (two-sum c0 d0))
(define-fun d1 () FLOAT (two-sum-err c0 d0))

; b2, c2 = two_sum(b1, c1)
(define-fun b2 () FLOAT (two-sum b1 c1))
(define-fun c2 () FLOAT (two-sum-err b1 c1))

; a3, b3 = two_sum(a1, b2)
(define-fun a3 () FLOAT (two-sum a1 b2))
(define-fun b3 () FLOAT (two-sum-err a1 b2))

; b4, d4 = two_sum(b3, d1)
(define-fun b4 () FLOAT (two-sum b3 d1))
(define-fun d4 () FLOAT (two-sum-err b3 d1))

; a5, b5 = two_sum(a3, b4)
(assert (= a5 (two-sum a3 b4)))
(assert (= b5 (two-sum-err a3 b4)))

; c5, d5 = two_sum(c2, d4)
(assert (= c5 (two-sum c2 d4)))
(assert (= d5 (two-sum-err c2 d4)))

(assert (not (or
    (bvsge ea5 (bvadd ec5 (bvsub (bvadd PRECISION_INT PRECISION_INT) ONE_INT)))
    (fp.isZero c5))))

(check-sat)
(get-model)
