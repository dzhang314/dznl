#include "Float64.inc"

#define SIGN (_ BitVec 1)
#define EXPONENT (_ BitVec EXPONENT_WIDTH)
#define MANTISSA (_ BitVec MANTISSA_WIDTH)
#define FLOAT (_ FloatingPoint EXPONENT_WIDTH PRECISION)
#define INT (_ BitVec INT_WIDTH)

#define CONCAT(S, T) S ## T
#define BV_LITERAL(VALUE, WIDTH) (_ CONCAT(bv, VALUE) WIDTH)
#define PRECISION_INT BV_LITERAL(PRECISION    , INT_WIDTH     )
#define ONE_INT       BV_LITERAL(1            , INT_WIDTH     )
#define BIAS_INT      BV_LITERAL(EXPONENT_BIAS, INT_WIDTH     )
#define PADDING       BV_LITERAL(0            , PADDING_WIDTH )
#define ZERO_MANTISSA BV_LITERAL(0            , MANTISSA_WIDTH)

(set-logic QF_BVFP)

(define-fun two-sum ((x FLOAT) (y FLOAT)) FLOAT
    (fp.add RNE x y))

(define-fun two-sum-err ((x FLOAT) (y FLOAT)) FLOAT
    (let ((s (fp.add RNE x y)))
    (let ((x_eff (fp.sub RNE s y)))
    (let ((y_eff (fp.sub RNE s x_eff)))
    (fp.add RNE (fp.sub RNE x x_eff) (fp.sub RNE y y_eff))))))

(define-fun apply-bias ((e EXPONENT)) INT
    (bvsub (concat PADDING e) BIAS_INT))

(declare-const sx SIGN)
(declare-const sy SIGN)
(declare-const rx EXPONENT)
(declare-const ry EXPONENT)
(declare-const mx MANTISSA)
(declare-const my MANTISSA)

(define-fun ex () INT (apply-bias rx))
(define-fun ey () INT (apply-bias ry))

(define-fun x () FLOAT (fp sx rx mx))
(define-fun y () FLOAT (fp sy ry my))
(define-fun s () FLOAT (two-sum x y))
(define-fun e () FLOAT (two-sum-err x y))

(assert (not (fp.isSubnormal x)))
(assert (not (fp.isSubnormal y)))
(assert (not (fp.isSubnormal s)))
(assert (not (fp.isSubnormal e)))
(assert (not (fp.isInfinite x)))
(assert (not (fp.isInfinite y)))
(assert (not (fp.isInfinite s)))
(assert (not (fp.isInfinite e)))
(assert (not (fp.isNaN x)))
(assert (not (fp.isNaN y)))
(assert (not (fp.isNaN s)))
(assert (not (fp.isNaN e)))

(define-fun x_pow2 () Bool (and (not (fp.isZero x)) (= mx ZERO_MANTISSA)))
(define-fun y_pow2 () Bool (and (not (fp.isZero y)) (= my ZERO_MANTISSA)))
(define-fun x_odd () Bool (= ((_ extract 0 0) mx) (_ bv1 1)))

; (x, y) == TwoSum(x, y) if and only if one of the following conditions holds:
; (1) y is zero.
; (2) ex > ey + (p+1).
; (3) ex = ey + (p+1) and one or more of the following sub-conditions holds:
;     (3a) x and y have the same sign.
;     (3b) x is not a power of 2.
;     (3c) y is a power of 2.
; (4) ex = ey + p, y is a power of 2, the mantissa of x is even
;     (i.e., its least significant bit is 0),
;     and one or more of the following sub-conditions holds:
;     (4a) x and y have the same sign.
;     (4b) x is not a power of 2.

(push 1)
(assert (not (=
    (or (fp.isZero y)
        (bvsgt ex (bvadd ey (bvadd PRECISION_INT ONE_INT)))
        (and (= ex (bvadd ey (bvadd PRECISION_INT ONE_INT))) (or (= sx sy) (not x_pow2) y_pow2))
        (and (= ex (bvadd ey PRECISION_INT)) (or (= sx sy) (not x_pow2)) y_pow2 (not x_odd)))
    (and (fp.eq s x) (fp.eq e y)))))
(check-sat)
(pop 1)
