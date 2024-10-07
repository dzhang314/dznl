(set-logic QF_BVFP)

; Suppose we have floating-point numbers (x, y) with exponents (e_x, e_y).

(declare-const x_sign (_ BitVec 1))
(declare-const x_exponent (_ BitVec 8))
(declare-const x_mantissa (_ BitVec 23))
(define-fun x () Float32 (fp x_sign x_exponent x_mantissa))

(declare-const y_sign (_ BitVec 1))
(declare-const y_exponent (_ BitVec 8))
(declare-const y_mantissa (_ BitVec 23))
(define-fun y () Float32 (fp y_sign y_exponent y_mantissa))

; Let s := x + y (RNE), and let e_s denote its exponent.

(declare-const s_sign (_ BitVec 1))
(declare-const s_exponent (_ BitVec 8))
(declare-const s_mantissa (_ BitVec 23))
(define-fun s () Float32 (fp s_sign s_exponent s_mantissa))
(assert (= s (fp.add RNE x y)))

; Let e := x + y - s (exact), as computed by the
; TwoSum algorithm, and let e_e denote its exponent.

(declare-const e_sign (_ BitVec 1))
(declare-const e_exponent (_ BitVec 8))
(declare-const e_mantissa (_ BitVec 23))
(define-fun e () Float32 (fp e_sign e_exponent e_mantissa))

(define-fun x_prime () Float32 (fp.sub RNE s y))
(define-fun y_prime () Float32 (fp.sub RNE s x_prime))
(define-fun x_err () Float32 (fp.sub RNE x x_prime))
(define-fun y_err () Float32 (fp.sub RNE y y_prime))
(assert (= e (fp.add RNE x_err y_err)))

; We extend e_x, e_y, e_s. and e_e in order
; to perform arithmetic without overflow.

(define-fun e_x () (_ BitVec 16)
    (bvadd #b0111111110000000 (concat #b00000000 x_exponent)))
(define-fun e_y () (_ BitVec 16)
    (bvadd #b0111111110000000 (concat #b00000000 y_exponent)))
(define-fun e_s () (_ BitVec 16)
    (bvadd #b0111111110000000 (concat #b00000000 s_exponent)))
(define-fun e_e () (_ BitVec 16)
    (bvadd #b0111111110000000 (concat #b00000000 e_exponent)))

; Let e_min and e_max denote min(e_x, e_y) and max(e_x, e_y), respectively.

(define-fun e_min () (_ BitVec 16) (ite (bvult e_x e_y) e_x e_y))
(define-fun e_max () (_ BitVec 16) (ite (bvugt e_x e_y) e_x e_y))

; Theorem: If e is finite, nonzero, and not subnormal, then e_e <= e_s - 24.

(assert (not (fp.isInfinite e)))
(assert (not (fp.isNaN e)))
(assert (not (fp.isZero e)))
(assert (not (fp.isSubnormal e)))
(assert (not (bvule e_e (bvsub e_s #x0018))))
(check-sat)

; Known to be unsatisfiable. Takes 5-10 minutes to verify with CVC5.
