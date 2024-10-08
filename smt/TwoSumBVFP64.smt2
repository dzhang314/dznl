(set-logic QF_BVFP)

; Suppose we have floating-point numbers (x, y) with exponents (e_x, e_y).

(declare-const x_sign (_ BitVec 1))
(declare-const x_exponent (_ BitVec 11))
(declare-const x_mantissa (_ BitVec 52))
(define-fun x () Float64 (fp x_sign x_exponent x_mantissa))

(declare-const y_sign (_ BitVec 1))
(declare-const y_exponent (_ BitVec 11))
(declare-const y_mantissa (_ BitVec 52))
(define-fun y () Float64 (fp y_sign y_exponent y_mantissa))

; Let s := x + y (RNE), and let e_s denote its exponent.

(declare-const s_sign (_ BitVec 1))
(declare-const s_exponent (_ BitVec 11))
(declare-const s_mantissa (_ BitVec 52))
(define-fun s () Float64 (fp s_sign s_exponent s_mantissa))
(assert (= s (fp.add RNE x y)))

; Let e := x + y - s (exact), as computed by the
; TwoSum algorithm, and let e_e denote its exponent.

(declare-const e_sign (_ BitVec 1))
(declare-const e_exponent (_ BitVec 11))
(declare-const e_mantissa (_ BitVec 52))
(define-fun e () Float64 (fp e_sign e_exponent e_mantissa))

(define-fun x_prime () Float64 (fp.sub RNE s y))
(define-fun y_prime () Float64 (fp.sub RNE s x_prime))
(define-fun x_err () Float64 (fp.sub RNE x x_prime))
(define-fun y_err () Float64 (fp.sub RNE y y_prime))
(assert (= e (fp.add RNE x_err y_err)))

; We extend e_x, e_y, e_s. and e_e in order
; to perform arithmetic without overflow.

(define-fun e_x () (_ BitVec 16)
    (bvadd #b0111110000000000 (concat #b00000 x_exponent)))
(define-fun e_y () (_ BitVec 16)
    (bvadd #b0111110000000000 (concat #b00000 y_exponent)))
(define-fun e_s () (_ BitVec 16)
    (bvadd #b0111110000000000 (concat #b00000 s_exponent)))
(define-fun e_e () (_ BitVec 16)
    (bvadd #b0111110000000000 (concat #b00000 e_exponent)))

; Let e_min and e_max denote min(e_x, e_y) and max(e_x, e_y), respectively.

(define-fun e_min () (_ BitVec 16) (ite (bvult e_x e_y) e_x e_y))
(define-fun e_max () (_ BitVec 16) (ite (bvugt e_x e_y) e_x e_y))

; Theorem: If e is finite, nonzero, and not subnormal, then e_e < e_s - 53 or
; e_e = e_s - 53 and e is a power of 2 (i.e., its mantissa bits are all zero).

(push 1)
    ; Hypotheses:
    (assert (not (fp.isInfinite e)))
    (assert (not (fp.isNaN e)))
    (assert (not (fp.isZero e)))
    (assert (not (fp.isSubnormal e)))
    ; Conclusion:
    (assert (not (or (bvult e_e (bvsub e_s #x0035))
                     (and (= e_e (bvsub e_s #x0035))
                          (= e_mantissa #x0000000000000)))))
    (check-sat) ; Takes roughly an hour to verify UNSAT with CVC5.
(pop 1)
