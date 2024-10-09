(set-logic QF_BVFP)

(declare-const s_x (_ BitVec 1))
(declare-const x_exponent (_ BitVec 8))
(declare-const x_mantissa (_ BitVec 23))
(define-fun x () Float32 (fp s_x x_exponent x_mantissa))
(assert (not (fp.isInfinite x)))
(assert (not (fp.isNaN x)))

(declare-const s_y (_ BitVec 1))
(declare-const y_exponent (_ BitVec 8))
(declare-const y_mantissa (_ BitVec 23))
(define-fun y () Float32 (fp s_y y_exponent y_mantissa))
(assert (not (fp.isInfinite y)))
(assert (not (fp.isNaN y)))

(declare-const s_s (_ BitVec 1))
(declare-const s_exponent (_ BitVec 8))
(declare-const s_mantissa (_ BitVec 23))
(define-fun s () Float32 (fp s_s s_exponent s_mantissa))
(assert (not (fp.isInfinite s)))
(assert (not (fp.isNaN s)))

(declare-const s_e (_ BitVec 1))
(declare-const e_exponent (_ BitVec 8))
(declare-const e_mantissa (_ BitVec 23))
(define-fun e () Float32 (fp s_e e_exponent e_mantissa))
(assert (not (fp.isInfinite e)))
(assert (not (fp.isNaN e)))

(assert (= s (fp.add RNE x y)))
(define-fun x_prime () Float32 (fp.sub RNE s y))
(define-fun y_prime () Float32 (fp.sub RNE s x_prime))
(define-fun x_err () Float32 (fp.sub RNE x x_prime))
(define-fun y_err () Float32 (fp.sub RNE y y_prime))
(assert (= e (fp.add RNE x_err y_err)))

(define-fun p () (_ BitVec 16) #x0018)
(define-fun e_x () (_ BitVec 16) (bvadd #x7F80 (concat #x00 x_exponent)))
(define-fun e_y () (_ BitVec 16) (bvadd #x7F80 (concat #x00 y_exponent)))
(define-fun e_s () (_ BitVec 16) (bvadd #x7F80 (concat #x00 s_exponent)))
(define-fun e_e () (_ BitVec 16) (bvadd #x7F80 (concat #x00 e_exponent)))

(define-fun num_leading_ones ((v (_ BitVec 23))) (_ BitVec 16)
    (ite (= ((_ extract 22 0) v) #b11111111111111111111111) #x0017
    (ite (= ((_ extract 21 0) v) #b1111111111111111111111) #x0016
    (ite (= ((_ extract 20 0) v) #b111111111111111111111) #x0015
    (ite (= ((_ extract 19 0) v) #b11111111111111111111) #x0014
    (ite (= ((_ extract 18 0) v) #b1111111111111111111) #x0013
    (ite (= ((_ extract 17 0) v) #b111111111111111111) #x0012
    (ite (= ((_ extract 16 0) v) #b11111111111111111) #x0011
    (ite (= ((_ extract 15 0) v) #b1111111111111111) #x0010
    (ite (= ((_ extract 14 0) v) #b111111111111111) #x000F
    (ite (= ((_ extract 13 0) v) #b11111111111111) #x000E
    (ite (= ((_ extract 12 0) v) #b1111111111111) #x000D
    (ite (= ((_ extract 11 0) v) #b111111111111) #x000C
    (ite (= ((_ extract 10 0) v) #b11111111111) #x000B
    (ite (= ((_ extract 9 0) v) #b1111111111) #x000A
    (ite (= ((_ extract 8 0) v) #b111111111) #x0009
    (ite (= ((_ extract 7 0) v) #b11111111) #x0008
    (ite (= ((_ extract 6 0) v) #b1111111) #x0007
    (ite (= ((_ extract 5 0) v) #b111111) #x0006
    (ite (= ((_ extract 4 0) v) #b11111) #x0005
    (ite (= ((_ extract 3 0) v) #b1111) #x0004
    (ite (= ((_ extract 2 0) v) #b111) #x0003
    (ite (= ((_ extract 1 0) v) #b11) #x0002
    (ite (= ((_ extract 0 0) v) #b1) #x0001 #x0000))))))))))))))))))))))))

(define-fun o_x () (_ BitVec 16) (num_leading_ones x_mantissa))
(define-fun o_y () (_ BitVec 16) (num_leading_ones y_mantissa))
(define-fun o_s () (_ BitVec 16) (num_leading_ones s_mantissa))
(define-fun o_e () (_ BitVec 16) (num_leading_ones e_mantissa))

(define-fun last_nonzero_bit_index ((v (_ BitVec 23))) (_ BitVec 16)
    (ite (= ((_ extract 22 0) v) #b00000000000000000000000) #x0000
    (ite (= ((_ extract 21 0) v) #b0000000000000000000000) #x0001
    (ite (= ((_ extract 20 0) v) #b000000000000000000000) #x0002
    (ite (= ((_ extract 19 0) v) #b00000000000000000000) #x0003
    (ite (= ((_ extract 18 0) v) #b0000000000000000000) #x0004
    (ite (= ((_ extract 17 0) v) #b000000000000000000) #x0005
    (ite (= ((_ extract 16 0) v) #b00000000000000000) #x0006
    (ite (= ((_ extract 15 0) v) #b0000000000000000) #x0007
    (ite (= ((_ extract 14 0) v) #b000000000000000) #x0008
    (ite (= ((_ extract 13 0) v) #b00000000000000) #x0009
    (ite (= ((_ extract 12 0) v) #b0000000000000) #x000A
    (ite (= ((_ extract 11 0) v) #b000000000000) #x000B
    (ite (= ((_ extract 10 0) v) #b00000000000) #x000C
    (ite (= ((_ extract 9 0) v) #b0000000000) #x000D
    (ite (= ((_ extract 8 0) v) #b000000000) #x000E
    (ite (= ((_ extract 7 0) v) #b00000000) #x000F
    (ite (= ((_ extract 6 0) v) #b0000000) #x0010
    (ite (= ((_ extract 5 0) v) #b000000) #x0011
    (ite (= ((_ extract 4 0) v) #b00000) #x0012
    (ite (= ((_ extract 3 0) v) #b0000) #x0013
    (ite (= ((_ extract 2 0) v) #b000) #x0014
    (ite (= ((_ extract 1 0) v) #b00) #x0015
    (ite (= ((_ extract 0 0) v) #b0) #x0016 #x0017))))))))))))))))))))))))

(define-fun n_x () (_ BitVec 16) (last_nonzero_bit_index x_mantissa))
(define-fun n_y () (_ BitVec 16) (last_nonzero_bit_index y_mantissa))
(define-fun n_s () (_ BitVec 16) (last_nonzero_bit_index s_mantissa))
(define-fun n_e () (_ BitVec 16) (last_nonzero_bit_index e_mantissa))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; METATHEOREMS

; Theorem: 0 <= o_x <= n_x < p.

(push 1)
    (assert (not (and (bvule #x0000 o_x)
                      (bvule o_x n_x)
                      (bvult n_x p))))
    (check-sat)
(pop 1)

; Theorem: 0 <= o_y <= n_y < p.

(push 1)
    (assert (not (and (bvule #x0000 o_y)
                      (bvule o_y n_y)
                      (bvult n_y p))))
    (check-sat)
(pop 1)

; Theorem: 0 <= o_s <= n_s < p.

(push 1)
    (assert (not (and (bvule #x0000 o_s)
                      (bvule o_s n_s)
                      (bvult n_s p))))
    (check-sat)
(pop 1)

; Theorem: 0 <= o_e <= n_e < p.

(push 1)
    (assert (not (and (bvule #x0000 o_e)
                      (bvule o_e n_e)
                      (bvult n_e p))))
    (check-sat)
(pop 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; CASE 0: ONE OR BOTH ADDENDS ARE ZERO

; Theorem: If x and y are both zero, then s and e are both zero.

(push 1)
    ; Hypotheses:
    (assert (fp.isZero x))
    (assert (fp.isZero y))
    ; Conclusion:
    (assert (not (fp.isZero s)))
    (assert (not (fp.isZero e)))
    (check-sat)
(pop 1)

; If x is zero, then s == y and e is zero.

(push 1)
    ; Hypotheses:
    (assert (fp.isZero x))
    ; Conclusion:
    (assert (not (and (fp.eq s y) (fp.isZero e))))
    (check-sat)
(pop 1)

; If y is zero, then s == x and e is zero.

(push 1)
    ; Hypotheses:
    (assert (fp.isZero y))
    ; Conclusion:
    (assert (not (and (fp.eq s x) (fp.isZero e))))
    (check-sat)
(pop 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; CASE 1: ADDENDS ARE AT LEAST 2-SEPARATED

; Theorem: If e_x - (p + 2) >= e_y, then s === x and e == y.

(push 1)
    ; Hypotheses:
    (assert (bvugt (bvsub e_x (bvadd p #x0002)) e_y))
    ; Conclusion:
    (assert (not (and (= s x) (fp.eq e y))))
    (check-sat)
(pop 1)

; Theorem: If e_x <= e_y - (p + 2), then s === y and e == x.

(push 1)
    ; Hypotheses:
    (assert (bvule e_x (bvsub e_y (bvadd p #x0002))))
    ; Conclusion:
    (assert (not (and (= s y) (fp.eq e x))))
    (check-sat)
(pop 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; CASE 2: ADDENDS ARE 1-SEPARATED

;;;;;;;;;;;;;;;;;;;;;;;;;;; CASE 2.1: ADDENDS ARE 1-SEPARATED AND HAVE SAME SIGN

; Theorem: If e_x - (p + 1) == e_y and s_x == s_y, then s === x and e == y.

(push 1)
    ; Hypotheses:
    (assert (= s_x s_y))
    (assert (= (bvsub e_x (bvadd p #x0001)) e_y))
    ; Conclusion:
    (assert (not (and (= s x) (fp.eq e y))))
    (check-sat)
(pop 1)

; Theorem: If e_x == e_y - (p + 1) and s_x == s_y, then s === y and e == x.

(push 1)
    ; Hypotheses:
    (assert (= s_x s_y))
    (assert (= e_x (bvsub e_y (bvadd p #x0001))))
    ; Conclusion:
    (assert (not (and (= s y) (fp.eq e x))))
    (check-sat)
(pop 1)

;;;;;;;;;;;;;;;;;;;;; CASE 2.2: ADDENDS ARE 1-SEPARATED AND HAVE DIFFERENT SIGNS

; Starting from case 2.2, we will not be able to determine the exact values of
; s and e using our approximate model of floating-point arithmetic. Instead, we
; will only be able to determine s_s, s_e, and ranges of possible values for
; e_s, e_e, o_s, o_e, n_s, and n_e.

; Theorem: If e_x - (p + 1) == e_y and s_x != s_y, then:
; - s_s == s_x.
; - s_e can be s_x or s_y.
; - e_s == e_x or (e_s == e_x - 1 and n_x == 0 and o_s == p - 1).
; - e_e <= e_y and e_e >= e_y - (p - 1).
; - TBD: o_s, o_e, n_s, n_e

(push 1)
    ; Hypotheses:
    (assert (not (= s_x s_y)))
    (assert (= (bvsub e_x (bvadd p #x0001)) e_y))
    ; Conclusion:
    (assert (not (and (= s_s s_x)
                      (or (= e_s e_x) (and (= e_s (bvsub e_x #x0001))
                                           (= n_x #x0000)
                                           (= o_s (bvsub p #x0001))))
                      (and (bvule e_e e_y)
                           (bvuge e_e (bvsub e_y (bvsub p #x0001)))))))
    (check-sat)
(pop 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; CASE 3: ADDENDS ARE 0-SEPARATED

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; CASE 4: ADDENDS OVERLAP
