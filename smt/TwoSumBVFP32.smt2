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

(define-fun num_leading_zeroes ((v (_ BitVec 23))) (_ BitVec 16)
    (ite (= ((_ extract 22 0) v) #b00000000000000000000000) #x0017
    (ite (= ((_ extract 22 1) v) #b0000000000000000000000) #x0016
    (ite (= ((_ extract 22 2) v) #b000000000000000000000) #x0015
    (ite (= ((_ extract 22 3) v) #b00000000000000000000) #x0014
    (ite (= ((_ extract 22 4) v) #b0000000000000000000) #x0013
    (ite (= ((_ extract 22 5) v) #b000000000000000000) #x0012
    (ite (= ((_ extract 22 6) v) #b00000000000000000) #x0011
    (ite (= ((_ extract 22 7) v) #b0000000000000000) #x0010
    (ite (= ((_ extract 22 8) v) #b000000000000000) #x000F
    (ite (= ((_ extract 22 9) v) #b00000000000000) #x000E
    (ite (= ((_ extract 22 10) v) #b0000000000000) #x000D
    (ite (= ((_ extract 22 11) v) #b000000000000) #x000C
    (ite (= ((_ extract 22 12) v) #b00000000000) #x000B
    (ite (= ((_ extract 22 13) v) #b0000000000) #x000A
    (ite (= ((_ extract 22 14) v) #b000000000) #x0009
    (ite (= ((_ extract 22 15) v) #b00000000) #x0008
    (ite (= ((_ extract 22 16) v) #b0000000) #x0007
    (ite (= ((_ extract 22 17) v) #b000000) #x0006
    (ite (= ((_ extract 22 18) v) #b00000) #x0005
    (ite (= ((_ extract 22 19) v) #b0000) #x0004
    (ite (= ((_ extract 22 20) v) #b000) #x0003
    (ite (= ((_ extract 22 21) v) #b00) #x0002
    (ite (= ((_ extract 22 22) v) #b0) #x0001 #x0000))))))))))))))))))))))))

(define-fun z_x () (_ BitVec 16) (num_leading_zeroes x_mantissa))
(define-fun z_y () (_ BitVec 16) (num_leading_zeroes y_mantissa))
(define-fun z_s () (_ BitVec 16) (num_leading_zeroes s_mantissa))
(define-fun z_e () (_ BitVec 16) (num_leading_zeroes e_mantissa))

(define-fun num_leading_ones ((v (_ BitVec 23))) (_ BitVec 16)
    (ite (= ((_ extract 22 0) v) #b11111111111111111111111) #x0017
    (ite (= ((_ extract 22 1) v) #b1111111111111111111111) #x0016
    (ite (= ((_ extract 22 2) v) #b111111111111111111111) #x0015
    (ite (= ((_ extract 22 3) v) #b11111111111111111111) #x0014
    (ite (= ((_ extract 22 4) v) #b1111111111111111111) #x0013
    (ite (= ((_ extract 22 5) v) #b111111111111111111) #x0012
    (ite (= ((_ extract 22 6) v) #b11111111111111111) #x0011
    (ite (= ((_ extract 22 7) v) #b1111111111111111) #x0010
    (ite (= ((_ extract 22 8) v) #b111111111111111) #x000F
    (ite (= ((_ extract 22 9) v) #b11111111111111) #x000E
    (ite (= ((_ extract 22 10) v) #b1111111111111) #x000D
    (ite (= ((_ extract 22 11) v) #b111111111111) #x000C
    (ite (= ((_ extract 22 12) v) #b11111111111) #x000B
    (ite (= ((_ extract 22 13) v) #b1111111111) #x000A
    (ite (= ((_ extract 22 14) v) #b111111111) #x0009
    (ite (= ((_ extract 22 15) v) #b11111111) #x0008
    (ite (= ((_ extract 22 16) v) #b1111111) #x0007
    (ite (= ((_ extract 22 17) v) #b111111) #x0006
    (ite (= ((_ extract 22 18) v) #b11111) #x0005
    (ite (= ((_ extract 22 19) v) #b1111) #x0004
    (ite (= ((_ extract 22 20) v) #b111) #x0003
    (ite (= ((_ extract 22 21) v) #b11) #x0002
    (ite (= ((_ extract 22 22) v) #b1) #x0001 #x0000))))))))))))))))))))))))

(define-fun o_x () (_ BitVec 16) (num_leading_ones x_mantissa))
(define-fun o_y () (_ BitVec 16) (num_leading_ones y_mantissa))
(define-fun o_s () (_ BitVec 16) (num_leading_ones s_mantissa))
(define-fun o_e () (_ BitVec 16) (num_leading_ones e_mantissa))

(define-fun final_one_index ((v (_ BitVec 23))) (_ BitVec 16)
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

(define-fun n_x () (_ BitVec 16) (final_one_index x_mantissa))
(define-fun n_y () (_ BitVec 16) (final_one_index y_mantissa))
(define-fun n_s () (_ BitVec 16) (final_one_index s_mantissa))
(define-fun n_e () (_ BitVec 16) (final_one_index e_mantissa))

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

; Theorem: If e_x - (p + 1) == e_y and s_x == s_y, then s === x and e == y.

(push 1)
    ; Hypotheses:
    (assert (= (bvsub e_x (bvadd p #x0001)) e_y))
    (assert (= s_x s_y))
    ; Conclusion:
    (assert (not (and (= s x) (fp.eq e y))))
    (check-sat)
(pop 1)

; Theorem: If e_x == e_y - (p + 1) and s_x == s_y, then s === y and e == x.

(push 1)
    ; Hypotheses:
    (assert (= e_x (bvsub e_y (bvadd p #x0001))))
    (assert (= s_x s_y))
    ; Conclusion:
    (assert (not (and (= s y) (fp.eq e x))))
    (check-sat)
(pop 1)

; Theorem: If e_x - (p + 1) == e_y, s_x != s_y, and n_x != 0,
; then s === x and e == y.

(push 1)
    ; Hypotheses:
    (assert (= (bvsub e_x (bvadd p #x0001)) e_y))
    (assert (not (= s_x s_y)))
    (assert (not (= n_x #x0000)))
    ; Conclusion:
    (assert (not (and (= s x) (fp.eq e y))))
    (check-sat)
(pop 1)

; Theorem: If e_x == e_y - (p + 1), s_x != s_y, and n_y != 0,
; then s === y and e == x.

(push 1)
    ; Hypotheses:
    (assert (= e_x (bvsub e_y (bvadd p #x0001))))
    (assert (not (= s_x s_y)))
    (assert (not (= n_y #x0000)))
    ; Conclusion:
    (assert (not (and (= s y) (fp.eq e x))))
    (check-sat)
(pop 1)

; Theorem: If e_x - (p + 1) == e_y, s_x != s_y, n_x == 0, and n_y == 0,
; then s === x and e == y.

(push 1)
    ; Hypotheses:
    (assert (= (bvsub e_x (bvadd p #x0001)) e_y))
    (assert (not (= s_x s_y)))
    (assert (= n_x #x0000))
    (assert (= n_y #x0000))
    ; Conclusion:
    (assert (not (and (= s x) (fp.eq e y))))
    (check-sat)
(pop 1)

; Theorem: If e_x == e_y - (p + 1), s_x != s_y, n_x == 0, and n_y == 0,
; then s === y and e == x.

(push 1)
    ; Hypotheses:
    (assert (= e_x (bvsub e_y (bvadd p #x0001))))
    (assert (not (= s_x s_y)))
    (assert (= n_x #x0000))
    (assert (= n_y #x0000))
    ; Conclusion:
    (assert (not (and (= s y) (fp.eq e x))))
    (check-sat)
(pop 1)

; Theorem: If e_x - (p + 1) == e_y, s_x != s_y, n_x == 0, n_y != 0,
; and y is not subnormal, then s is the immediate predecessor of x
; (which means s_s == s_x, e_s == e_x - 1, and o_s == p - 1) and e_e < e_y.

(push 1)
    ; Hypotheses:
    (assert (= (bvsub e_x (bvadd p #x0001)) e_y))
    (assert (not (= s_x s_y)))
    (assert (= n_x #x0000))
    (assert (not (= n_y #x0000)))
    (assert (not (fp.isSubnormal y)))
    ; Conclusion:
    (assert (not (and (= s_s s_x)
                      (= e_s (bvsub e_x #x0001))
                      (= o_s (bvsub p #x0001))
                      (= s_e s_x)
                      (bvult e_e e_y))))
    (check-sat)
(pop 1)

; Theorem: If e_x == e_y - (p + 1), s_x != s_y, n_x != 0, n_y == 0,
; and x is not subnormal, then s is the immediate predecessor of y
; (which means s_s == s_y, e_s == e_y - 1, and o_s == p - 1) and e_e < e_x.

(push 1)
    ; Hypotheses:
    (assert (= e_x (bvsub e_y (bvadd p #x0001))))
    (assert (not (= s_x s_y)))
    (assert (not (= n_x #x0000)))
    (assert (= n_y #x0000))
    (assert (not (fp.isSubnormal x)))
    ; Conclusion:
    (assert (not (and (= s_s s_y)
                      (= e_s (bvsub e_y #x0001))
                      (= o_s (bvsub p #x0001))
                      (= s_e s_y)
                      (bvult e_e e_x))))
    (check-sat)
(pop 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; CASE 3: ADDENDS ARE 0-SEPARATED

(push 1)
    ; Hypotheses:
    (assert (= (bvsub e_x p) e_y))
    (assert (= s_x s_y))
    (assert (not (= o_x (bvsub p #x0001))))
    (assert (not (fp.isSubnormal y)))
    ; Conclusion:
    (assert (not (and (= s_s s_x)
                      (= e_s e_x)
                      (or (and (= s x) (fp.eq e y))
                          (and (not (= s_e s_x))
                               (bvult e_e e_y))
                          (and (not (= s_e s_x))
                               (= e_e e_y)
                               (= n_y #x0000)
                               (= n_e #x0000))))))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (= (bvsub e_x p) e_y))
    (assert (= s_x s_y))
    (assert (= o_x (bvsub p #x0001)))
    (assert (not (fp.isZero y)))
    (assert (not (fp.isSubnormal y)))
    ; Conclusion:
    (assert (not (and (= s_s s_x)
                      (= e_s (bvadd e_x #x0001))
                      (not (= s_e s_x))
                      (or (bvult e_e e_y)
                          (and (= e_e e_y)
                               (= n_y #x0000)
                               (= n_e #x0000))))))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (= e_x (bvsub e_y p)))
    (assert (= s_x s_y))
    (assert (not (= o_y (bvsub p #x0001))))
    (assert (not (fp.isSubnormal x)))
    ; Conclusion:
    (assert (not (and (= s_s s_y)
                      (= e_s e_y)
                      (or (and (= s y) (fp.eq e x))
                          (and (not (= s_e s_y))
                               (bvult e_e e_x))
                          (and (not (= s_e s_y))
                               (= e_e e_x)
                               (= n_x #x0000)
                               (= n_e #x0000))))))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (= e_x (bvsub e_y p)))
    (assert (= s_x s_y))
    (assert (= o_y (bvsub p #x0001)))
    (assert (not (fp.isZero x)))
    (assert (not (fp.isSubnormal x)))
    ; Conclusion:
    (assert (not (and (= s_s s_y)
                      (= e_s (bvadd e_y #x0001))
                      (not (= s_e s_y))
                      (or (bvult e_e e_x)
                          (and (= e_e e_x)
                               (= n_x #x0000)
                               (= n_e #x0000))))))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (= (bvsub e_x p) e_y))
    (assert (not (= s_x s_y)))
    ; Conclusion:
    (assert (not (and (= s_s s_x)
                      (= e_s e_x))))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (= e_x (bvsub e_y p)))
    (assert (not (= s_x s_y)))
    ; Conclusion:
    (check-sat)
(pop 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; CASE 4: ADDENDS PARTIALLY OVERLAP

(push 1)
    ; Hypotheses:
    (assert (bvult (bvsub e_x p) e_y))
    (assert (bvugt e_x e_y))
    (assert (= s_x s_y))
    ; Conclusion:
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (bvugt e_x (bvsub e_y p)))
    (assert (bvult e_x e_y))
    (assert (= s_x s_y))
    ; Conclusion:
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (bvult (bvsub e_x p) e_y))
    (assert (bvugt e_x e_y))
    (assert (not (= s_x s_y)))
    ; Conclusion:
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (bvugt e_x (bvsub e_y p)))
    (assert (bvult e_x e_y))
    (assert (not (= s_x s_y)))
    ; Conclusion:
    (check-sat)
(pop 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; CASE 5: ADDENDS FULLY OVERLAP

; Theorem: If e_x == e_y, s_x == s_y, x and y are nonzero with different LSBs,
; and none of x, y, or e are subnormal, then s_s == s_x == s_y,
; e_s == e_x + 1 == e_y + 1, and e is a nonzero power of two.

(push 1)
    ; Hypotheses:
    (assert (= e_x e_y))
    (assert (= s_x s_y))
    (assert (not (fp.isZero x)))
    (assert (not (fp.isZero y)))
    (assert (xor (= n_x (bvsub p #x0001))
                 (= n_y (bvsub p #x0001))))
    (assert (not (fp.isSubnormal x)))
    (assert (not (fp.isSubnormal y)))
    (assert (not (fp.isSubnormal e)))
    ; Conclusion:
    (assert (not (and (= s_s s_x)
                      (= s_s s_y)
                      (= e_s (bvadd e_x #x0001))
                      (= e_s (bvadd e_y #x0001))
                      (not (fp.isZero e))
                      (= n_e #x0000))))
    (check-sat)
(pop 1)

; Theorem: If e_x == e_y, s_x == s_y, x and y are nonzero with the same LSB,
; and none of x, y, or e are subnormal, then s_s == s_x == s_y,
; e_s == e_x + 1 == e_y + 1, and e is zero.

(push 1)
    ; Hypotheses:
    (assert (= e_x e_y))
    (assert (= s_x s_y))
    (assert (not (fp.isZero x)))
    (assert (not (fp.isZero y)))
    (assert (not (xor (= n_x (bvsub p #x0001))
                      (= n_y (bvsub p #x0001)))))
    (assert (not (fp.isSubnormal x)))
    (assert (not (fp.isSubnormal y)))
    (assert (not (fp.isSubnormal e)))
    ; Conclusion:
    (assert (not (and (= s_s s_x)
                      (= s_s s_y)
                      (= e_s (bvadd e_x #x0001))
                      (= e_s (bvadd e_y #x0001))
                      (fp.isZero e))))
    (check-sat)
(pop 1)

; Theorem: If e_x == e_y, s_x != s_y, x and y are nonzero and not subnormal,
; then e_s < e_x == e_y and e is zero.

(push 1)
    ; Hypotheses:
    (assert (= e_x e_y))
    (assert (not (= s_x s_y)))
    (assert (not (fp.isZero x)))
    (assert (not (fp.isZero y)))
    (assert (not (fp.isSubnormal x)))
    (assert (not (fp.isSubnormal y)))
    ; Conclusion:
    (assert (not (and (bvult e_s e_x)
                      (bvult e_s e_y)
                      (fp.isZero e))))
    (check-sat)
(pop 1)
