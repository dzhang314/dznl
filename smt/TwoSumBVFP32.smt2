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

; Theorem: Exactly one of z_x and o_x is zero.
(push 1)
    (assert (not (xor (= z_x #x0000) (= o_x #x0000))))
    (check-sat)
(pop 1)

; Theorem: If z_x < p - 1, then z_x < n_x.

(push 1)
    ; Hypotheses:
    (assert (bvult z_x (bvsub p #x0001)))
    ; Conclusion:
    (assert (not (bvult z_x n_x)))
    (check-sat)
(pop 1)

; Theorem: If z_x == p - 1, then n_x == 0.

(push 1)
    ; Hypotheses:
    (assert (= z_x (bvsub p #x0001)))
    ; Conclusion:
    (assert (not (= n_x #x0000)))
    (check-sat)
(pop 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; CASE ANALYSIS

; Let e_min = min(e_x, e_y) and e_max = max(e_x, e_y). We split our
; analysis into five cases based on the gap between e_min and e_max.

; CASE 0: e_min == -inf (i.e., x or y is zero).
; CASE 1: e_min <= e_max - (p + 2).
; CASE 2: e_min == e_max - (p + 1).
; CASE 3: e_min == e_max - p.
; CASE 4: e_max - p < e_min < e_max.
; CASE 5: e_min == e_max.

; We do not use the expressions e_min and e_max in our concrete theorem
; statements. Instead, we state each theorem in two versions, A and B,
; corresponding to e_x > e_y and e_x < e_y, respectively. In some cases,
; we also differentiate between subcases S and D, in which x and y have
; the same or different signs, respectively. Further ad-hoc case splitting
; is denoted by an underscore following this systematic name.

(define-fun CASE0A () Bool (fp.isZero y))
(define-fun CASE0B () Bool (fp.isZero x))
(define-fun CASE1A () Bool (bvuge (bvsub e_x (bvadd p #x0002)) e_y))
(define-fun CASE1B () Bool (bvule e_x (bvsub e_y (bvadd p #x0002))))
(define-fun CASE2AS () Bool (and (= (bvsub e_x (bvadd p #x0001)) e_y) (= s_x s_y)))
(define-fun CASE2AD_N () Bool (and (= (bvsub e_x (bvadd p #x0001)) e_y) (not (= s_x s_y)) (not (= n_x #x0000))))
(define-fun CASE2AD_ZZ () Bool (and (= (bvsub e_x (bvadd p #x0001)) e_y) (not (= s_x s_y)) (= n_x #x0000) (= n_y #x0000)))
(define-fun CASE2AD_ZN () Bool (and (= (bvsub e_x (bvadd p #x0001)) e_y) (not (= s_x s_y)) (= n_x #x0000) (not (= n_y #x0000))))
(define-fun CASE2BS () Bool (and (= e_x (bvsub e_y (bvadd p #x0001))) (= s_x s_y)))
(define-fun CASE2BD_N () Bool (and (= e_x (bvsub e_y (bvadd p #x0001))) (not (= s_x s_y)) (not (= n_y #x0000))))
(define-fun CASE2BD_ZZ () Bool (and (= e_x (bvsub e_y (bvadd p #x0001))) (not (= s_x s_y)) (= n_x #x0000) (= n_y #x0000)))
(define-fun CASE2BD_ZN () Bool (and (= e_x (bvsub e_y (bvadd p #x0001))) (not (= s_x s_y)) (not (= n_x #x0000)) (= n_y #x0000)))
(define-fun CASE3AS () Bool (and (= (bvsub e_x p) e_y) (= s_x s_y)))
(define-fun CASE3AD () Bool (and (= (bvsub e_x p) e_y) (not (= s_x s_y))))
(define-fun CASE3BS () Bool (and (= e_x (bvsub e_y p)) (= s_x s_y)))
(define-fun CASE3BD () Bool (and (= e_x (bvsub e_y p)) (not (= s_x s_y))))
(define-fun CASE4AS () Bool (and (bvult (bvsub e_x p) e_y) (bvugt e_x e_y) (= s_x s_y)))
(define-fun CASE4AD () Bool (and (bvult (bvsub e_x p) e_y) (bvugt e_x e_y) (not (= s_x s_y))))
(define-fun CASE4BS () Bool (and (bvugt e_x (bvsub e_y p)) (bvult e_x e_y) (= s_x s_y)))
(define-fun CASE4BD () Bool (and (bvugt e_x (bvsub e_y p)) (bvult e_x e_y) (not (= s_x s_y))))
(define-fun CASE5S_X () Bool (and (= e_x e_y) (= s_x s_y) (not (fp.isZero x)) (not (fp.isZero y)) (xor (= n_x (bvsub p #x0001)) (= n_y (bvsub p #x0001)))))
(define-fun CASE5S_N () Bool (and (= e_x e_y) (= s_x s_y) (not (fp.isZero x)) (not (fp.isZero y)) (not (xor (= n_x (bvsub p #x0001)) (= n_y (bvsub p #x0001))))))
(define-fun CASE5D () Bool (and (= e_x e_y) (not (= s_x s_y)) (not (fp.isZero x)) (not (fp.isZero y))))

; Theorem: The preceding cases are exhaustive.

(push 1)
    (assert (not (or CASE0A CASE0B CASE1A CASE1B
                     CASE2AS CASE2AD_N CASE2AD_ZZ CASE2AD_ZN
                     CASE2BS CASE2BD_N CASE2BD_ZZ CASE2BD_ZN
                     CASE3AS CASE3AD CASE3BS CASE3BD
                     CASE4AS CASE4AD CASE4BS CASE4BD
                     CASE5S_X CASE5S_N CASE5D)))
    (check-sat)
(pop 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; CASE 0: ONE OR BOTH ADDENDS ARE ZERO

; If x is zero, then s == y and e is zero.

(push 1)
    ; Hypotheses:
    (assert CASE0A)
    ; Conclusion:
    (assert (not (and (fp.eq s x) (fp.isZero e))))
    (check-sat)
(pop 1)

; If y is zero, then s == x and e is zero.

(push 1)
    ; Hypotheses:
    (assert CASE0B)
    ; Conclusion:
    (assert (not (and (fp.eq s y) (fp.isZero e))))
    (check-sat)
(pop 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; CASE 1: ADDENDS ARE AT LEAST 2-SEPARATED

; Theorem: If e_x - (p + 2) >= e_y, then s === x and e == y.

(push 1)
    ; Hypotheses:
    (assert CASE1A)
    ; Conclusion:
    (assert (not (and (= s x) (fp.eq e y))))
    (check-sat)
(pop 1)

; Theorem: If e_x <= e_y - (p + 2), then s === y and e == x.

(push 1)
    ; Hypotheses:
    (assert CASE1B)
    ; Conclusion:
    (assert (not (and (= s y) (fp.eq e x))))
    (check-sat)
(pop 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; CASE 2: ADDENDS ARE 1-SEPARATED

; Theorem: If e_x - (p + 1) == e_y and s_x == s_y, then s === x and e == y.

(push 1)
    ; Hypotheses:
    (assert CASE2AS)
    ; Conclusion:
    (assert (not (and (= s x) (fp.eq e y))))
    (check-sat)
(pop 1)

; Theorem: If e_x == e_y - (p + 1) and s_x == s_y, then s === y and e == x.

(push 1)
    ; Hypotheses:
    (assert CASE2BS)
    ; Conclusion:
    (assert (not (and (= s y) (fp.eq e x))))
    (check-sat)
(pop 1)

; Theorem: If e_x - (p + 1) == e_y, s_x != s_y, and n_x != 0,
; then s === x and e == y.

(push 1)
    ; Hypotheses:
    (assert CASE2AD_N)
    ; Conclusion:
    (assert (not (and (= s x) (fp.eq e y))))
    (check-sat)
(pop 1)

; Theorem: If e_x == e_y - (p + 1), s_x != s_y, and n_y != 0,
; then s === y and e == x.

(push 1)
    ; Hypotheses:
    (assert CASE2BD_N)
    ; Conclusion:
    (assert (not (and (= s y) (fp.eq e x))))
    (check-sat)
(pop 1)

; Theorem: If e_x - (p + 1) == e_y, s_x != s_y, n_x == 0, and n_y == 0,
; then s === x and e == y.

(push 1)
    ; Hypotheses:
    (assert CASE2AD_ZZ)
    ; Conclusion:
    (assert (not (and (= s x) (fp.eq e y))))
    (check-sat)
(pop 1)

; Theorem: If e_x == e_y - (p + 1), s_x != s_y, n_x == 0, and n_y == 0,
; then s === y and e == x.

(push 1)
    ; Hypotheses:
    (assert CASE2BD_ZZ)
    ; Conclusion:
    (assert (not (and (= s y) (fp.eq e x))))
    (check-sat)
(pop 1)

; Theorem: If e_x - (p + 1) == e_y, s_x != s_y, n_x == 0, n_y != 0,
; and y is not subnormal, then s is the immediate predecessor of x
; (which means s_s == s_x, e_s == e_x - 1, and o_s == p - 1) and e_e < e_y.

(push 1)
    ; Hypotheses:
    (assert CASE2AD_ZN)
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
    (assert CASE2BD_ZN)
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
    (assert CASE3AS)
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
    (assert CASE3BS)
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
    (assert CASE3AS)
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
    (assert CASE3BS)
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
    (assert CASE3AD)
    ; Conclusion:
    (assert (not (and (= s_s s_x)
                      (or (= e_s e_x) (= e_s (bvsub e_x #x0001))))))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert CASE3BD)
    ; Conclusion:
    (assert (not (and (= s_s s_y)
                      (or (= e_s e_y) (= e_s (bvsub e_y #x0001))))))
    (check-sat)
(pop 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; CASE 4: ADDENDS PARTIALLY OVERLAP

; Theorem: If e_x - p < e_y < e_x and s_x == s_y, then s_s == s_x == s_y and
; e_s == e_x or e_s == e_x = 1.

(push 1)
    ; Hypotheses:
    (assert CASE4AS)
    ; Conclusion:
    (assert (not (and (= s_s s_x)
                      (or (= e_s e_x) (= e_s (bvadd e_x #x0001))))))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert CASE4BS)
    ; Conclusion:
    (assert (not (and (= s_s s_y)
                      (or (= e_s e_y) (= e_s (bvadd e_y #x0001))))))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert CASE4AD)
    ; Conclusion:
    (assert (not (and (= s_s s_x)
                      (bvule e_s e_x))))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert CASE4BD)
    ; Conclusion:
    (assert (not (and (= s_s s_y)
                      (bvule e_s e_y))))
    (check-sat)
(pop 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; CASE 5: ADDENDS FULLY OVERLAP

; Theorem: If e_x == e_y, s_x == s_y, x and y are nonzero with different LSBs,
; and none of x, y, or e are subnormal, then s_s == s_x == s_y,
; e_s == e_x + 1 == e_y + 1, and e is a nonzero power of two.

; The sign of e is unpredictable in this case,
; depending on round-to-even tiebreaking for s.

(push 1)
    ; Hypotheses:
    (assert CASE5S_X)
    (assert (not (fp.isSubnormal x)))
    (assert (not (fp.isSubnormal y)))
    (assert (not (fp.isSubnormal e)))
    ; Conclusion:
    (assert (not (and (= s_s s_x)
                      (= s_s s_y)
                      (= e_s (bvadd e_x #x0001))
                      (= e_s (bvadd e_y #x0001))
                      ; I think the following statements are true,
                      ; but they take a very long time to verify.
                      ; (or (bvuge o_s o_x) (bvuge o_s o_y))
                      ; (or (bvuge z_s z_x) (bvuge z_s z_y))
                      (= e_e (bvsub e_x (bvsub p #x0001)))
                      (= e_e (bvsub e_y (bvsub p #x0001)))
                      (= n_e #x0000))))
    (check-sat)
(pop 1)

; Theorem: If e_x == e_y, s_x == s_y, x and y are nonzero with the same LSB,
; and none of x, y, or e are subnormal, then s_s == s_x == s_y,
; e_s == e_x + 1 == e_y + 1, and e is zero.

(push 1)
    ; Hypotheses:
    (assert CASE5S_N)
    (assert (not (fp.isSubnormal x)))
    (assert (not (fp.isSubnormal y)))
    (assert (not (fp.isSubnormal e)))
    ; Conclusion:
    (assert (not (and (= s_s s_x)
                      (= s_s s_y)
                      (= e_s (bvadd e_x #x0001))
                      (= e_s (bvadd e_y #x0001))
                      ; I think the following statements are true,
                      ; but they take a very long time to verify.
                      ; (or (bvuge o_s o_x) (bvuge o_s o_y))
                      ; (or (bvuge z_s z_x) (bvuge z_s z_y))
                      (fp.isZero e))))
    (check-sat)
(pop 1)

; Theorem: If e_x == e_y, s_x != s_y, x and y are nonzero and not subnormal,
; then e_s < e_x == e_y and e is zero.

(push 1)
    ; Hypotheses:
    (assert CASE5D)
    (assert (not (fp.isSubnormal x)))
    (assert (not (fp.isSubnormal y)))
    (assert (not (fp.isSubnormal s)))
    ; Conclusion:
    (assert (not (and (or (fp.isZero s)
                          (bvult e_s (bvsub e_x o_x))
                          (bvult e_s (bvsub e_y o_y)))
                      (or (fp.isZero s)
                          (bvult e_s (bvsub e_x z_x))
                          (bvult e_s (bvsub e_y z_y)))
                      (fp.isZero e))))
    (check-sat)
(pop 1)
