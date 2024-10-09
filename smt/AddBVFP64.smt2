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

; We extend e_x, e_y, and e_s in order to perform arithmetic without overflow.

(define-fun e_x () (_ BitVec 16)
    (bvadd #b0111110000000000 (concat #b00000 x_exponent)))
(define-fun e_y () (_ BitVec 16)
    (bvadd #b0111110000000000 (concat #b00000 y_exponent)))
(define-fun e_s () (_ BitVec 16)
    (bvadd #b0111110000000000 (concat #b00000 s_exponent)))

; Let e_min and e_max denote min(e_x, e_y) and max(e_x, e_y), respectively.

(define-fun e_min () (_ BitVec 16) (ite (bvult e_x e_y) e_x e_y))
(define-fun e_max () (_ BitVec 16) (ite (bvugt e_x e_y) e_x e_y))

; Let nnzb_x denote the number of nonzero leading bits in the mantissa of x.
; We define nnzb_y and nnzb_s similarly.

(define-fun nnzb ((m (_ BitVec 52))) (_ BitVec 16)
    (ite (= ((_ extract 51 0) m) #b0000000000000000000000000000000000000000000000000000) #x0000
    (ite (= ((_ extract 50 0) m) #b000000000000000000000000000000000000000000000000000) #x0001
    (ite (= ((_ extract 49 0) m) #b00000000000000000000000000000000000000000000000000) #x0002
    (ite (= ((_ extract 48 0) m) #b0000000000000000000000000000000000000000000000000) #x0003
    (ite (= ((_ extract 47 0) m) #b000000000000000000000000000000000000000000000000) #x0004
    (ite (= ((_ extract 46 0) m) #b00000000000000000000000000000000000000000000000) #x0005
    (ite (= ((_ extract 45 0) m) #b0000000000000000000000000000000000000000000000) #x0006
    (ite (= ((_ extract 44 0) m) #b000000000000000000000000000000000000000000000) #x0007
    (ite (= ((_ extract 43 0) m) #b00000000000000000000000000000000000000000000) #x0008
    (ite (= ((_ extract 42 0) m) #b0000000000000000000000000000000000000000000) #x0009
    (ite (= ((_ extract 41 0) m) #b000000000000000000000000000000000000000000) #x000A
    (ite (= ((_ extract 40 0) m) #b00000000000000000000000000000000000000000) #x000B
    (ite (= ((_ extract 39 0) m) #b0000000000000000000000000000000000000000) #x000C
    (ite (= ((_ extract 38 0) m) #b000000000000000000000000000000000000000) #x000D
    (ite (= ((_ extract 37 0) m) #b00000000000000000000000000000000000000) #x000E
    (ite (= ((_ extract 36 0) m) #b0000000000000000000000000000000000000) #x000F
    (ite (= ((_ extract 35 0) m) #b000000000000000000000000000000000000) #x0010
    (ite (= ((_ extract 34 0) m) #b00000000000000000000000000000000000) #x0011
    (ite (= ((_ extract 33 0) m) #b0000000000000000000000000000000000) #x0012
    (ite (= ((_ extract 32 0) m) #b000000000000000000000000000000000) #x0013
    (ite (= ((_ extract 31 0) m) #b00000000000000000000000000000000) #x0014
    (ite (= ((_ extract 30 0) m) #b0000000000000000000000000000000) #x0015
    (ite (= ((_ extract 29 0) m) #b000000000000000000000000000000) #x0016
    (ite (= ((_ extract 28 0) m) #b00000000000000000000000000000) #x0017
    (ite (= ((_ extract 27 0) m) #b0000000000000000000000000000) #x0018
    (ite (= ((_ extract 26 0) m) #b000000000000000000000000000) #x0019
    (ite (= ((_ extract 25 0) m) #b00000000000000000000000000) #x001A
    (ite (= ((_ extract 24 0) m) #b0000000000000000000000000) #x001B
    (ite (= ((_ extract 23 0) m) #b000000000000000000000000) #x001C
    (ite (= ((_ extract 22 0) m) #b00000000000000000000000) #x001D
    (ite (= ((_ extract 21 0) m) #b0000000000000000000000) #x001E
    (ite (= ((_ extract 20 0) m) #b000000000000000000000) #x001F
    (ite (= ((_ extract 19 0) m) #b00000000000000000000) #x0020
    (ite (= ((_ extract 18 0) m) #b0000000000000000000) #x0021
    (ite (= ((_ extract 17 0) m) #b000000000000000000) #x0022
    (ite (= ((_ extract 16 0) m) #b00000000000000000) #x0023
    (ite (= ((_ extract 15 0) m) #b0000000000000000) #x0024
    (ite (= ((_ extract 14 0) m) #b000000000000000) #x0025
    (ite (= ((_ extract 13 0) m) #b00000000000000) #x0026
    (ite (= ((_ extract 12 0) m) #b0000000000000) #x0027
    (ite (= ((_ extract 11 0) m) #b000000000000) #x0028
    (ite (= ((_ extract 10 0) m) #b00000000000) #x0029
    (ite (= ((_ extract 9 0) m) #b0000000000) #x002A
    (ite (= ((_ extract 8 0) m) #b000000000) #x002B
    (ite (= ((_ extract 7 0) m) #b00000000) #x002C
    (ite (= ((_ extract 6 0) m) #b0000000) #x002D
    (ite (= ((_ extract 5 0) m) #b000000) #x002E
    (ite (= ((_ extract 4 0) m) #b00000) #x002F
    (ite (= ((_ extract 3 0) m) #b0000) #x0030
    (ite (= ((_ extract 2 0) m) #b000) #x0031
    (ite (= ((_ extract 1 0) m) #b00) #x0032
    (ite (= ((_ extract 0 0) m) #b0) #x0033
    #x0034)))))))))))))))))))))))))))))))))))))))))))))))))))))

(define-fun nnzb_x () (_ BitVec 16) (nnzb x_mantissa))
(define-fun nnzb_y () (_ BitVec 16) (nnzb y_mantissa))
(define-fun nnzb_s () (_ BitVec 16) (nnzb s_mantissa))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; ZERO PROPERTIES

; Theorem: If x == 0 and y == 0, then s == 0.

(push 1)
    ; Hypotheses:
    (assert (fp.isZero x))
    (assert (fp.isZero y))
    ; Conclusion:
    (assert (not (fp.isZero s)))
    (check-sat)
(pop 1)

; Theorem: If x == 0, then s == y or s === y.

(push 1)
    ; Hypotheses:
    (assert (fp.isZero x))
    ; Conclusion:
    (assert (not (or (fp.eq s y) (= s y))))
    (check-sat)
(pop 1)

; Theorem: If y == 0, then s == x or s === x.

(push 1)
    ; Hypotheses:
    (assert (fp.isZero y))
    ; Conclusion:
    (assert (not (or (fp.eq s x) (= s x))))
    (check-sat)
(pop 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; EXPONENT PROPERTIES

; Theorem: If e_x > e_y + p + 1, then s === x.

(push 1)
    ; Hypotheses:
    (assert (bvugt e_x (bvadd e_y #x0036)))
    ; Conclusion:
    (assert (not (= s x)))
    (check-sat)
(pop 1)

; Theorem: If e_x + p + 1 < e_y, then s === y.

(push 1)
    ; Hypotheses:
    (assert (bvult (bvadd e_x #x0036) e_y))
    ; Conclusion:
    (assert (not (= s y)))
    (check-sat)
(pop 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; EXPONENT UPPER BOUNDS

; Theorem: e_s <= e_max + 1.

(push 1)
    ; Conclusion:
    (assert (not (bvule e_s (bvadd e_max #x0001))))
    (check-sat)
(pop 1)

; Theorem: If s_x != s_y, then e_s <= e_max.

(push 1)
    ; Hypotheses:
    (assert (not (= x_sign y_sign)))
    ; Conclusion:
    (assert (not (bvule e_s e_max)))
    (check-sat)
(pop 1)

; Theorem: If e_x - nnzb_x > e_y + 1, then e_s <= e_x.
(push 1)
    ; Hypotheses:
    (assert (bvugt (bvsub e_x nnzb_x) (bvadd e_y #x0001)))
    ; Conclusion:
    (assert (not (bvule e_s e_x)))
    (check-sat)
(pop 1)

; Theorem: If e_x + 1 < e_y - nnzb_y, then e_s <= e_y.
(push 1)
    ; Hypotheses:
    (assert (bvult (bvadd e_x #x0001) (bvsub e_y nnzb_y)))
    ; Conclusion:
    (assert (not (bvule e_s e_y)))
    (check-sat)
(pop 1)

; Theorem: If e_x - nnzb_x > e_y and e_x - p < e_y - nnzb_y,
; then e_s <= e_x.
(push 1)
    ; Hypotheses:
    (assert (bvugt (bvsub e_x nnzb_x) e_y))
    (assert (bvult (bvsub e_x #x0035) (bvsub e_y nnzb_y)))
    ; Conclusion:
    (assert (not (bvule e_s e_x)))
    (check-sat)
(pop 1)

; Theorem: If e_x < e_y - nnzb_y and e_x - nnzb_x > e_y - p, then e_s <= e_y.
(push 1)
    ; Hypotheses:
    (assert (bvult e_x (bvsub e_y nnzb_y)))
    (assert (bvugt (bvsub e_x nnzb_x) (bvsub e_y #x0035)))
    ; Conclusion:
    (assert (not (bvule e_s e_y)))
    (check-sat)
(pop 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; EXPONENT LOWER BOUNDS

; Theorem: s == 0 or e_s >= e_min - (p - 1).

(push 1)
    ; Conclusion:
    (assert (not (or (fp.isZero s) (bvuge e_s (bvsub e_min #x0034)))))
    (check-sat)
(pop 1)

; Theorem: s == 0 or e_s >= e_max - p.

(push 1)
    ; Conclusion:
    (assert (not (or (fp.isZero s) (bvuge e_s (bvsub e_max #x0035)))))
    (check-sat)
(pop 1)

; Theorem: If e_x > e_y + nnzb_y, then e_s >= e_y + nnzb_y.

(push 1)
    ; Hypotheses:
    (assert (bvugt e_x (bvadd e_y nnzb_y)))
    ; Conclusion:
    (assert (not (bvuge e_s (bvadd e_y nnzb_y))))
    (check-sat)
(pop 1)

; Theorem: If e_x + nnzb_x < e_y, then e_s >= e_x + nnzb_x.
(push 1)
    ; Hypotheses:
    (assert (bvult (bvadd e_x nnzb_x) e_y))
    ; Conclusion:
    (assert (not (bvuge e_s (bvadd e_x nnzb_x))))
    (check-sat)
(pop 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; NNZB UPPER BOUNDS

; Theorem: If s is not zero or subnormal, then e_s - nnzb_s >= e_max - p.

(push 1)
    ; Hypotheses:
    (assert (not (fp.isZero s)))
    (assert (not (fp.isSubnormal s)))
    ; Conclusion:
    (assert (not (bvuge (bvsub e_s nnzb_s) (bvsub e_max #x0035))))
    (check-sat)
(pop 1)
