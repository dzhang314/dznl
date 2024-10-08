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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Theorem: If e_x > e_y + 54, then s === x.

(push 1)
    ; Hypotheses:
    (assert (bvugt e_x (bvadd e_y #x0036)))
    ; Conclusion:
    (assert (not (= s x)))
    (check-sat)
(pop 1)

; Theorem: If e_x + 54 < e_y, then s === y.

(push 1)
    ; Hypotheses:
    (assert (bvult (bvadd e_x #x0036) e_y))
    ; Conclusion:
    (assert (not (= s y)))
    (check-sat)
(pop 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Theorem: e_s <= e_max + 1.

(push 1)
    ; Conclusion:
    (assert (not (bvule e_s (bvadd e_max #x0001))))
    (check-sat)
(pop 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Theorem: s == 0 or e_s >= e_min - 52.

(push 1)
    ; Conclusion:
    (assert (not (or (fp.isZero s) (bvuge e_s (bvsub e_min #x0034)))))
    (check-sat)
(pop 1)

; Theorem: s == 0 or e_s >= e_max - 53.

(push 1)
    ; Conclusion:
    (assert (not (or (fp.isZero s) (bvuge e_s (bvsub e_max #x0035)))))
    (check-sat)
(pop 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Theorem: If s is not subnormal and e_s < e_max, then
; the final e_max - e_s - 1 bits of s_mantissa are zero.

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0002)))
    ; Conclusion:
    (assert (not (= ((_ extract 0 0) s_mantissa) #b0)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0003)))
    ; Conclusion:
    (assert (not (= ((_ extract 1 0) s_mantissa) #b00)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0004)))
    ; Conclusion:
    (assert (not (= ((_ extract 2 0) s_mantissa) #b000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0005)))
    ; Conclusion:
    (assert (not (= ((_ extract 3 0) s_mantissa) #b0000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0006)))
    ; Conclusion:
    (assert (not (= ((_ extract 4 0) s_mantissa) #b00000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0007)))
    ; Conclusion:
    (assert (not (= ((_ extract 5 0) s_mantissa) #b000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0008)))
    ; Conclusion:
    (assert (not (= ((_ extract 6 0) s_mantissa) #b0000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0009)))
    ; Conclusion:
    (assert (not (= ((_ extract 7 0) s_mantissa) #b00000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x000A)))
    ; Conclusion:
    (assert (not (= ((_ extract 8 0) s_mantissa) #b000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x000B)))
    ; Conclusion:
    (assert (not (= ((_ extract 9 0) s_mantissa) #b0000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x000C)))
    ; Conclusion:
    (assert (not (= ((_ extract 10 0) s_mantissa) #b00000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x000D)))
    ; Conclusion:
    (assert (not (= ((_ extract 11 0) s_mantissa) #b000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x000E)))
    ; Conclusion:
    (assert (not (= ((_ extract 12 0) s_mantissa) #b0000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x000F)))
    ; Conclusion:
    (assert (not (= ((_ extract 13 0) s_mantissa) #b00000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0010)))
    ; Conclusion:
    (assert (not (= ((_ extract 14 0) s_mantissa) #b000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0011)))
    ; Conclusion:
    (assert (not (= ((_ extract 15 0) s_mantissa) #b0000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0012)))
    ; Conclusion:
    (assert (not (= ((_ extract 16 0) s_mantissa) #b00000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0013)))
    ; Conclusion:
    (assert (not (= ((_ extract 17 0) s_mantissa) #b000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0014)))
    ; Conclusion:
    (assert (not (= ((_ extract 18 0) s_mantissa) #b0000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0015)))
    ; Conclusion:
    (assert (not (= ((_ extract 19 0) s_mantissa) #b00000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0016)))
    ; Conclusion:
    (assert (not (= ((_ extract 20 0) s_mantissa) #b000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0017)))
    ; Conclusion:
    (assert (not (= ((_ extract 21 0) s_mantissa) #b0000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0018)))
    ; Conclusion:
    (assert (not (= ((_ extract 22 0) s_mantissa) #b00000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0019)))
    ; Conclusion:
    (assert (not (= ((_ extract 23 0) s_mantissa) #b000000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x001A)))
    ; Conclusion:
    (assert (not (= ((_ extract 24 0) s_mantissa)
                    #b0000000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x001B)))
    ; Conclusion:
    (assert (not (= ((_ extract 25 0) s_mantissa)
                    #b00000000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x001C)))
    ; Conclusion:
    (assert (not (= ((_ extract 26 0) s_mantissa)
                    #b000000000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x001D)))
    ; Conclusion:
    (assert (not (= ((_ extract 27 0) s_mantissa)
                    #b0000000000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x001E)))
    ; Conclusion:
    (assert (not (= ((_ extract 28 0) s_mantissa)
                    #b00000000000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x001F)))
    ; Conclusion:
    (assert (not (= ((_ extract 29 0) s_mantissa)
                    #b000000000000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0020)))
    ; Conclusion:
    (assert (not (= ((_ extract 30 0) s_mantissa)
                    #b0000000000000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0021)))
    ; Conclusion:
    (assert (not (= ((_ extract 31 0) s_mantissa)
                    #b00000000000000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0022)))
    ; Conclusion:
    (assert (not (= ((_ extract 32 0) s_mantissa)
                    #b000000000000000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0023)))
    ; Conclusion:
    (assert (not (= ((_ extract 33 0) s_mantissa)
                    #b0000000000000000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0024)))
    ; Conclusion:
    (assert (not (= ((_ extract 34 0) s_mantissa)
                    #b00000000000000000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0025)))
    ; Conclusion:
    (assert (not (= ((_ extract 35 0) s_mantissa)
                    #b000000000000000000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0026)))
    ; Conclusion:
    (assert (not (= ((_ extract 36 0) s_mantissa)
                    #b0000000000000000000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0027)))
    ; Conclusion:
    (assert (not (= ((_ extract 37 0) s_mantissa)
                    #b00000000000000000000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0028)))
    ; Conclusion:
    (assert (not (= ((_ extract 38 0) s_mantissa)
                    #b000000000000000000000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0029)))
    ; Conclusion:
    (assert (not (= ((_ extract 39 0) s_mantissa)
                    #b0000000000000000000000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x002A)))
    ; Conclusion:
    (assert (not (= ((_ extract 40 0) s_mantissa)
                    #b00000000000000000000000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x002B)))
    ; Conclusion:
    (assert (not (= ((_ extract 41 0) s_mantissa)
                    #b000000000000000000000000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x002C)))
    ; Conclusion:
    (assert (not (= ((_ extract 42 0) s_mantissa)
                    #b0000000000000000000000000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x002D)))
    ; Conclusion:
    (assert (not (= ((_ extract 43 0) s_mantissa)
                    #b00000000000000000000000000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x002E)))
    ; Conclusion:
    (assert (not (= ((_ extract 44 0) s_mantissa)
                    #b000000000000000000000000000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x002F)))
    ; Conclusion:
    (assert (not (= ((_ extract 45 0) s_mantissa)
                    #b0000000000000000000000000000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0030)))
    ; Conclusion:
    (assert (not (= ((_ extract 46 0) s_mantissa)
                    #b00000000000000000000000000000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0031)))
    ; Conclusion:
    (assert (not (= ((_ extract 47 0) s_mantissa)
                    #b000000000000000000000000000000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0032)))
    ; Conclusion:
    (assert (not (= ((_ extract 48 0) s_mantissa)
                    #b0000000000000000000000000000000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0033)))
    ; Conclusion:
    (assert (not (= ((_ extract 49 0) s_mantissa)
                    #b00000000000000000000000000000000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0034)))
    ; Conclusion:
    (assert (not (= ((_ extract 50 0) s_mantissa)
                    #b000000000000000000000000000000000000000000000000000)))
    (check-sat)
(pop 1)

(push 1)
    ; Hypotheses:
    (assert (not (fp.isSubnormal s)))
    (assert (= e_s (bvsub e_max #x0035)))
    ; Conclusion:
    (assert (not (= ((_ extract 51 0) s_mantissa)
                    #b0000000000000000000000000000000000000000000000000000)))
    (check-sat)
(pop 1)

; Theorem: If e_s == e_max - 53, then s is 0 or a power of 2.

(define-fun isPow2 ((x (_ BitVec 52))) Bool
    (= (bvand x (bvsub x #x0000000000001)) #x0000000000000))

(push 1)
    ; Hypotheses:
    (assert (= e_s (bvsub e_max #x0035)))
    ; Conclusion:
    (assert (not  (or (= s_mantissa #x0000000000000)
                      (and (= s_exponent #b00000000000) (isPow2 s_mantissa)))))
    (check-sat)
(pop 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
