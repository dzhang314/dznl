(set-logic QF_FP)

(declare-const x Float32)
(declare-const y Float32)

(define-fun sum () Float32 (fp.add RNE x y))
(define-fun x_prime () Float32 (fp.sub RNE sum y))
(define-fun y_prime () Float32 (fp.sub RNE sum x_prime))
(define-fun x_err () Float32 (fp.sub RNE x x_prime))
(define-fun y_err () Float32 (fp.sub RNE y y_prime))
(define-fun err () Float32 (fp.add RNE x_err y_err))

(push 1)
    (assert (fp.gt (fp.abs err) (fp.mul RNE (fp #b0 #b01100110 #b11111111111111111111111) (fp.abs sum))))
    (check-sat)
    (get-model)
(pop 1)

(push 1)
    (assert (fp.gt (fp.abs err) (fp.mul RNE (fp #b0 #b01100111 #b00000000000000000000000) (fp.abs sum))))
    (check-sat)
(pop 1)
