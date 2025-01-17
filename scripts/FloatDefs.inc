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

(define-fun two-sum ((x FLOAT) (y FLOAT)) FLOAT
    (fp.add RNE x y))

(define-fun two-sum-err ((x FLOAT) (y FLOAT)) FLOAT
    (let ((s (fp.add RNE x y)))
    (let ((x_eff (fp.sub RNE s y)))
    (let ((y_eff (fp.sub RNE s x_eff)))
    (fp.add RNE (fp.sub RNE x x_eff) (fp.sub RNE y y_eff))))))

(define-fun apply-bias ((e EXPONENT)) INT
    (bvsub (concat PADDING e) BIAS_INT))
