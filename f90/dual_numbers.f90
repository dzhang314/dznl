module dual_numbers

    use constants, only : rk
    implicit none
    private

    type, public :: dual_t
        real(rk) :: re, du
    end type dual_t
    
    ! =========================================== dual number operator overloads

    public :: assignment (=)
    interface assignment (=)
        module procedure mov_real_dual, mov_dual_real
    end interface assignment (=)

    public :: operator (+)
    interface operator (+)
        module procedure pos_dual, add_real_dual, add_dual_real, add_dual_dual
    end interface operator (+)

    public :: operator (-)
    interface operator (-)
        module procedure neg_dual, sub_real_dual, sub_dual_real, sub_dual_dual
    end interface operator (-)

    public :: operator (*)
    interface operator (*)
        module procedure mul_real_dual, mul_dual_real, mul_dual_dual
    end interface operator (*)

    public :: operator (/)
    interface operator (/)
        module procedure div_real_dual, div_dual_real, div_dual_dual
    end interface operator (/)

    ! TODO: Add operator overload for exponentiation operator (**).
    ! TODO: Add elemental interface overloads for scalar intrinsic functions,
    !       e.g., sin, cos, tan, log, exp, bessel_j0, etc.
    ! TODO: Add interface overloads for intrinsic array functions,
    !       e.g., dot_product.

    public :: sum
    interface sum
        module procedure sum_dual
    end interface sum

    public :: dot_product
    interface dot_product
        module procedure dot_product_real_dual, dot_product_dual_real, &
                       & dot_product_dual_dual
    end interface dot_product

contains

    ! ========================================= dual number conversion operators

    elemental subroutine mov_real_dual(c, a)
        real(rk), intent(out) :: c
        type(dual_t), intent(in) :: a
        c = a%re
    end subroutine mov_real_dual

    elemental subroutine mov_dual_real(c, a)
        type(dual_t), intent(out) :: c
        real(rk), intent(in) :: a
        c%re = a
        c%du = 0.0_rk
    end subroutine mov_dual_real

    ! ============================================== dual number unary operators

    type(dual_t) elemental function pos_dual(a) result (c)
        type(dual_t), intent(in) :: a
        c%re = +a%re
        c%du = +a%du
    end function pos_dual

    type(dual_t) elemental function neg_dual(a) result (c)
        type(dual_t), intent(in) :: a
        c%re = -a%re
        c%du = -a%du
    end function neg_dual

    ! =========================================== dual number addition operators

    type(dual_t) elemental function add_real_dual(a, b) result (c)
        real(rk), intent(in) :: a
        type(dual_t), intent(in) :: b
        c%re = a + b%re
        c%du = b%du
    end function add_real_dual

    type(dual_t) elemental function add_dual_real(a, b) result (c)
        type(dual_t), intent(in) :: a
        real(rk), intent(in) :: b
        c%re = a%re + b
        c%du = a%du
    end function add_dual_real

    type(dual_t) elemental function add_dual_dual(a, b) result (c)
        type(dual_t), intent(in) :: a, b
        c%re = a%re + b%re
        c%du = a%du + b%du
    end function add_dual_dual

    ! ======================================== dual number subtraction operators

    type(dual_t) elemental function sub_real_dual(a, b) result (c)
        real(rk), intent(in) :: a
        type(dual_t), intent(in) :: b
        c%re = a - b%re
        c%du = -b%du
    end function sub_real_dual

    type(dual_t) elemental function sub_dual_real(a, b) result (c)
        type(dual_t), intent(in) :: a
        real(rk), intent(in) :: b
        c%re = a%re - b
        c%du = a%du
    end function sub_dual_real

    type(dual_t) elemental function sub_dual_dual(a, b) result (c)
        type(dual_t), intent(in) :: a, b
        c%re = a%re - b%re
        c%du = a%du - b%du
    end function sub_dual_dual

    ! ===================================== dual number multiplication operators

    type(dual_t) elemental function mul_real_dual(a, b) result (c)
        real(rk), intent(in) :: a
        type(dual_t), intent(in) :: b
        c%re = a * b%re
        c%du = a * b%du
    end function mul_real_dual

    type(dual_t) elemental function mul_dual_real(a, b) result (c)
        type(dual_t), intent(in) :: a
        real(rk), intent(in) :: b
        c%re = a%re * b
        c%du = a%du * b
    end function mul_dual_real

    type(dual_t) elemental function mul_dual_dual(a, b) result (c)
        type(dual_t), intent(in) :: a, b
        c%re = a%re * b%re
        c%du = a%re * b%du + a%du * b%re
    end function mul_dual_dual

    ! =========================================== dual number division operators

    type(dual_t) elemental function div_real_dual(a, b) result (c)
        real(rk), intent(in) :: a
        type(dual_t), intent(in) :: b
        c%re = a / b%re
        c%du = -c%re * b%du / b%re
    end function div_real_dual

    type(dual_t) elemental function div_dual_real(a, b) result (c)
        type(dual_t), intent(in) :: a
        real(rk), intent(in) :: b
        c%re = a%re / b
        c%du = a%du / b
    end function div_dual_real

    type(dual_t) elemental function div_dual_dual(a, b) result (c)
        type(dual_t), intent(in) :: a, b
        c%re = a%re / b%re
        c%du = (a%du - c%re * b%du) / b%re
    end function div_dual_dual

    ! ============================================= dual number array intrinsics

    type(dual_t) pure function sum_dual(a)
        type(dual_t), intent(in) :: a(:)
        integer :: i
        sum_dual = 0.0_rk
        do i = 1, size(a)
            sum_dual = sum_dual + a(i)
        end do
    end function sum_dual

    type(dual_t) pure function dot_product_real_dual(a, b)
        real(rk), intent(in) :: a(:)
        type(dual_t), intent(in) :: b(:)
        dot_product_real_dual = sum(a * b)
    end function dot_product_real_dual

    type(dual_t) pure function dot_product_dual_real(a, b)
        type(dual_t), intent(in) :: a(:)
        real(rk), intent(in) :: b(:)
        dot_product_dual_real = sum(a * b)
    end function dot_product_dual_real

    type(dual_t) pure function dot_product_dual_dual(a, b)
        type(dual_t), intent(in) :: a(:), b(:)
        dot_product_dual_dual = sum(a * b)
    end function dot_product_dual_dual

end module dual_numbers
