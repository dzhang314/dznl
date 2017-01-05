#ifndef DZNL_CONSTANTS_H
#define DZNL_CONSTANTS_H

namespace dznl {

    namespace constants {

        // =================================================== ALGEBRAIC NUMBERS

        const double sqrt_2 = 1.4142135623730950488;
        const double sqrt_3 = 1.7320508075688772935;
        const double cbrt_2 = 1.2599210498948731648;
        const double cbrt_3 = 1.4422495703074083823;
        const double golden_phi = 1.6180339887498948482;

        // =========================== COMMON VALUES OF TRANSCENDENTAL FUNCTIONS

        const double log_2 = 0.69314718055994530942;
        const double log_10 = 2.3025850929940456840;

        // ============================================ TRANSCENDENTAL CONSTANTS

        const double pi = 3.1415926535897932385;
        const double tau = 6.2831853071795864769;
        const double e = 2.7182818284590452354;

        /* Technically it isn't proven whether these two are irrational,
         * let alone transcendental, but they almost certainly are. */
        const double euler_gamma = 0.57721566490153286061;
        const double catalan_g = 0.91596559417721901505;

    } // namespace constants

} // namespace dznl

#endif // DZNL_CONSTANTS_H
