#ifndef DZNL_HYPERDUAL6_H
#define DZNL_HYPERDUAL6_H

struct hyperdual6 {
    double real;
    double dual1;
    double dual2;
    double dual12;
    double dual3;
    double dual13;
    double dual23;
    double dual123;
    double dual4;
    double dual14;
    double dual24;
    double dual124;
    double dual34;
    double dual134;
    double dual234;
    double dual1234;
    double dual5;
    double dual15;
    double dual25;
    double dual125;
    double dual35;
    double dual135;
    double dual235;
    double dual1235;
    double dual45;
    double dual145;
    double dual245;
    double dual1245;
    double dual345;
    double dual1345;
    double dual2345;
    double dual12345;
    double dual6;
    double dual16;
    double dual26;
    double dual126;
    double dual36;
    double dual136;
    double dual236;
    double dual1236;
    double dual46;
    double dual146;
    double dual246;
    double dual1246;
    double dual346;
    double dual1346;
    double dual2346;
    double dual12346;
    double dual56;
    double dual156;
    double dual256;
    double dual1256;
    double dual356;
    double dual1356;
    double dual2356;
    double dual12356;
    double dual456;
    double dual1456;
    double dual2456;
    double dual12456;
    double dual3456;
    double dual13456;
    double dual23456;
    double dual123456;
};

hyperdual6 operator+(const hyperdual6 &x) {
    return {
            .real = +x.real,
            .dual1 = +x.dual1,
            .dual2 = +x.dual2,
            .dual12 = +x.dual12,
            .dual3 = +x.dual3,
            .dual13 = +x.dual13,
            .dual23 = +x.dual23,
            .dual123 = +x.dual123,
            .dual4 = +x.dual4,
            .dual14 = +x.dual14,
            .dual24 = +x.dual24,
            .dual124 = +x.dual124,
            .dual34 = +x.dual34,
            .dual134 = +x.dual134,
            .dual234 = +x.dual234,
            .dual1234 = +x.dual1234,
            .dual5 = +x.dual5,
            .dual15 = +x.dual15,
            .dual25 = +x.dual25,
            .dual125 = +x.dual125,
            .dual35 = +x.dual35,
            .dual135 = +x.dual135,
            .dual235 = +x.dual235,
            .dual1235 = +x.dual1235,
            .dual45 = +x.dual45,
            .dual145 = +x.dual145,
            .dual245 = +x.dual245,
            .dual1245 = +x.dual1245,
            .dual345 = +x.dual345,
            .dual1345 = +x.dual1345,
            .dual2345 = +x.dual2345,
            .dual12345 = +x.dual12345,
            .dual6 = +x.dual6,
            .dual16 = +x.dual16,
            .dual26 = +x.dual26,
            .dual126 = +x.dual126,
            .dual36 = +x.dual36,
            .dual136 = +x.dual136,
            .dual236 = +x.dual236,
            .dual1236 = +x.dual1236,
            .dual46 = +x.dual46,
            .dual146 = +x.dual146,
            .dual246 = +x.dual246,
            .dual1246 = +x.dual1246,
            .dual346 = +x.dual346,
            .dual1346 = +x.dual1346,
            .dual2346 = +x.dual2346,
            .dual12346 = +x.dual12346,
            .dual56 = +x.dual56,
            .dual156 = +x.dual156,
            .dual256 = +x.dual256,
            .dual1256 = +x.dual1256,
            .dual356 = +x.dual356,
            .dual1356 = +x.dual1356,
            .dual2356 = +x.dual2356,
            .dual12356 = +x.dual12356,
            .dual456 = +x.dual456,
            .dual1456 = +x.dual1456,
            .dual2456 = +x.dual2456,
            .dual12456 = +x.dual12456,
            .dual3456 = +x.dual3456,
            .dual13456 = +x.dual13456,
            .dual23456 = +x.dual23456,
            .dual123456 = +x.dual123456,
    };
}

hyperdual6 operator-(const hyperdual6 &x) {
    return {
            .real = -x.real,
            .dual1 = -x.dual1,
            .dual2 = -x.dual2,
            .dual12 = -x.dual12,
            .dual3 = -x.dual3,
            .dual13 = -x.dual13,
            .dual23 = -x.dual23,
            .dual123 = -x.dual123,
            .dual4 = -x.dual4,
            .dual14 = -x.dual14,
            .dual24 = -x.dual24,
            .dual124 = -x.dual124,
            .dual34 = -x.dual34,
            .dual134 = -x.dual134,
            .dual234 = -x.dual234,
            .dual1234 = -x.dual1234,
            .dual5 = -x.dual5,
            .dual15 = -x.dual15,
            .dual25 = -x.dual25,
            .dual125 = -x.dual125,
            .dual35 = -x.dual35,
            .dual135 = -x.dual135,
            .dual235 = -x.dual235,
            .dual1235 = -x.dual1235,
            .dual45 = -x.dual45,
            .dual145 = -x.dual145,
            .dual245 = -x.dual245,
            .dual1245 = -x.dual1245,
            .dual345 = -x.dual345,
            .dual1345 = -x.dual1345,
            .dual2345 = -x.dual2345,
            .dual12345 = -x.dual12345,
            .dual6 = -x.dual6,
            .dual16 = -x.dual16,
            .dual26 = -x.dual26,
            .dual126 = -x.dual126,
            .dual36 = -x.dual36,
            .dual136 = -x.dual136,
            .dual236 = -x.dual236,
            .dual1236 = -x.dual1236,
            .dual46 = -x.dual46,
            .dual146 = -x.dual146,
            .dual246 = -x.dual246,
            .dual1246 = -x.dual1246,
            .dual346 = -x.dual346,
            .dual1346 = -x.dual1346,
            .dual2346 = -x.dual2346,
            .dual12346 = -x.dual12346,
            .dual56 = -x.dual56,
            .dual156 = -x.dual156,
            .dual256 = -x.dual256,
            .dual1256 = -x.dual1256,
            .dual356 = -x.dual356,
            .dual1356 = -x.dual1356,
            .dual2356 = -x.dual2356,
            .dual12356 = -x.dual12356,
            .dual456 = -x.dual456,
            .dual1456 = -x.dual1456,
            .dual2456 = -x.dual2456,
            .dual12456 = -x.dual12456,
            .dual3456 = -x.dual3456,
            .dual13456 = -x.dual13456,
            .dual23456 = -x.dual23456,
            .dual123456 = -x.dual123456,
    };
}

hyperdual6 operator+(const hyperdual6 &x, const hyperdual6 &y) {
    return {
            .real = x.real + y.real,
            .dual1 = x.dual1 + y.dual1,
            .dual2 = x.dual2 + y.dual2,
            .dual12 = x.dual12 + y.dual12,
            .dual3 = x.dual3 + y.dual3,
            .dual13 = x.dual13 + y.dual13,
            .dual23 = x.dual23 + y.dual23,
            .dual123 = x.dual123 + y.dual123,
            .dual4 = x.dual4 + y.dual4,
            .dual14 = x.dual14 + y.dual14,
            .dual24 = x.dual24 + y.dual24,
            .dual124 = x.dual124 + y.dual124,
            .dual34 = x.dual34 + y.dual34,
            .dual134 = x.dual134 + y.dual134,
            .dual234 = x.dual234 + y.dual234,
            .dual1234 = x.dual1234 + y.dual1234,
            .dual5 = x.dual5 + y.dual5,
            .dual15 = x.dual15 + y.dual15,
            .dual25 = x.dual25 + y.dual25,
            .dual125 = x.dual125 + y.dual125,
            .dual35 = x.dual35 + y.dual35,
            .dual135 = x.dual135 + y.dual135,
            .dual235 = x.dual235 + y.dual235,
            .dual1235 = x.dual1235 + y.dual1235,
            .dual45 = x.dual45 + y.dual45,
            .dual145 = x.dual145 + y.dual145,
            .dual245 = x.dual245 + y.dual245,
            .dual1245 = x.dual1245 + y.dual1245,
            .dual345 = x.dual345 + y.dual345,
            .dual1345 = x.dual1345 + y.dual1345,
            .dual2345 = x.dual2345 + y.dual2345,
            .dual12345 = x.dual12345 + y.dual12345,
            .dual6 = x.dual6 + y.dual6,
            .dual16 = x.dual16 + y.dual16,
            .dual26 = x.dual26 + y.dual26,
            .dual126 = x.dual126 + y.dual126,
            .dual36 = x.dual36 + y.dual36,
            .dual136 = x.dual136 + y.dual136,
            .dual236 = x.dual236 + y.dual236,
            .dual1236 = x.dual1236 + y.dual1236,
            .dual46 = x.dual46 + y.dual46,
            .dual146 = x.dual146 + y.dual146,
            .dual246 = x.dual246 + y.dual246,
            .dual1246 = x.dual1246 + y.dual1246,
            .dual346 = x.dual346 + y.dual346,
            .dual1346 = x.dual1346 + y.dual1346,
            .dual2346 = x.dual2346 + y.dual2346,
            .dual12346 = x.dual12346 + y.dual12346,
            .dual56 = x.dual56 + y.dual56,
            .dual156 = x.dual156 + y.dual156,
            .dual256 = x.dual256 + y.dual256,
            .dual1256 = x.dual1256 + y.dual1256,
            .dual356 = x.dual356 + y.dual356,
            .dual1356 = x.dual1356 + y.dual1356,
            .dual2356 = x.dual2356 + y.dual2356,
            .dual12356 = x.dual12356 + y.dual12356,
            .dual456 = x.dual456 + y.dual456,
            .dual1456 = x.dual1456 + y.dual1456,
            .dual2456 = x.dual2456 + y.dual2456,
            .dual12456 = x.dual12456 + y.dual12456,
            .dual3456 = x.dual3456 + y.dual3456,
            .dual13456 = x.dual13456 + y.dual13456,
            .dual23456 = x.dual23456 + y.dual23456,
            .dual123456 = x.dual123456 + y.dual123456,
    };
}

hyperdual6 operator-(const hyperdual6 &x, const hyperdual6 &y) {
    return {
            .real = x.real - y.real,
            .dual1 = x.dual1 - y.dual1,
            .dual2 = x.dual2 - y.dual2,
            .dual12 = x.dual12 - y.dual12,
            .dual3 = x.dual3 - y.dual3,
            .dual13 = x.dual13 - y.dual13,
            .dual23 = x.dual23 - y.dual23,
            .dual123 = x.dual123 - y.dual123,
            .dual4 = x.dual4 - y.dual4,
            .dual14 = x.dual14 - y.dual14,
            .dual24 = x.dual24 - y.dual24,
            .dual124 = x.dual124 - y.dual124,
            .dual34 = x.dual34 - y.dual34,
            .dual134 = x.dual134 - y.dual134,
            .dual234 = x.dual234 - y.dual234,
            .dual1234 = x.dual1234 - y.dual1234,
            .dual5 = x.dual5 - y.dual5,
            .dual15 = x.dual15 - y.dual15,
            .dual25 = x.dual25 - y.dual25,
            .dual125 = x.dual125 - y.dual125,
            .dual35 = x.dual35 - y.dual35,
            .dual135 = x.dual135 - y.dual135,
            .dual235 = x.dual235 - y.dual235,
            .dual1235 = x.dual1235 - y.dual1235,
            .dual45 = x.dual45 - y.dual45,
            .dual145 = x.dual145 - y.dual145,
            .dual245 = x.dual245 - y.dual245,
            .dual1245 = x.dual1245 - y.dual1245,
            .dual345 = x.dual345 - y.dual345,
            .dual1345 = x.dual1345 - y.dual1345,
            .dual2345 = x.dual2345 - y.dual2345,
            .dual12345 = x.dual12345 - y.dual12345,
            .dual6 = x.dual6 - y.dual6,
            .dual16 = x.dual16 - y.dual16,
            .dual26 = x.dual26 - y.dual26,
            .dual126 = x.dual126 - y.dual126,
            .dual36 = x.dual36 - y.dual36,
            .dual136 = x.dual136 - y.dual136,
            .dual236 = x.dual236 - y.dual236,
            .dual1236 = x.dual1236 - y.dual1236,
            .dual46 = x.dual46 - y.dual46,
            .dual146 = x.dual146 - y.dual146,
            .dual246 = x.dual246 - y.dual246,
            .dual1246 = x.dual1246 - y.dual1246,
            .dual346 = x.dual346 - y.dual346,
            .dual1346 = x.dual1346 - y.dual1346,
            .dual2346 = x.dual2346 - y.dual2346,
            .dual12346 = x.dual12346 - y.dual12346,
            .dual56 = x.dual56 - y.dual56,
            .dual156 = x.dual156 - y.dual156,
            .dual256 = x.dual256 - y.dual256,
            .dual1256 = x.dual1256 - y.dual1256,
            .dual356 = x.dual356 - y.dual356,
            .dual1356 = x.dual1356 - y.dual1356,
            .dual2356 = x.dual2356 - y.dual2356,
            .dual12356 = x.dual12356 - y.dual12356,
            .dual456 = x.dual456 - y.dual456,
            .dual1456 = x.dual1456 - y.dual1456,
            .dual2456 = x.dual2456 - y.dual2456,
            .dual12456 = x.dual12456 - y.dual12456,
            .dual3456 = x.dual3456 - y.dual3456,
            .dual13456 = x.dual13456 - y.dual13456,
            .dual23456 = x.dual23456 - y.dual23456,
            .dual123456 = x.dual123456 - y.dual123456,
    };
}

hyperdual6 operator*(const hyperdual6 &x, const hyperdual6 &y) {
    return {
            .real = x.real * y.real,
            .dual1 = x.dual1 * y.real + x.real * y.dual1,
            .dual2 = x.dual2 * y.real + x.real * y.dual2,
            .dual12 = x.dual12 * y.real + x.dual2 * y.dual1 +
                      x.dual1 * y.dual2 + x.real * y.dual12,
            .dual3 = x.dual3 * y.real + x.real * y.dual3,
            .dual13 = x.dual13 * y.real + x.dual3 * y.dual1 +
                      x.dual1 * y.dual3 + x.real * y.dual13,
            .dual23 = x.dual23 * y.real + x.dual3 * y.dual2 +
                      x.dual2 * y.dual3 + x.real * y.dual23,
            .dual123 = x.dual123 * y.real + x.dual23 * y.dual1 +
                       x.dual13 * y.dual2 + x.dual3 * y.dual12 +
                       x.dual12 * y.dual3 + x.dual2 * y.dual13 +
                       x.dual1 * y.dual23 + x.real * y.dual123,
            .dual4 = x.dual4 * y.real + x.real * y.dual4,
            .dual14 = x.dual14 * y.real + x.dual4 * y.dual1 +
                      x.dual1 * y.dual4 + x.real * y.dual14,
            .dual24 = x.dual24 * y.real + x.dual4 * y.dual2 +
                      x.dual2 * y.dual4 + x.real * y.dual24,
            .dual124 = x.dual124 * y.real + x.dual24 * y.dual1 +
                       x.dual14 * y.dual2 + x.dual4 * y.dual12 +
                       x.dual12 * y.dual4 + x.dual2 * y.dual14 +
                       x.dual1 * y.dual24 + x.real * y.dual124,
            .dual34 = x.dual34 * y.real + x.dual4 * y.dual3 +
                      x.dual3 * y.dual4 + x.real * y.dual34,
            .dual134 = x.dual134 * y.real + x.dual34 * y.dual1 +
                       x.dual14 * y.dual3 + x.dual4 * y.dual13 +
                       x.dual13 * y.dual4 + x.dual3 * y.dual14 +
                       x.dual1 * y.dual34 + x.real * y.dual134,
            .dual234 = x.dual234 * y.real + x.dual34 * y.dual2 +
                       x.dual24 * y.dual3 + x.dual4 * y.dual23 +
                       x.dual23 * y.dual4 + x.dual3 * y.dual24 +
                       x.dual2 * y.dual34 + x.real * y.dual234,
            .dual1234 = x.dual1234 * y.real + x.dual234 * y.dual1 +
                        x.dual134 * y.dual2 + x.dual34 * y.dual12 +
                        x.dual124 * y.dual3 + x.dual24 * y.dual13 +
                        x.dual14 * y.dual23 + x.dual4 * y.dual123 +
                        x.dual123 * y.dual4 + x.dual23 * y.dual14 +
                        x.dual13 * y.dual24 + x.dual3 * y.dual124 +
                        x.dual12 * y.dual34 + x.dual2 * y.dual134 +
                        x.dual1 * y.dual234 + x.real * y.dual1234,
            .dual5 = x.dual5 * y.real + x.real * y.dual5,
            .dual15 = x.dual15 * y.real + x.dual5 * y.dual1 +
                      x.dual1 * y.dual5 + x.real * y.dual15,
            .dual25 = x.dual25 * y.real + x.dual5 * y.dual2 +
                      x.dual2 * y.dual5 + x.real * y.dual25,
            .dual125 = x.dual125 * y.real + x.dual25 * y.dual1 +
                       x.dual15 * y.dual2 + x.dual5 * y.dual12 +
                       x.dual12 * y.dual5 + x.dual2 * y.dual15 +
                       x.dual1 * y.dual25 + x.real * y.dual125,
            .dual35 = x.dual35 * y.real + x.dual5 * y.dual3 +
                      x.dual3 * y.dual5 + x.real * y.dual35,
            .dual135 = x.dual135 * y.real + x.dual35 * y.dual1 +
                       x.dual15 * y.dual3 + x.dual5 * y.dual13 +
                       x.dual13 * y.dual5 + x.dual3 * y.dual15 +
                       x.dual1 * y.dual35 + x.real * y.dual135,
            .dual235 = x.dual235 * y.real + x.dual35 * y.dual2 +
                       x.dual25 * y.dual3 + x.dual5 * y.dual23 +
                       x.dual23 * y.dual5 + x.dual3 * y.dual25 +
                       x.dual2 * y.dual35 + x.real * y.dual235,
            .dual1235 = x.dual1235 * y.real + x.dual235 * y.dual1 +
                        x.dual135 * y.dual2 + x.dual35 * y.dual12 +
                        x.dual125 * y.dual3 + x.dual25 * y.dual13 +
                        x.dual15 * y.dual23 + x.dual5 * y.dual123 +
                        x.dual123 * y.dual5 + x.dual23 * y.dual15 +
                        x.dual13 * y.dual25 + x.dual3 * y.dual125 +
                        x.dual12 * y.dual35 + x.dual2 * y.dual135 +
                        x.dual1 * y.dual235 + x.real * y.dual1235,
            .dual45 = x.dual45 * y.real + x.dual5 * y.dual4 +
                      x.dual4 * y.dual5 + x.real * y.dual45,
            .dual145 = x.dual145 * y.real + x.dual45 * y.dual1 +
                       x.dual15 * y.dual4 + x.dual5 * y.dual14 +
                       x.dual14 * y.dual5 + x.dual4 * y.dual15 +
                       x.dual1 * y.dual45 + x.real * y.dual145,
            .dual245 = x.dual245 * y.real + x.dual45 * y.dual2 +
                       x.dual25 * y.dual4 + x.dual5 * y.dual24 +
                       x.dual24 * y.dual5 + x.dual4 * y.dual25 +
                       x.dual2 * y.dual45 + x.real * y.dual245,
            .dual1245 = x.dual1245 * y.real + x.dual245 * y.dual1 +
                        x.dual145 * y.dual2 + x.dual45 * y.dual12 +
                        x.dual125 * y.dual4 + x.dual25 * y.dual14 +
                        x.dual15 * y.dual24 + x.dual5 * y.dual124 +
                        x.dual124 * y.dual5 + x.dual24 * y.dual15 +
                        x.dual14 * y.dual25 + x.dual4 * y.dual125 +
                        x.dual12 * y.dual45 + x.dual2 * y.dual145 +
                        x.dual1 * y.dual245 + x.real * y.dual1245,
            .dual345 = x.dual345 * y.real + x.dual45 * y.dual3 +
                       x.dual35 * y.dual4 + x.dual5 * y.dual34 +
                       x.dual34 * y.dual5 + x.dual4 * y.dual35 +
                       x.dual3 * y.dual45 + x.real * y.dual345,
            .dual1345 = x.dual1345 * y.real + x.dual345 * y.dual1 +
                        x.dual145 * y.dual3 + x.dual45 * y.dual13 +
                        x.dual135 * y.dual4 + x.dual35 * y.dual14 +
                        x.dual15 * y.dual34 + x.dual5 * y.dual134 +
                        x.dual134 * y.dual5 + x.dual34 * y.dual15 +
                        x.dual14 * y.dual35 + x.dual4 * y.dual135 +
                        x.dual13 * y.dual45 + x.dual3 * y.dual145 +
                        x.dual1 * y.dual345 + x.real * y.dual1345,
            .dual2345 = x.dual2345 * y.real + x.dual345 * y.dual2 +
                        x.dual245 * y.dual3 + x.dual45 * y.dual23 +
                        x.dual235 * y.dual4 + x.dual35 * y.dual24 +
                        x.dual25 * y.dual34 + x.dual5 * y.dual234 +
                        x.dual234 * y.dual5 + x.dual34 * y.dual25 +
                        x.dual24 * y.dual35 + x.dual4 * y.dual235 +
                        x.dual23 * y.dual45 + x.dual3 * y.dual245 +
                        x.dual2 * y.dual345 + x.real * y.dual2345,
            .dual12345 = x.dual12345 * y.real + x.dual2345 * y.dual1 +
                         x.dual1345 * y.dual2 + x.dual345 * y.dual12 +
                         x.dual1245 * y.dual3 + x.dual245 * y.dual13 +
                         x.dual145 * y.dual23 + x.dual45 * y.dual123 +
                         x.dual1235 * y.dual4 + x.dual235 * y.dual14 +
                         x.dual135 * y.dual24 + x.dual35 * y.dual124 +
                         x.dual125 * y.dual34 + x.dual25 * y.dual134 +
                         x.dual15 * y.dual234 + x.dual5 * y.dual1234 +
                         x.dual1234 * y.dual5 + x.dual234 * y.dual15 +
                         x.dual134 * y.dual25 + x.dual34 * y.dual125 +
                         x.dual124 * y.dual35 + x.dual24 * y.dual135 +
                         x.dual14 * y.dual235 + x.dual4 * y.dual1235 +
                         x.dual123 * y.dual45 + x.dual23 * y.dual145 +
                         x.dual13 * y.dual245 + x.dual3 * y.dual1245 +
                         x.dual12 * y.dual345 + x.dual2 * y.dual1345 +
                         x.dual1 * y.dual2345 + x.real * y.dual12345,
            .dual6 = x.dual6 * y.real + x.real * y.dual6,
            .dual16 = x.dual16 * y.real + x.dual6 * y.dual1 +
                      x.dual1 * y.dual6 + x.real * y.dual16,
            .dual26 = x.dual26 * y.real + x.dual6 * y.dual2 +
                      x.dual2 * y.dual6 + x.real * y.dual26,
            .dual126 = x.dual126 * y.real + x.dual26 * y.dual1 +
                       x.dual16 * y.dual2 + x.dual6 * y.dual12 +
                       x.dual12 * y.dual6 + x.dual2 * y.dual16 +
                       x.dual1 * y.dual26 + x.real * y.dual126,
            .dual36 = x.dual36 * y.real + x.dual6 * y.dual3 +
                      x.dual3 * y.dual6 + x.real * y.dual36,
            .dual136 = x.dual136 * y.real + x.dual36 * y.dual1 +
                       x.dual16 * y.dual3 + x.dual6 * y.dual13 +
                       x.dual13 * y.dual6 + x.dual3 * y.dual16 +
                       x.dual1 * y.dual36 + x.real * y.dual136,
            .dual236 = x.dual236 * y.real + x.dual36 * y.dual2 +
                       x.dual26 * y.dual3 + x.dual6 * y.dual23 +
                       x.dual23 * y.dual6 + x.dual3 * y.dual26 +
                       x.dual2 * y.dual36 + x.real * y.dual236,
            .dual1236 = x.dual1236 * y.real + x.dual236 * y.dual1 +
                        x.dual136 * y.dual2 + x.dual36 * y.dual12 +
                        x.dual126 * y.dual3 + x.dual26 * y.dual13 +
                        x.dual16 * y.dual23 + x.dual6 * y.dual123 +
                        x.dual123 * y.dual6 + x.dual23 * y.dual16 +
                        x.dual13 * y.dual26 + x.dual3 * y.dual126 +
                        x.dual12 * y.dual36 + x.dual2 * y.dual136 +
                        x.dual1 * y.dual236 + x.real * y.dual1236,
            .dual46 = x.dual46 * y.real + x.dual6 * y.dual4 +
                      x.dual4 * y.dual6 + x.real * y.dual46,
            .dual146 = x.dual146 * y.real + x.dual46 * y.dual1 +
                       x.dual16 * y.dual4 + x.dual6 * y.dual14 +
                       x.dual14 * y.dual6 + x.dual4 * y.dual16 +
                       x.dual1 * y.dual46 + x.real * y.dual146,
            .dual246 = x.dual246 * y.real + x.dual46 * y.dual2 +
                       x.dual26 * y.dual4 + x.dual6 * y.dual24 +
                       x.dual24 * y.dual6 + x.dual4 * y.dual26 +
                       x.dual2 * y.dual46 + x.real * y.dual246,
            .dual1246 = x.dual1246 * y.real + x.dual246 * y.dual1 +
                        x.dual146 * y.dual2 + x.dual46 * y.dual12 +
                        x.dual126 * y.dual4 + x.dual26 * y.dual14 +
                        x.dual16 * y.dual24 + x.dual6 * y.dual124 +
                        x.dual124 * y.dual6 + x.dual24 * y.dual16 +
                        x.dual14 * y.dual26 + x.dual4 * y.dual126 +
                        x.dual12 * y.dual46 + x.dual2 * y.dual146 +
                        x.dual1 * y.dual246 + x.real * y.dual1246,
            .dual346 = x.dual346 * y.real + x.dual46 * y.dual3 +
                       x.dual36 * y.dual4 + x.dual6 * y.dual34 +
                       x.dual34 * y.dual6 + x.dual4 * y.dual36 +
                       x.dual3 * y.dual46 + x.real * y.dual346,
            .dual1346 = x.dual1346 * y.real + x.dual346 * y.dual1 +
                        x.dual146 * y.dual3 + x.dual46 * y.dual13 +
                        x.dual136 * y.dual4 + x.dual36 * y.dual14 +
                        x.dual16 * y.dual34 + x.dual6 * y.dual134 +
                        x.dual134 * y.dual6 + x.dual34 * y.dual16 +
                        x.dual14 * y.dual36 + x.dual4 * y.dual136 +
                        x.dual13 * y.dual46 + x.dual3 * y.dual146 +
                        x.dual1 * y.dual346 + x.real * y.dual1346,
            .dual2346 = x.dual2346 * y.real + x.dual346 * y.dual2 +
                        x.dual246 * y.dual3 + x.dual46 * y.dual23 +
                        x.dual236 * y.dual4 + x.dual36 * y.dual24 +
                        x.dual26 * y.dual34 + x.dual6 * y.dual234 +
                        x.dual234 * y.dual6 + x.dual34 * y.dual26 +
                        x.dual24 * y.dual36 + x.dual4 * y.dual236 +
                        x.dual23 * y.dual46 + x.dual3 * y.dual246 +
                        x.dual2 * y.dual346 + x.real * y.dual2346,
            .dual12346 = x.dual12346 * y.real + x.dual2346 * y.dual1 +
                         x.dual1346 * y.dual2 + x.dual346 * y.dual12 +
                         x.dual1246 * y.dual3 + x.dual246 * y.dual13 +
                         x.dual146 * y.dual23 + x.dual46 * y.dual123 +
                         x.dual1236 * y.dual4 + x.dual236 * y.dual14 +
                         x.dual136 * y.dual24 + x.dual36 * y.dual124 +
                         x.dual126 * y.dual34 + x.dual26 * y.dual134 +
                         x.dual16 * y.dual234 + x.dual6 * y.dual1234 +
                         x.dual1234 * y.dual6 + x.dual234 * y.dual16 +
                         x.dual134 * y.dual26 + x.dual34 * y.dual126 +
                         x.dual124 * y.dual36 + x.dual24 * y.dual136 +
                         x.dual14 * y.dual236 + x.dual4 * y.dual1236 +
                         x.dual123 * y.dual46 + x.dual23 * y.dual146 +
                         x.dual13 * y.dual246 + x.dual3 * y.dual1246 +
                         x.dual12 * y.dual346 + x.dual2 * y.dual1346 +
                         x.dual1 * y.dual2346 + x.real * y.dual12346,
            .dual56 = x.dual56 * y.real + x.dual6 * y.dual5 +
                      x.dual5 * y.dual6 + x.real * y.dual56,
            .dual156 = x.dual156 * y.real + x.dual56 * y.dual1 +
                       x.dual16 * y.dual5 + x.dual6 * y.dual15 +
                       x.dual15 * y.dual6 + x.dual5 * y.dual16 +
                       x.dual1 * y.dual56 + x.real * y.dual156,
            .dual256 = x.dual256 * y.real + x.dual56 * y.dual2 +
                       x.dual26 * y.dual5 + x.dual6 * y.dual25 +
                       x.dual25 * y.dual6 + x.dual5 * y.dual26 +
                       x.dual2 * y.dual56 + x.real * y.dual256,
            .dual1256 = x.dual1256 * y.real + x.dual256 * y.dual1 +
                        x.dual156 * y.dual2 + x.dual56 * y.dual12 +
                        x.dual126 * y.dual5 + x.dual26 * y.dual15 +
                        x.dual16 * y.dual25 + x.dual6 * y.dual125 +
                        x.dual125 * y.dual6 + x.dual25 * y.dual16 +
                        x.dual15 * y.dual26 + x.dual5 * y.dual126 +
                        x.dual12 * y.dual56 + x.dual2 * y.dual156 +
                        x.dual1 * y.dual256 + x.real * y.dual1256,
            .dual356 = x.dual356 * y.real + x.dual56 * y.dual3 +
                       x.dual36 * y.dual5 + x.dual6 * y.dual35 +
                       x.dual35 * y.dual6 + x.dual5 * y.dual36 +
                       x.dual3 * y.dual56 + x.real * y.dual356,
            .dual1356 = x.dual1356 * y.real + x.dual356 * y.dual1 +
                        x.dual156 * y.dual3 + x.dual56 * y.dual13 +
                        x.dual136 * y.dual5 + x.dual36 * y.dual15 +
                        x.dual16 * y.dual35 + x.dual6 * y.dual135 +
                        x.dual135 * y.dual6 + x.dual35 * y.dual16 +
                        x.dual15 * y.dual36 + x.dual5 * y.dual136 +
                        x.dual13 * y.dual56 + x.dual3 * y.dual156 +
                        x.dual1 * y.dual356 + x.real * y.dual1356,
            .dual2356 = x.dual2356 * y.real + x.dual356 * y.dual2 +
                        x.dual256 * y.dual3 + x.dual56 * y.dual23 +
                        x.dual236 * y.dual5 + x.dual36 * y.dual25 +
                        x.dual26 * y.dual35 + x.dual6 * y.dual235 +
                        x.dual235 * y.dual6 + x.dual35 * y.dual26 +
                        x.dual25 * y.dual36 + x.dual5 * y.dual236 +
                        x.dual23 * y.dual56 + x.dual3 * y.dual256 +
                        x.dual2 * y.dual356 + x.real * y.dual2356,
            .dual12356 = x.dual12356 * y.real + x.dual2356 * y.dual1 +
                         x.dual1356 * y.dual2 + x.dual356 * y.dual12 +
                         x.dual1256 * y.dual3 + x.dual256 * y.dual13 +
                         x.dual156 * y.dual23 + x.dual56 * y.dual123 +
                         x.dual1236 * y.dual5 + x.dual236 * y.dual15 +
                         x.dual136 * y.dual25 + x.dual36 * y.dual125 +
                         x.dual126 * y.dual35 + x.dual26 * y.dual135 +
                         x.dual16 * y.dual235 + x.dual6 * y.dual1235 +
                         x.dual1235 * y.dual6 + x.dual235 * y.dual16 +
                         x.dual135 * y.dual26 + x.dual35 * y.dual126 +
                         x.dual125 * y.dual36 + x.dual25 * y.dual136 +
                         x.dual15 * y.dual236 + x.dual5 * y.dual1236 +
                         x.dual123 * y.dual56 + x.dual23 * y.dual156 +
                         x.dual13 * y.dual256 + x.dual3 * y.dual1256 +
                         x.dual12 * y.dual356 + x.dual2 * y.dual1356 +
                         x.dual1 * y.dual2356 + x.real * y.dual12356,
            .dual456 = x.dual456 * y.real + x.dual56 * y.dual4 +
                       x.dual46 * y.dual5 + x.dual6 * y.dual45 +
                       x.dual45 * y.dual6 + x.dual5 * y.dual46 +
                       x.dual4 * y.dual56 + x.real * y.dual456,
            .dual1456 = x.dual1456 * y.real + x.dual456 * y.dual1 +
                        x.dual156 * y.dual4 + x.dual56 * y.dual14 +
                        x.dual146 * y.dual5 + x.dual46 * y.dual15 +
                        x.dual16 * y.dual45 + x.dual6 * y.dual145 +
                        x.dual145 * y.dual6 + x.dual45 * y.dual16 +
                        x.dual15 * y.dual46 + x.dual5 * y.dual146 +
                        x.dual14 * y.dual56 + x.dual4 * y.dual156 +
                        x.dual1 * y.dual456 + x.real * y.dual1456,
            .dual2456 = x.dual2456 * y.real + x.dual456 * y.dual2 +
                        x.dual256 * y.dual4 + x.dual56 * y.dual24 +
                        x.dual246 * y.dual5 + x.dual46 * y.dual25 +
                        x.dual26 * y.dual45 + x.dual6 * y.dual245 +
                        x.dual245 * y.dual6 + x.dual45 * y.dual26 +
                        x.dual25 * y.dual46 + x.dual5 * y.dual246 +
                        x.dual24 * y.dual56 + x.dual4 * y.dual256 +
                        x.dual2 * y.dual456 + x.real * y.dual2456,
            .dual12456 = x.dual12456 * y.real + x.dual2456 * y.dual1 +
                         x.dual1456 * y.dual2 + x.dual456 * y.dual12 +
                         x.dual1256 * y.dual4 + x.dual256 * y.dual14 +
                         x.dual156 * y.dual24 + x.dual56 * y.dual124 +
                         x.dual1246 * y.dual5 + x.dual246 * y.dual15 +
                         x.dual146 * y.dual25 + x.dual46 * y.dual125 +
                         x.dual126 * y.dual45 + x.dual26 * y.dual145 +
                         x.dual16 * y.dual245 + x.dual6 * y.dual1245 +
                         x.dual1245 * y.dual6 + x.dual245 * y.dual16 +
                         x.dual145 * y.dual26 + x.dual45 * y.dual126 +
                         x.dual125 * y.dual46 + x.dual25 * y.dual146 +
                         x.dual15 * y.dual246 + x.dual5 * y.dual1246 +
                         x.dual124 * y.dual56 + x.dual24 * y.dual156 +
                         x.dual14 * y.dual256 + x.dual4 * y.dual1256 +
                         x.dual12 * y.dual456 + x.dual2 * y.dual1456 +
                         x.dual1 * y.dual2456 + x.real * y.dual12456,
            .dual3456 = x.dual3456 * y.real + x.dual456 * y.dual3 +
                        x.dual356 * y.dual4 + x.dual56 * y.dual34 +
                        x.dual346 * y.dual5 + x.dual46 * y.dual35 +
                        x.dual36 * y.dual45 + x.dual6 * y.dual345 +
                        x.dual345 * y.dual6 + x.dual45 * y.dual36 +
                        x.dual35 * y.dual46 + x.dual5 * y.dual346 +
                        x.dual34 * y.dual56 + x.dual4 * y.dual356 +
                        x.dual3 * y.dual456 + x.real * y.dual3456,
            .dual13456 = x.dual13456 * y.real + x.dual3456 * y.dual1 +
                         x.dual1456 * y.dual3 + x.dual456 * y.dual13 +
                         x.dual1356 * y.dual4 + x.dual356 * y.dual14 +
                         x.dual156 * y.dual34 + x.dual56 * y.dual134 +
                         x.dual1346 * y.dual5 + x.dual346 * y.dual15 +
                         x.dual146 * y.dual35 + x.dual46 * y.dual135 +
                         x.dual136 * y.dual45 + x.dual36 * y.dual145 +
                         x.dual16 * y.dual345 + x.dual6 * y.dual1345 +
                         x.dual1345 * y.dual6 + x.dual345 * y.dual16 +
                         x.dual145 * y.dual36 + x.dual45 * y.dual136 +
                         x.dual135 * y.dual46 + x.dual35 * y.dual146 +
                         x.dual15 * y.dual346 + x.dual5 * y.dual1346 +
                         x.dual134 * y.dual56 + x.dual34 * y.dual156 +
                         x.dual14 * y.dual356 + x.dual4 * y.dual1356 +
                         x.dual13 * y.dual456 + x.dual3 * y.dual1456 +
                         x.dual1 * y.dual3456 + x.real * y.dual13456,
            .dual23456 = x.dual23456 * y.real + x.dual3456 * y.dual2 +
                         x.dual2456 * y.dual3 + x.dual456 * y.dual23 +
                         x.dual2356 * y.dual4 + x.dual356 * y.dual24 +
                         x.dual256 * y.dual34 + x.dual56 * y.dual234 +
                         x.dual2346 * y.dual5 + x.dual346 * y.dual25 +
                         x.dual246 * y.dual35 + x.dual46 * y.dual235 +
                         x.dual236 * y.dual45 + x.dual36 * y.dual245 +
                         x.dual26 * y.dual345 + x.dual6 * y.dual2345 +
                         x.dual2345 * y.dual6 + x.dual345 * y.dual26 +
                         x.dual245 * y.dual36 + x.dual45 * y.dual236 +
                         x.dual235 * y.dual46 + x.dual35 * y.dual246 +
                         x.dual25 * y.dual346 + x.dual5 * y.dual2346 +
                         x.dual234 * y.dual56 + x.dual34 * y.dual256 +
                         x.dual24 * y.dual356 + x.dual4 * y.dual2356 +
                         x.dual23 * y.dual456 + x.dual3 * y.dual2456 +
                         x.dual2 * y.dual3456 + x.real * y.dual23456,
            .dual123456 = x.dual123456 * y.real + x.dual23456 * y.dual1 +
                          x.dual13456 * y.dual2 + x.dual3456 * y.dual12 +
                          x.dual12456 * y.dual3 + x.dual2456 * y.dual13 +
                          x.dual1456 * y.dual23 + x.dual456 * y.dual123 +
                          x.dual12356 * y.dual4 + x.dual2356 * y.dual14 +
                          x.dual1356 * y.dual24 + x.dual356 * y.dual124 +
                          x.dual1256 * y.dual34 + x.dual256 * y.dual134 +
                          x.dual156 * y.dual234 + x.dual56 * y.dual1234 +
                          x.dual12346 * y.dual5 + x.dual2346 * y.dual15 +
                          x.dual1346 * y.dual25 + x.dual346 * y.dual125 +
                          x.dual1246 * y.dual35 + x.dual246 * y.dual135 +
                          x.dual146 * y.dual235 + x.dual46 * y.dual1235 +
                          x.dual1236 * y.dual45 + x.dual236 * y.dual145 +
                          x.dual136 * y.dual245 + x.dual36 * y.dual1245 +
                          x.dual126 * y.dual345 + x.dual26 * y.dual1345 +
                          x.dual16 * y.dual2345 + x.dual6 * y.dual12345 +
                          x.dual12345 * y.dual6 + x.dual2345 * y.dual16 +
                          x.dual1345 * y.dual26 + x.dual345 * y.dual126 +
                          x.dual1245 * y.dual36 + x.dual245 * y.dual136 +
                          x.dual145 * y.dual236 + x.dual45 * y.dual1236 +
                          x.dual1235 * y.dual46 + x.dual235 * y.dual146 +
                          x.dual135 * y.dual246 + x.dual35 * y.dual1246 +
                          x.dual125 * y.dual346 + x.dual25 * y.dual1346 +
                          x.dual15 * y.dual2346 + x.dual5 * y.dual12346 +
                          x.dual1234 * y.dual56 + x.dual234 * y.dual156 +
                          x.dual134 * y.dual256 + x.dual34 * y.dual1256 +
                          x.dual124 * y.dual356 + x.dual24 * y.dual1356 +
                          x.dual14 * y.dual2356 + x.dual4 * y.dual12356 +
                          x.dual123 * y.dual456 + x.dual23 * y.dual1456 +
                          x.dual13 * y.dual2456 + x.dual3 * y.dual12456 +
                          x.dual12 * y.dual3456 + x.dual2 * y.dual13456 +
                          x.dual1 * y.dual23456 + x.real * y.dual123456,
    };
}

hyperdual6 operator/(const hyperdual6 &x, const hyperdual6 &y) {
    const auto u = x.real / y.real;
    const auto u1 = x.dual1 / y.real;
    const auto u2 = x.dual2 / y.real;
    const auto u12 = x.dual12 / y.real;
    const auto u3 = x.dual3 / y.real;
    const auto u13 = x.dual13 / y.real;
    const auto u23 = x.dual23 / y.real;
    const auto u123 = x.dual123 / y.real;
    const auto u4 = x.dual4 / y.real;
    const auto u14 = x.dual14 / y.real;
    const auto u24 = x.dual24 / y.real;
    const auto u124 = x.dual124 / y.real;
    const auto u34 = x.dual34 / y.real;
    const auto u134 = x.dual134 / y.real;
    const auto u234 = x.dual234 / y.real;
    const auto u1234 = x.dual1234 / y.real;
    const auto u5 = x.dual5 / y.real;
    const auto u15 = x.dual15 / y.real;
    const auto u25 = x.dual25 / y.real;
    const auto u125 = x.dual125 / y.real;
    const auto u35 = x.dual35 / y.real;
    const auto u135 = x.dual135 / y.real;
    const auto u235 = x.dual235 / y.real;
    const auto u1235 = x.dual1235 / y.real;
    const auto u45 = x.dual45 / y.real;
    const auto u145 = x.dual145 / y.real;
    const auto u245 = x.dual245 / y.real;
    const auto u1245 = x.dual1245 / y.real;
    const auto u345 = x.dual345 / y.real;
    const auto u1345 = x.dual1345 / y.real;
    const auto u2345 = x.dual2345 / y.real;
    const auto u12345 = x.dual12345 / y.real;
    const auto u6 = x.dual6 / y.real;
    const auto u16 = x.dual16 / y.real;
    const auto u26 = x.dual26 / y.real;
    const auto u126 = x.dual126 / y.real;
    const auto u36 = x.dual36 / y.real;
    const auto u136 = x.dual136 / y.real;
    const auto u236 = x.dual236 / y.real;
    const auto u1236 = x.dual1236 / y.real;
    const auto u46 = x.dual46 / y.real;
    const auto u146 = x.dual146 / y.real;
    const auto u246 = x.dual246 / y.real;
    const auto u1246 = x.dual1246 / y.real;
    const auto u346 = x.dual346 / y.real;
    const auto u1346 = x.dual1346 / y.real;
    const auto u2346 = x.dual2346 / y.real;
    const auto u12346 = x.dual12346 / y.real;
    const auto u56 = x.dual56 / y.real;
    const auto u156 = x.dual156 / y.real;
    const auto u256 = x.dual256 / y.real;
    const auto u1256 = x.dual1256 / y.real;
    const auto u356 = x.dual356 / y.real;
    const auto u1356 = x.dual1356 / y.real;
    const auto u2356 = x.dual2356 / y.real;
    const auto u12356 = x.dual12356 / y.real;
    const auto u456 = x.dual456 / y.real;
    const auto u1456 = x.dual1456 / y.real;
    const auto u2456 = x.dual2456 / y.real;
    const auto u12456 = x.dual12456 / y.real;
    const auto u3456 = x.dual3456 / y.real;
    const auto u13456 = x.dual13456 / y.real;
    const auto u23456 = x.dual23456 / y.real;
    const auto u123456 = x.dual123456 / y.real;
    const auto v1 = y.dual1 / y.real;
    const auto v2 = y.dual2 / y.real;
    const auto v12 = y.dual12 / y.real;
    const auto v3 = y.dual3 / y.real;
    const auto v13 = y.dual13 / y.real;
    const auto v23 = y.dual23 / y.real;
    const auto v123 = y.dual123 / y.real;
    const auto v4 = y.dual4 / y.real;
    const auto v14 = y.dual14 / y.real;
    const auto v24 = y.dual24 / y.real;
    const auto v124 = y.dual124 / y.real;
    const auto v34 = y.dual34 / y.real;
    const auto v134 = y.dual134 / y.real;
    const auto v234 = y.dual234 / y.real;
    const auto v1234 = y.dual1234 / y.real;
    const auto v5 = y.dual5 / y.real;
    const auto v15 = y.dual15 / y.real;
    const auto v25 = y.dual25 / y.real;
    const auto v125 = y.dual125 / y.real;
    const auto v35 = y.dual35 / y.real;
    const auto v135 = y.dual135 / y.real;
    const auto v235 = y.dual235 / y.real;
    const auto v1235 = y.dual1235 / y.real;
    const auto v45 = y.dual45 / y.real;
    const auto v145 = y.dual145 / y.real;
    const auto v245 = y.dual245 / y.real;
    const auto v1245 = y.dual1245 / y.real;
    const auto v345 = y.dual345 / y.real;
    const auto v1345 = y.dual1345 / y.real;
    const auto v2345 = y.dual2345 / y.real;
    const auto v12345 = y.dual12345 / y.real;
    const auto v6 = y.dual6 / y.real;
    const auto v16 = y.dual16 / y.real;
    const auto v26 = y.dual26 / y.real;
    const auto v126 = y.dual126 / y.real;
    const auto v36 = y.dual36 / y.real;
    const auto v136 = y.dual136 / y.real;
    const auto v236 = y.dual236 / y.real;
    const auto v1236 = y.dual1236 / y.real;
    const auto v46 = y.dual46 / y.real;
    const auto v146 = y.dual146 / y.real;
    const auto v246 = y.dual246 / y.real;
    const auto v1246 = y.dual1246 / y.real;
    const auto v346 = y.dual346 / y.real;
    const auto v1346 = y.dual1346 / y.real;
    const auto v2346 = y.dual2346 / y.real;
    const auto v12346 = y.dual12346 / y.real;
    const auto v56 = y.dual56 / y.real;
    const auto v156 = y.dual156 / y.real;
    const auto v256 = y.dual256 / y.real;
    const auto v1256 = y.dual1256 / y.real;
    const auto v356 = y.dual356 / y.real;
    const auto v1356 = y.dual1356 / y.real;
    const auto v2356 = y.dual2356 / y.real;
    const auto v12356 = y.dual12356 / y.real;
    const auto v456 = y.dual456 / y.real;
    const auto v1456 = y.dual1456 / y.real;
    const auto v2456 = y.dual2456 / y.real;
    const auto v12456 = y.dual12456 / y.real;
    const auto v3456 = y.dual3456 / y.real;
    const auto v13456 = y.dual13456 / y.real;
    const auto v23456 = y.dual23456 / y.real;
    const auto v123456 = y.dual123456 / y.real;
    return {
    .real = u, .dual1 = u1 - u * v1, .dual2 = u2 - u * v2,
    .dual12 = u12 - u2 * v1 - u1 * v2 + 2 * u * v1 * v2 - u * v12,
    .dual3 = u3 - u * v3,
    .dual13 = u13 - u3 * v1 - u1 * v3 + 2 * u * v1 * v3 - u * v13,
    .dual23 = u23 - u3 * v2 - u2 * v3 + 2 * u * v2 * v3 - u * v23,
    .dual123 = u123 - u23 * v1 - u13 * v2 + 2 * u3 * v1 * v2 - u3 * v12 -
               u12 * v3 + 2 * u2 * v1 * v3 + 2 * u1 * v2 * v3 -
               6 * u * v1 * v2 * v3 + 2 * u * v12 * v3 - u2 * v13 +
               2 * u * v2 * v13 - u1 * v23 + 2 * u * v1 * v23 - u * v123,
    .dual4 = u4 - u * v4,
    .dual14 = u14 - u4 * v1 - u1 * v4 + 2 * u * v1 * v4 - u * v14,
    .dual24 = u24 - u4 * v2 - u2 * v4 + 2 * u * v2 * v4 - u * v24,
    .dual124 = u124 - u24 * v1 - u14 * v2 + 2 * u4 * v1 * v2 - u4 * v12 -
               u12 * v4 + 2 * u2 * v1 * v4 + 2 * u1 * v2 * v4 -
               6 * u * v1 * v2 * v4 + 2 * u * v12 * v4 - u2 * v14 +
               2 * u * v2 * v14 - u1 * v24 + 2 * u * v1 * v24 - u * v124,
    .dual34 = u34 - u4 * v3 - u3 * v4 + 2 * u * v3 * v4 - u * v34,
    .dual134 = u134 - u34 * v1 - u14 * v3 + 2 * u4 * v1 * v3 - u4 * v13 -
               u13 * v4 + 2 * u3 * v1 * v4 + 2 * u1 * v3 * v4 -
               6 * u * v1 * v3 * v4 + 2 * u * v13 * v4 - u3 * v14 +
               2 * u * v3 * v14 - u1 * v34 + 2 * u * v1 * v34 - u * v134,
    .dual234 = u234 - u34 * v2 - u24 * v3 + 2 * u4 * v2 * v3 - u4 * v23 -
               u23 * v4 + 2 * u3 * v2 * v4 + 2 * u2 * v3 * v4 -
               6 * u * v2 * v3 * v4 + 2 * u * v23 * v4 - u3 * v24 +
               2 * u * v3 * v24 - u2 * v34 + 2 * u * v2 * v34 - u * v234,
    .dual1234 = u1234 - u234 * v1 - u134 * v2 + 2 * u34 * v1 * v2 - u34 * v12 -
                u124 * v3 + 2 * u24 * v1 * v3 + 2 * u14 * v2 * v3 -
                6 * u4 * v1 * v2 * v3 + 2 * u4 * v12 * v3 - u24 * v13 +
                2 * u4 * v2 * v13 - u14 * v23 + 2 * u4 * v1 * v23 - u4 * v123 -
                u123 * v4 + 2 * u23 * v1 * v4 + 2 * u13 * v2 * v4 -
                6 * u3 * v1 * v2 * v4 + 2 * u3 * v12 * v4 + 2 * u12 * v3 * v4 -
                6 * u2 * v1 * v3 * v4 - 6 * u1 * v2 * v3 * v4 +
                24 * u * v1 * v2 * v3 * v4 - 6 * u * v12 * v3 * v4 +
                2 * u2 * v13 * v4 - 6 * u * v2 * v13 * v4 + 2 * u1 * v23 * v4 -
                6 * u * v1 * v23 * v4 + 2 * u * v123 * v4 - u23 * v14 +
                2 * u3 * v2 * v14 + 2 * u2 * v3 * v14 - 6 * u * v2 * v3 * v14 +
                2 * u * v23 * v14 - u13 * v24 + 2 * u3 * v1 * v24 +
                2 * u1 * v3 * v24 - 6 * u * v1 * v3 * v24 + 2 * u * v13 * v24 -
                u3 * v124 + 2 * u * v3 * v124 - u12 * v34 + 2 * u2 * v1 * v34 +
                2 * u1 * v2 * v34 - 6 * u * v1 * v2 * v34 + 2 * u * v12 * v34 -
                u2 * v134 + 2 * u * v2 * v134 - u1 * v234 + 2 * u * v1 * v234 -
                u * v1234,
    .dual5 = u5 - u * v5,
    .dual15 = u15 - u5 * v1 - u1 * v5 + 2 * u * v1 * v5 - u * v15,
    .dual25 = u25 - u5 * v2 - u2 * v5 + 2 * u * v2 * v5 - u * v25,
    .dual125 = u125 - u25 * v1 - u15 * v2 + 2 * u5 * v1 * v2 - u5 * v12 -
               u12 * v5 + 2 * u2 * v1 * v5 + 2 * u1 * v2 * v5 -
               6 * u * v1 * v2 * v5 + 2 * u * v12 * v5 - u2 * v15 +
               2 * u * v2 * v15 - u1 * v25 + 2 * u * v1 * v25 - u * v125,
    .dual35 = u35 - u5 * v3 - u3 * v5 + 2 * u * v3 * v5 - u * v35,
    .dual135 = u135 - u35 * v1 - u15 * v3 + 2 * u5 * v1 * v3 - u5 * v13 -
               u13 * v5 + 2 * u3 * v1 * v5 + 2 * u1 * v3 * v5 -
               6 * u * v1 * v3 * v5 + 2 * u * v13 * v5 - u3 * v15 +
               2 * u * v3 * v15 - u1 * v35 + 2 * u * v1 * v35 - u * v135,
    .dual235 = u235 - u35 * v2 - u25 * v3 + 2 * u5 * v2 * v3 - u5 * v23 -
               u23 * v5 + 2 * u3 * v2 * v5 + 2 * u2 * v3 * v5 -
               6 * u * v2 * v3 * v5 + 2 * u * v23 * v5 - u3 * v25 +
               2 * u * v3 * v25 - u2 * v35 + 2 * u * v2 * v35 - u * v235,
    .dual1235 = u1235 - u235 * v1 - u135 * v2 + 2 * u35 * v1 * v2 - u35 * v12 -
                u125 * v3 + 2 * u25 * v1 * v3 + 2 * u15 * v2 * v3 -
                6 * u5 * v1 * v2 * v3 + 2 * u5 * v12 * v3 - u25 * v13 +
                2 * u5 * v2 * v13 - u15 * v23 + 2 * u5 * v1 * v23 - u5 * v123 -
                u123 * v5 + 2 * u23 * v1 * v5 + 2 * u13 * v2 * v5 -
                6 * u3 * v1 * v2 * v5 + 2 * u3 * v12 * v5 + 2 * u12 * v3 * v5 -
                6 * u2 * v1 * v3 * v5 - 6 * u1 * v2 * v3 * v5 +
                24 * u * v1 * v2 * v3 * v5 - 6 * u * v12 * v3 * v5 +
                2 * u2 * v13 * v5 - 6 * u * v2 * v13 * v5 + 2 * u1 * v23 * v5 -
                6 * u * v1 * v23 * v5 + 2 * u * v123 * v5 - u23 * v15 +
                2 * u3 * v2 * v15 + 2 * u2 * v3 * v15 - 6 * u * v2 * v3 * v15 +
                2 * u * v23 * v15 - u13 * v25 + 2 * u3 * v1 * v25 +
                2 * u1 * v3 * v25 - 6 * u * v1 * v3 * v25 + 2 * u * v13 * v25 -
                u3 * v125 + 2 * u * v3 * v125 - u12 * v35 + 2 * u2 * v1 * v35 +
                2 * u1 * v2 * v35 - 6 * u * v1 * v2 * v35 + 2 * u * v12 * v35 -
                u2 * v135 + 2 * u * v2 * v135 - u1 * v235 + 2 * u * v1 * v235 -
                u * v1235,
    .dual45 = u45 - u5 * v4 - u4 * v5 + 2 * u * v4 * v5 - u * v45,
    .dual145 = u145 - u45 * v1 - u15 * v4 + 2 * u5 * v1 * v4 - u5 * v14 -
               u14 * v5 + 2 * u4 * v1 * v5 + 2 * u1 * v4 * v5 -
               6 * u * v1 * v4 * v5 + 2 * u * v14 * v5 - u4 * v15 +
               2 * u * v4 * v15 - u1 * v45 + 2 * u * v1 * v45 - u * v145,
    .dual245 = u245 - u45 * v2 - u25 * v4 + 2 * u5 * v2 * v4 - u5 * v24 -
               u24 * v5 + 2 * u4 * v2 * v5 + 2 * u2 * v4 * v5 -
               6 * u * v2 * v4 * v5 + 2 * u * v24 * v5 - u4 * v25 +
               2 * u * v4 * v25 - u2 * v45 + 2 * u * v2 * v45 - u * v245,
    .dual1245 = u1245 - u245 * v1 - u145 * v2 + 2 * u45 * v1 * v2 - u45 * v12 -
                u125 * v4 + 2 * u25 * v1 * v4 + 2 * u15 * v2 * v4 -
                6 * u5 * v1 * v2 * v4 + 2 * u5 * v12 * v4 - u25 * v14 +
                2 * u5 * v2 * v14 - u15 * v24 + 2 * u5 * v1 * v24 - u5 * v124 -
                u124 * v5 + 2 * u24 * v1 * v5 + 2 * u14 * v2 * v5 -
                6 * u4 * v1 * v2 * v5 + 2 * u4 * v12 * v5 + 2 * u12 * v4 * v5 -
                6 * u2 * v1 * v4 * v5 - 6 * u1 * v2 * v4 * v5 +
                24 * u * v1 * v2 * v4 * v5 - 6 * u * v12 * v4 * v5 +
                2 * u2 * v14 * v5 - 6 * u * v2 * v14 * v5 + 2 * u1 * v24 * v5 -
                6 * u * v1 * v24 * v5 + 2 * u * v124 * v5 - u24 * v15 +
                2 * u4 * v2 * v15 + 2 * u2 * v4 * v15 - 6 * u * v2 * v4 * v15 +
                2 * u * v24 * v15 - u14 * v25 + 2 * u4 * v1 * v25 +
                2 * u1 * v4 * v25 - 6 * u * v1 * v4 * v25 + 2 * u * v14 * v25 -
                u4 * v125 + 2 * u * v4 * v125 - u12 * v45 + 2 * u2 * v1 * v45 +
                2 * u1 * v2 * v45 - 6 * u * v1 * v2 * v45 + 2 * u * v12 * v45 -
                u2 * v145 + 2 * u * v2 * v145 - u1 * v245 + 2 * u * v1 * v245 -
                u * v1245,
    .dual345 = u345 - u45 * v3 - u35 * v4 + 2 * u5 * v3 * v4 - u5 * v34 -
               u34 * v5 + 2 * u4 * v3 * v5 + 2 * u3 * v4 * v5 -
               6 * u * v3 * v4 * v5 + 2 * u * v34 * v5 - u4 * v35 +
               2 * u * v4 * v35 - u3 * v45 + 2 * u * v3 * v45 - u * v345,
    .dual1345 = u1345 - u345 * v1 - u145 * v3 + 2 * u45 * v1 * v3 - u45 * v13 -
                u135 * v4 + 2 * u35 * v1 * v4 + 2 * u15 * v3 * v4 -
                6 * u5 * v1 * v3 * v4 + 2 * u5 * v13 * v4 - u35 * v14 +
                2 * u5 * v3 * v14 - u15 * v34 + 2 * u5 * v1 * v34 - u5 * v134 -
                u134 * v5 + 2 * u34 * v1 * v5 + 2 * u14 * v3 * v5 -
                6 * u4 * v1 * v3 * v5 + 2 * u4 * v13 * v5 + 2 * u13 * v4 * v5 -
                6 * u3 * v1 * v4 * v5 - 6 * u1 * v3 * v4 * v5 +
                24 * u * v1 * v3 * v4 * v5 - 6 * u * v13 * v4 * v5 +
                2 * u3 * v14 * v5 - 6 * u * v3 * v14 * v5 + 2 * u1 * v34 * v5 -
                6 * u * v1 * v34 * v5 + 2 * u * v134 * v5 - u34 * v15 +
                2 * u4 * v3 * v15 + 2 * u3 * v4 * v15 - 6 * u * v3 * v4 * v15 +
                2 * u * v34 * v15 - u14 * v35 + 2 * u4 * v1 * v35 +
                2 * u1 * v4 * v35 - 6 * u * v1 * v4 * v35 + 2 * u * v14 * v35 -
                u4 * v135 + 2 * u * v4 * v135 - u13 * v45 + 2 * u3 * v1 * v45 +
                2 * u1 * v3 * v45 - 6 * u * v1 * v3 * v45 + 2 * u * v13 * v45 -
                u3 * v145 + 2 * u * v3 * v145 - u1 * v345 + 2 * u * v1 * v345 -
                u * v1345,
    .dual2345 = u2345 - u345 * v2 - u245 * v3 + 2 * u45 * v2 * v3 - u45 * v23 -
                u235 * v4 + 2 * u35 * v2 * v4 + 2 * u25 * v3 * v4 -
                6 * u5 * v2 * v3 * v4 + 2 * u5 * v23 * v4 - u35 * v24 +
                2 * u5 * v3 * v24 - u25 * v34 + 2 * u5 * v2 * v34 - u5 * v234 -
                u234 * v5 + 2 * u34 * v2 * v5 + 2 * u24 * v3 * v5 -
                6 * u4 * v2 * v3 * v5 + 2 * u4 * v23 * v5 + 2 * u23 * v4 * v5 -
                6 * u3 * v2 * v4 * v5 - 6 * u2 * v3 * v4 * v5 +
                24 * u * v2 * v3 * v4 * v5 - 6 * u * v23 * v4 * v5 +
                2 * u3 * v24 * v5 - 6 * u * v3 * v24 * v5 + 2 * u2 * v34 * v5 -
                6 * u * v2 * v34 * v5 + 2 * u * v234 * v5 - u34 * v25 +
                2 * u4 * v3 * v25 + 2 * u3 * v4 * v25 - 6 * u * v3 * v4 * v25 +
                2 * u * v34 * v25 - u24 * v35 + 2 * u4 * v2 * v35 +
                2 * u2 * v4 * v35 - 6 * u * v2 * v4 * v35 + 2 * u * v24 * v35 -
                u4 * v235 + 2 * u * v4 * v235 - u23 * v45 + 2 * u3 * v2 * v45 +
                2 * u2 * v3 * v45 - 6 * u * v2 * v3 * v45 + 2 * u * v23 * v45 -
                u3 * v245 + 2 * u * v3 * v245 - u2 * v345 + 2 * u * v2 * v345 -
                u * v2345,
    .dual12345 =
            u12345 - u2345 * v1 - u1345 * v2 + 2 * u345 * v1 * v2 - u345 * v12 -
            u1245 * v3 + 2 * u245 * v1 * v3 + 2 * u145 * v2 * v3 -
            6 * u45 * v1 * v2 * v3 + 2 * u45 * v12 * v3 - u245 * v13 +
            2 * u45 * v2 * v13 - u145 * v23 + 2 * u45 * v1 * v23 - u45 * v123 -
            u1235 * v4 + 2 * u235 * v1 * v4 + 2 * u135 * v2 * v4 -
            6 * u35 * v1 * v2 * v4 + 2 * u35 * v12 * v4 + 2 * u125 * v3 * v4 -
            6 * u25 * v1 * v3 * v4 - 6 * u15 * v2 * v3 * v4 +
            24 * u5 * v1 * v2 * v3 * v4 - 6 * u5 * v12 * v3 * v4 +
            2 * u25 * v13 * v4 - 6 * u5 * v2 * v13 * v4 + 2 * u15 * v23 * v4 -
            6 * u5 * v1 * v23 * v4 + 2 * u5 * v123 * v4 - u235 * v14 +
            2 * u35 * v2 * v14 + 2 * u25 * v3 * v14 - 6 * u5 * v2 * v3 * v14 +
            2 * u5 * v23 * v14 - u135 * v24 + 2 * u35 * v1 * v24 +
            2 * u15 * v3 * v24 - 6 * u5 * v1 * v3 * v24 + 2 * u5 * v13 * v24 -
            u35 * v124 + 2 * u5 * v3 * v124 - u125 * v34 + 2 * u25 * v1 * v34 +
            2 * u15 * v2 * v34 - 6 * u5 * v1 * v2 * v34 + 2 * u5 * v12 * v34 -
            u25 * v134 + 2 * u5 * v2 * v134 - u15 * v234 + 2 * u5 * v1 * v234 -
            u5 * v1234 - u1234 * v5 + 2 * u234 * v1 * v5 + 2 * u134 * v2 * v5 -
            6 * u34 * v1 * v2 * v5 + 2 * u34 * v12 * v5 + 2 * u124 * v3 * v5 -
            6 * u24 * v1 * v3 * v5 - 6 * u14 * v2 * v3 * v5 +
            24 * u4 * v1 * v2 * v3 * v5 - 6 * u4 * v12 * v3 * v5 +
            2 * u24 * v13 * v5 - 6 * u4 * v2 * v13 * v5 + 2 * u14 * v23 * v5 -
            6 * u4 * v1 * v23 * v5 + 2 * u4 * v123 * v5 + 2 * u123 * v4 * v5 -
            6 * u23 * v1 * v4 * v5 - 6 * u13 * v2 * v4 * v5 +
            24 * u3 * v1 * v2 * v4 * v5 - 6 * u3 * v12 * v4 * v5 -
            6 * u12 * v3 * v4 * v5 + 24 * u2 * v1 * v3 * v4 * v5 +
            24 * u1 * v2 * v3 * v4 * v5 - 120 * u * v1 * v2 * v3 * v4 * v5 +
            24 * u * v12 * v3 * v4 * v5 - 6 * u2 * v13 * v4 * v5 +
            24 * u * v2 * v13 * v4 * v5 - 6 * u1 * v23 * v4 * v5 +
            24 * u * v1 * v23 * v4 * v5 - 6 * u * v123 * v4 * v5 +
            2 * u23 * v14 * v5 - 6 * u3 * v2 * v14 * v5 -
            6 * u2 * v3 * v14 * v5 + 24 * u * v2 * v3 * v14 * v5 -
            6 * u * v23 * v14 * v5 + 2 * u13 * v24 * v5 -
            6 * u3 * v1 * v24 * v5 - 6 * u1 * v3 * v24 * v5 +
            24 * u * v1 * v3 * v24 * v5 - 6 * u * v13 * v24 * v5 +
            2 * u3 * v124 * v5 - 6 * u * v3 * v124 * v5 + 2 * u12 * v34 * v5 -
            6 * u2 * v1 * v34 * v5 - 6 * u1 * v2 * v34 * v5 +
            24 * u * v1 * v2 * v34 * v5 - 6 * u * v12 * v34 * v5 +
            2 * u2 * v134 * v5 - 6 * u * v2 * v134 * v5 + 2 * u1 * v234 * v5 -
            6 * u * v1 * v234 * v5 + 2 * u * v1234 * v5 - u234 * v15 +
            2 * u34 * v2 * v15 + 2 * u24 * v3 * v15 - 6 * u4 * v2 * v3 * v15 +
            2 * u4 * v23 * v15 + 2 * u23 * v4 * v15 - 6 * u3 * v2 * v4 * v15 -
            6 * u2 * v3 * v4 * v15 + 24 * u * v2 * v3 * v4 * v15 -
            6 * u * v23 * v4 * v15 + 2 * u3 * v24 * v15 -
            6 * u * v3 * v24 * v15 + 2 * u2 * v34 * v15 -
            6 * u * v2 * v34 * v15 + 2 * u * v234 * v15 - u134 * v25 +
            2 * u34 * v1 * v25 + 2 * u14 * v3 * v25 - 6 * u4 * v1 * v3 * v25 +
            2 * u4 * v13 * v25 + 2 * u13 * v4 * v25 - 6 * u3 * v1 * v4 * v25 -
            6 * u1 * v3 * v4 * v25 + 24 * u * v1 * v3 * v4 * v25 -
            6 * u * v13 * v4 * v25 + 2 * u3 * v14 * v25 -
            6 * u * v3 * v14 * v25 + 2 * u1 * v34 * v25 -
            6 * u * v1 * v34 * v25 + 2 * u * v134 * v25 - u34 * v125 +
            2 * u4 * v3 * v125 + 2 * u3 * v4 * v125 - 6 * u * v3 * v4 * v125 +
            2 * u * v34 * v125 - u124 * v35 + 2 * u24 * v1 * v35 +
            2 * u14 * v2 * v35 - 6 * u4 * v1 * v2 * v35 + 2 * u4 * v12 * v35 +
            2 * u12 * v4 * v35 - 6 * u2 * v1 * v4 * v35 -
            6 * u1 * v2 * v4 * v35 + 24 * u * v1 * v2 * v4 * v35 -
            6 * u * v12 * v4 * v35 + 2 * u2 * v14 * v35 -
            6 * u * v2 * v14 * v35 + 2 * u1 * v24 * v35 -
            6 * u * v1 * v24 * v35 + 2 * u * v124 * v35 - u24 * v135 +
            2 * u4 * v2 * v135 + 2 * u2 * v4 * v135 - 6 * u * v2 * v4 * v135 +
            2 * u * v24 * v135 - u14 * v235 + 2 * u4 * v1 * v235 +
            2 * u1 * v4 * v235 - 6 * u * v1 * v4 * v235 + 2 * u * v14 * v235 -
            u4 * v1235 + 2 * u * v4 * v1235 - u123 * v45 + 2 * u23 * v1 * v45 +
            2 * u13 * v2 * v45 - 6 * u3 * v1 * v2 * v45 + 2 * u3 * v12 * v45 +
            2 * u12 * v3 * v45 - 6 * u2 * v1 * v3 * v45 -
            6 * u1 * v2 * v3 * v45 + 24 * u * v1 * v2 * v3 * v45 -
            6 * u * v12 * v3 * v45 + 2 * u2 * v13 * v45 -
            6 * u * v2 * v13 * v45 + 2 * u1 * v23 * v45 -
            6 * u * v1 * v23 * v45 + 2 * u * v123 * v45 - u23 * v145 +
            2 * u3 * v2 * v145 + 2 * u2 * v3 * v145 - 6 * u * v2 * v3 * v145 +
            2 * u * v23 * v145 - u13 * v245 + 2 * u3 * v1 * v245 +
            2 * u1 * v3 * v245 - 6 * u * v1 * v3 * v245 + 2 * u * v13 * v245 -
            u3 * v1245 + 2 * u * v3 * v1245 - u12 * v345 + 2 * u2 * v1 * v345 +
            2 * u1 * v2 * v345 - 6 * u * v1 * v2 * v345 + 2 * u * v12 * v345 -
            u2 * v1345 + 2 * u * v2 * v1345 - u1 * v2345 + 2 * u * v1 * v2345 -
            u * v12345,
    .dual6 = u6 - u * v6,
    .dual16 = u16 - u6 * v1 - u1 * v6 + 2 * u * v1 * v6 - u * v16,
    .dual26 = u26 - u6 * v2 - u2 * v6 + 2 * u * v2 * v6 - u * v26,
    .dual126 = u126 - u26 * v1 - u16 * v2 + 2 * u6 * v1 * v2 - u6 * v12 -
               u12 * v6 + 2 * u2 * v1 * v6 + 2 * u1 * v2 * v6 -
               6 * u * v1 * v2 * v6 + 2 * u * v12 * v6 - u2 * v16 +
               2 * u * v2 * v16 - u1 * v26 + 2 * u * v1 * v26 - u * v126,
    .dual36 = u36 - u6 * v3 - u3 * v6 + 2 * u * v3 * v6 - u * v36,
    .dual136 = u136 - u36 * v1 - u16 * v3 + 2 * u6 * v1 * v3 - u6 * v13 -
               u13 * v6 + 2 * u3 * v1 * v6 + 2 * u1 * v3 * v6 -
               6 * u * v1 * v3 * v6 + 2 * u * v13 * v6 - u3 * v16 +
               2 * u * v3 * v16 - u1 * v36 + 2 * u * v1 * v36 - u * v136,
    .dual236 = u236 - u36 * v2 - u26 * v3 + 2 * u6 * v2 * v3 - u6 * v23 -
               u23 * v6 + 2 * u3 * v2 * v6 + 2 * u2 * v3 * v6 -
               6 * u * v2 * v3 * v6 + 2 * u * v23 * v6 - u3 * v26 +
               2 * u * v3 * v26 - u2 * v36 + 2 * u * v2 * v36 - u * v236,
    .dual1236 = u1236 - u236 * v1 - u136 * v2 + 2 * u36 * v1 * v2 - u36 * v12 -
                u126 * v3 + 2 * u26 * v1 * v3 + 2 * u16 * v2 * v3 -
                6 * u6 * v1 * v2 * v3 + 2 * u6 * v12 * v3 - u26 * v13 +
                2 * u6 * v2 * v13 - u16 * v23 + 2 * u6 * v1 * v23 - u6 * v123 -
                u123 * v6 + 2 * u23 * v1 * v6 + 2 * u13 * v2 * v6 -
                6 * u3 * v1 * v2 * v6 + 2 * u3 * v12 * v6 + 2 * u12 * v3 * v6 -
                6 * u2 * v1 * v3 * v6 - 6 * u1 * v2 * v3 * v6 +
                24 * u * v1 * v2 * v3 * v6 - 6 * u * v12 * v3 * v6 +
                2 * u2 * v13 * v6 - 6 * u * v2 * v13 * v6 + 2 * u1 * v23 * v6 -
                6 * u * v1 * v23 * v6 + 2 * u * v123 * v6 - u23 * v16 +
                2 * u3 * v2 * v16 + 2 * u2 * v3 * v16 - 6 * u * v2 * v3 * v16 +
                2 * u * v23 * v16 - u13 * v26 + 2 * u3 * v1 * v26 +
                2 * u1 * v3 * v26 - 6 * u * v1 * v3 * v26 + 2 * u * v13 * v26 -
                u3 * v126 + 2 * u * v3 * v126 - u12 * v36 + 2 * u2 * v1 * v36 +
                2 * u1 * v2 * v36 - 6 * u * v1 * v2 * v36 + 2 * u * v12 * v36 -
                u2 * v136 + 2 * u * v2 * v136 - u1 * v236 + 2 * u * v1 * v236 -
                u * v1236,
    .dual46 = u46 - u6 * v4 - u4 * v6 + 2 * u * v4 * v6 - u * v46,
    .dual146 = u146 - u46 * v1 - u16 * v4 + 2 * u6 * v1 * v4 - u6 * v14 -
               u14 * v6 + 2 * u4 * v1 * v6 + 2 * u1 * v4 * v6 -
               6 * u * v1 * v4 * v6 + 2 * u * v14 * v6 - u4 * v16 +
               2 * u * v4 * v16 - u1 * v46 + 2 * u * v1 * v46 - u * v146,
    .dual246 = u246 - u46 * v2 - u26 * v4 + 2 * u6 * v2 * v4 - u6 * v24 -
               u24 * v6 + 2 * u4 * v2 * v6 + 2 * u2 * v4 * v6 -
               6 * u * v2 * v4 * v6 + 2 * u * v24 * v6 - u4 * v26 +
               2 * u * v4 * v26 - u2 * v46 + 2 * u * v2 * v46 - u * v246,
    .dual1246 = u1246 - u246 * v1 - u146 * v2 + 2 * u46 * v1 * v2 - u46 * v12 -
                u126 * v4 + 2 * u26 * v1 * v4 + 2 * u16 * v2 * v4 -
                6 * u6 * v1 * v2 * v4 + 2 * u6 * v12 * v4 - u26 * v14 +
                2 * u6 * v2 * v14 - u16 * v24 + 2 * u6 * v1 * v24 - u6 * v124 -
                u124 * v6 + 2 * u24 * v1 * v6 + 2 * u14 * v2 * v6 -
                6 * u4 * v1 * v2 * v6 + 2 * u4 * v12 * v6 + 2 * u12 * v4 * v6 -
                6 * u2 * v1 * v4 * v6 - 6 * u1 * v2 * v4 * v6 +
                24 * u * v1 * v2 * v4 * v6 - 6 * u * v12 * v4 * v6 +
                2 * u2 * v14 * v6 - 6 * u * v2 * v14 * v6 + 2 * u1 * v24 * v6 -
                6 * u * v1 * v24 * v6 + 2 * u * v124 * v6 - u24 * v16 +
                2 * u4 * v2 * v16 + 2 * u2 * v4 * v16 - 6 * u * v2 * v4 * v16 +
                2 * u * v24 * v16 - u14 * v26 + 2 * u4 * v1 * v26 +
                2 * u1 * v4 * v26 - 6 * u * v1 * v4 * v26 + 2 * u * v14 * v26 -
                u4 * v126 + 2 * u * v4 * v126 - u12 * v46 + 2 * u2 * v1 * v46 +
                2 * u1 * v2 * v46 - 6 * u * v1 * v2 * v46 + 2 * u * v12 * v46 -
                u2 * v146 + 2 * u * v2 * v146 - u1 * v246 + 2 * u * v1 * v246 -
                u * v1246,
    .dual346 = u346 - u46 * v3 - u36 * v4 + 2 * u6 * v3 * v4 - u6 * v34 -
               u34 * v6 + 2 * u4 * v3 * v6 + 2 * u3 * v4 * v6 -
               6 * u * v3 * v4 * v6 + 2 * u * v34 * v6 - u4 * v36 +
               2 * u * v4 * v36 - u3 * v46 + 2 * u * v3 * v46 - u * v346,
    .dual1346 = u1346 - u346 * v1 - u146 * v3 + 2 * u46 * v1 * v3 - u46 * v13 -
                u136 * v4 + 2 * u36 * v1 * v4 + 2 * u16 * v3 * v4 -
                6 * u6 * v1 * v3 * v4 + 2 * u6 * v13 * v4 - u36 * v14 +
                2 * u6 * v3 * v14 - u16 * v34 + 2 * u6 * v1 * v34 - u6 * v134 -
                u134 * v6 + 2 * u34 * v1 * v6 + 2 * u14 * v3 * v6 -
                6 * u4 * v1 * v3 * v6 + 2 * u4 * v13 * v6 + 2 * u13 * v4 * v6 -
                6 * u3 * v1 * v4 * v6 - 6 * u1 * v3 * v4 * v6 +
                24 * u * v1 * v3 * v4 * v6 - 6 * u * v13 * v4 * v6 +
                2 * u3 * v14 * v6 - 6 * u * v3 * v14 * v6 + 2 * u1 * v34 * v6 -
                6 * u * v1 * v34 * v6 + 2 * u * v134 * v6 - u34 * v16 +
                2 * u4 * v3 * v16 + 2 * u3 * v4 * v16 - 6 * u * v3 * v4 * v16 +
                2 * u * v34 * v16 - u14 * v36 + 2 * u4 * v1 * v36 +
                2 * u1 * v4 * v36 - 6 * u * v1 * v4 * v36 + 2 * u * v14 * v36 -
                u4 * v136 + 2 * u * v4 * v136 - u13 * v46 + 2 * u3 * v1 * v46 +
                2 * u1 * v3 * v46 - 6 * u * v1 * v3 * v46 + 2 * u * v13 * v46 -
                u3 * v146 + 2 * u * v3 * v146 - u1 * v346 + 2 * u * v1 * v346 -
                u * v1346,
    .dual2346 = u2346 - u346 * v2 - u246 * v3 + 2 * u46 * v2 * v3 - u46 * v23 -
                u236 * v4 + 2 * u36 * v2 * v4 + 2 * u26 * v3 * v4 -
                6 * u6 * v2 * v3 * v4 + 2 * u6 * v23 * v4 - u36 * v24 +
                2 * u6 * v3 * v24 - u26 * v34 + 2 * u6 * v2 * v34 - u6 * v234 -
                u234 * v6 + 2 * u34 * v2 * v6 + 2 * u24 * v3 * v6 -
                6 * u4 * v2 * v3 * v6 + 2 * u4 * v23 * v6 + 2 * u23 * v4 * v6 -
                6 * u3 * v2 * v4 * v6 - 6 * u2 * v3 * v4 * v6 +
                24 * u * v2 * v3 * v4 * v6 - 6 * u * v23 * v4 * v6 +
                2 * u3 * v24 * v6 - 6 * u * v3 * v24 * v6 + 2 * u2 * v34 * v6 -
                6 * u * v2 * v34 * v6 + 2 * u * v234 * v6 - u34 * v26 +
                2 * u4 * v3 * v26 + 2 * u3 * v4 * v26 - 6 * u * v3 * v4 * v26 +
                2 * u * v34 * v26 - u24 * v36 + 2 * u4 * v2 * v36 +
                2 * u2 * v4 * v36 - 6 * u * v2 * v4 * v36 + 2 * u * v24 * v36 -
                u4 * v236 + 2 * u * v4 * v236 - u23 * v46 + 2 * u3 * v2 * v46 +
                2 * u2 * v3 * v46 - 6 * u * v2 * v3 * v46 + 2 * u * v23 * v46 -
                u3 * v246 + 2 * u * v3 * v246 - u2 * v346 + 2 * u * v2 * v346 -
                u * v2346,
    .dual12346 =
            u12346 - u2346 * v1 - u1346 * v2 + 2 * u346 * v1 * v2 - u346 * v12 -
            u1246 * v3 + 2 * u246 * v1 * v3 + 2 * u146 * v2 * v3 -
            6 * u46 * v1 * v2 * v3 + 2 * u46 * v12 * v3 - u246 * v13 +
            2 * u46 * v2 * v13 - u146 * v23 + 2 * u46 * v1 * v23 - u46 * v123 -
            u1236 * v4 + 2 * u236 * v1 * v4 + 2 * u136 * v2 * v4 -
            6 * u36 * v1 * v2 * v4 + 2 * u36 * v12 * v4 + 2 * u126 * v3 * v4 -
            6 * u26 * v1 * v3 * v4 - 6 * u16 * v2 * v3 * v4 +
            24 * u6 * v1 * v2 * v3 * v4 - 6 * u6 * v12 * v3 * v4 +
            2 * u26 * v13 * v4 - 6 * u6 * v2 * v13 * v4 + 2 * u16 * v23 * v4 -
            6 * u6 * v1 * v23 * v4 + 2 * u6 * v123 * v4 - u236 * v14 +
            2 * u36 * v2 * v14 + 2 * u26 * v3 * v14 - 6 * u6 * v2 * v3 * v14 +
            2 * u6 * v23 * v14 - u136 * v24 + 2 * u36 * v1 * v24 +
            2 * u16 * v3 * v24 - 6 * u6 * v1 * v3 * v24 + 2 * u6 * v13 * v24 -
            u36 * v124 + 2 * u6 * v3 * v124 - u126 * v34 + 2 * u26 * v1 * v34 +
            2 * u16 * v2 * v34 - 6 * u6 * v1 * v2 * v34 + 2 * u6 * v12 * v34 -
            u26 * v134 + 2 * u6 * v2 * v134 - u16 * v234 + 2 * u6 * v1 * v234 -
            u6 * v1234 - u1234 * v6 + 2 * u234 * v1 * v6 + 2 * u134 * v2 * v6 -
            6 * u34 * v1 * v2 * v6 + 2 * u34 * v12 * v6 + 2 * u124 * v3 * v6 -
            6 * u24 * v1 * v3 * v6 - 6 * u14 * v2 * v3 * v6 +
            24 * u4 * v1 * v2 * v3 * v6 - 6 * u4 * v12 * v3 * v6 +
            2 * u24 * v13 * v6 - 6 * u4 * v2 * v13 * v6 + 2 * u14 * v23 * v6 -
            6 * u4 * v1 * v23 * v6 + 2 * u4 * v123 * v6 + 2 * u123 * v4 * v6 -
            6 * u23 * v1 * v4 * v6 - 6 * u13 * v2 * v4 * v6 +
            24 * u3 * v1 * v2 * v4 * v6 - 6 * u3 * v12 * v4 * v6 -
            6 * u12 * v3 * v4 * v6 + 24 * u2 * v1 * v3 * v4 * v6 +
            24 * u1 * v2 * v3 * v4 * v6 - 120 * u * v1 * v2 * v3 * v4 * v6 +
            24 * u * v12 * v3 * v4 * v6 - 6 * u2 * v13 * v4 * v6 +
            24 * u * v2 * v13 * v4 * v6 - 6 * u1 * v23 * v4 * v6 +
            24 * u * v1 * v23 * v4 * v6 - 6 * u * v123 * v4 * v6 +
            2 * u23 * v14 * v6 - 6 * u3 * v2 * v14 * v6 -
            6 * u2 * v3 * v14 * v6 + 24 * u * v2 * v3 * v14 * v6 -
            6 * u * v23 * v14 * v6 + 2 * u13 * v24 * v6 -
            6 * u3 * v1 * v24 * v6 - 6 * u1 * v3 * v24 * v6 +
            24 * u * v1 * v3 * v24 * v6 - 6 * u * v13 * v24 * v6 +
            2 * u3 * v124 * v6 - 6 * u * v3 * v124 * v6 + 2 * u12 * v34 * v6 -
            6 * u2 * v1 * v34 * v6 - 6 * u1 * v2 * v34 * v6 +
            24 * u * v1 * v2 * v34 * v6 - 6 * u * v12 * v34 * v6 +
            2 * u2 * v134 * v6 - 6 * u * v2 * v134 * v6 + 2 * u1 * v234 * v6 -
            6 * u * v1 * v234 * v6 + 2 * u * v1234 * v6 - u234 * v16 +
            2 * u34 * v2 * v16 + 2 * u24 * v3 * v16 - 6 * u4 * v2 * v3 * v16 +
            2 * u4 * v23 * v16 + 2 * u23 * v4 * v16 - 6 * u3 * v2 * v4 * v16 -
            6 * u2 * v3 * v4 * v16 + 24 * u * v2 * v3 * v4 * v16 -
            6 * u * v23 * v4 * v16 + 2 * u3 * v24 * v16 -
            6 * u * v3 * v24 * v16 + 2 * u2 * v34 * v16 -
            6 * u * v2 * v34 * v16 + 2 * u * v234 * v16 - u134 * v26 +
            2 * u34 * v1 * v26 + 2 * u14 * v3 * v26 - 6 * u4 * v1 * v3 * v26 +
            2 * u4 * v13 * v26 + 2 * u13 * v4 * v26 - 6 * u3 * v1 * v4 * v26 -
            6 * u1 * v3 * v4 * v26 + 24 * u * v1 * v3 * v4 * v26 -
            6 * u * v13 * v4 * v26 + 2 * u3 * v14 * v26 -
            6 * u * v3 * v14 * v26 + 2 * u1 * v34 * v26 -
            6 * u * v1 * v34 * v26 + 2 * u * v134 * v26 - u34 * v126 +
            2 * u4 * v3 * v126 + 2 * u3 * v4 * v126 - 6 * u * v3 * v4 * v126 +
            2 * u * v34 * v126 - u124 * v36 + 2 * u24 * v1 * v36 +
            2 * u14 * v2 * v36 - 6 * u4 * v1 * v2 * v36 + 2 * u4 * v12 * v36 +
            2 * u12 * v4 * v36 - 6 * u2 * v1 * v4 * v36 -
            6 * u1 * v2 * v4 * v36 + 24 * u * v1 * v2 * v4 * v36 -
            6 * u * v12 * v4 * v36 + 2 * u2 * v14 * v36 -
            6 * u * v2 * v14 * v36 + 2 * u1 * v24 * v36 -
            6 * u * v1 * v24 * v36 + 2 * u * v124 * v36 - u24 * v136 +
            2 * u4 * v2 * v136 + 2 * u2 * v4 * v136 - 6 * u * v2 * v4 * v136 +
            2 * u * v24 * v136 - u14 * v236 + 2 * u4 * v1 * v236 +
            2 * u1 * v4 * v236 - 6 * u * v1 * v4 * v236 + 2 * u * v14 * v236 -
            u4 * v1236 + 2 * u * v4 * v1236 - u123 * v46 + 2 * u23 * v1 * v46 +
            2 * u13 * v2 * v46 - 6 * u3 * v1 * v2 * v46 + 2 * u3 * v12 * v46 +
            2 * u12 * v3 * v46 - 6 * u2 * v1 * v3 * v46 -
            6 * u1 * v2 * v3 * v46 + 24 * u * v1 * v2 * v3 * v46 -
            6 * u * v12 * v3 * v46 + 2 * u2 * v13 * v46 -
            6 * u * v2 * v13 * v46 + 2 * u1 * v23 * v46 -
            6 * u * v1 * v23 * v46 + 2 * u * v123 * v46 - u23 * v146 +
            2 * u3 * v2 * v146 + 2 * u2 * v3 * v146 - 6 * u * v2 * v3 * v146 +
            2 * u * v23 * v146 - u13 * v246 + 2 * u3 * v1 * v246 +
            2 * u1 * v3 * v246 - 6 * u * v1 * v3 * v246 + 2 * u * v13 * v246 -
            u3 * v1246 + 2 * u * v3 * v1246 - u12 * v346 + 2 * u2 * v1 * v346 +
            2 * u1 * v2 * v346 - 6 * u * v1 * v2 * v346 + 2 * u * v12 * v346 -
            u2 * v1346 + 2 * u * v2 * v1346 - u1 * v2346 + 2 * u * v1 * v2346 -
            u * v12346,
    .dual56 = u56 - u6 * v5 - u5 * v6 + 2 * u * v5 * v6 - u * v56,
    .dual156 = u156 - u56 * v1 - u16 * v5 + 2 * u6 * v1 * v5 - u6 * v15 -
               u15 * v6 + 2 * u5 * v1 * v6 + 2 * u1 * v5 * v6 -
               6 * u * v1 * v5 * v6 + 2 * u * v15 * v6 - u5 * v16 +
               2 * u * v5 * v16 - u1 * v56 + 2 * u * v1 * v56 - u * v156,
    .dual256 = u256 - u56 * v2 - u26 * v5 + 2 * u6 * v2 * v5 - u6 * v25 -
               u25 * v6 + 2 * u5 * v2 * v6 + 2 * u2 * v5 * v6 -
               6 * u * v2 * v5 * v6 + 2 * u * v25 * v6 - u5 * v26 +
               2 * u * v5 * v26 - u2 * v56 + 2 * u * v2 * v56 - u * v256,
    .dual1256 = u1256 - u256 * v1 - u156 * v2 + 2 * u56 * v1 * v2 - u56 * v12 -
                u126 * v5 + 2 * u26 * v1 * v5 + 2 * u16 * v2 * v5 -
                6 * u6 * v1 * v2 * v5 + 2 * u6 * v12 * v5 - u26 * v15 +
                2 * u6 * v2 * v15 - u16 * v25 + 2 * u6 * v1 * v25 - u6 * v125 -
                u125 * v6 + 2 * u25 * v1 * v6 + 2 * u15 * v2 * v6 -
                6 * u5 * v1 * v2 * v6 + 2 * u5 * v12 * v6 + 2 * u12 * v5 * v6 -
                6 * u2 * v1 * v5 * v6 - 6 * u1 * v2 * v5 * v6 +
                24 * u * v1 * v2 * v5 * v6 - 6 * u * v12 * v5 * v6 +
                2 * u2 * v15 * v6 - 6 * u * v2 * v15 * v6 + 2 * u1 * v25 * v6 -
                6 * u * v1 * v25 * v6 + 2 * u * v125 * v6 - u25 * v16 +
                2 * u5 * v2 * v16 + 2 * u2 * v5 * v16 - 6 * u * v2 * v5 * v16 +
                2 * u * v25 * v16 - u15 * v26 + 2 * u5 * v1 * v26 +
                2 * u1 * v5 * v26 - 6 * u * v1 * v5 * v26 + 2 * u * v15 * v26 -
                u5 * v126 + 2 * u * v5 * v126 - u12 * v56 + 2 * u2 * v1 * v56 +
                2 * u1 * v2 * v56 - 6 * u * v1 * v2 * v56 + 2 * u * v12 * v56 -
                u2 * v156 + 2 * u * v2 * v156 - u1 * v256 + 2 * u * v1 * v256 -
                u * v1256,
    .dual356 = u356 - u56 * v3 - u36 * v5 + 2 * u6 * v3 * v5 - u6 * v35 -
               u35 * v6 + 2 * u5 * v3 * v6 + 2 * u3 * v5 * v6 -
               6 * u * v3 * v5 * v6 + 2 * u * v35 * v6 - u5 * v36 +
               2 * u * v5 * v36 - u3 * v56 + 2 * u * v3 * v56 - u * v356,
    .dual1356 = u1356 - u356 * v1 - u156 * v3 + 2 * u56 * v1 * v3 - u56 * v13 -
                u136 * v5 + 2 * u36 * v1 * v5 + 2 * u16 * v3 * v5 -
                6 * u6 * v1 * v3 * v5 + 2 * u6 * v13 * v5 - u36 * v15 +
                2 * u6 * v3 * v15 - u16 * v35 + 2 * u6 * v1 * v35 - u6 * v135 -
                u135 * v6 + 2 * u35 * v1 * v6 + 2 * u15 * v3 * v6 -
                6 * u5 * v1 * v3 * v6 + 2 * u5 * v13 * v6 + 2 * u13 * v5 * v6 -
                6 * u3 * v1 * v5 * v6 - 6 * u1 * v3 * v5 * v6 +
                24 * u * v1 * v3 * v5 * v6 - 6 * u * v13 * v5 * v6 +
                2 * u3 * v15 * v6 - 6 * u * v3 * v15 * v6 + 2 * u1 * v35 * v6 -
                6 * u * v1 * v35 * v6 + 2 * u * v135 * v6 - u35 * v16 +
                2 * u5 * v3 * v16 + 2 * u3 * v5 * v16 - 6 * u * v3 * v5 * v16 +
                2 * u * v35 * v16 - u15 * v36 + 2 * u5 * v1 * v36 +
                2 * u1 * v5 * v36 - 6 * u * v1 * v5 * v36 + 2 * u * v15 * v36 -
                u5 * v136 + 2 * u * v5 * v136 - u13 * v56 + 2 * u3 * v1 * v56 +
                2 * u1 * v3 * v56 - 6 * u * v1 * v3 * v56 + 2 * u * v13 * v56 -
                u3 * v156 + 2 * u * v3 * v156 - u1 * v356 + 2 * u * v1 * v356 -
                u * v1356,
    .dual2356 = u2356 - u356 * v2 - u256 * v3 + 2 * u56 * v2 * v3 - u56 * v23 -
                u236 * v5 + 2 * u36 * v2 * v5 + 2 * u26 * v3 * v5 -
                6 * u6 * v2 * v3 * v5 + 2 * u6 * v23 * v5 - u36 * v25 +
                2 * u6 * v3 * v25 - u26 * v35 + 2 * u6 * v2 * v35 - u6 * v235 -
                u235 * v6 + 2 * u35 * v2 * v6 + 2 * u25 * v3 * v6 -
                6 * u5 * v2 * v3 * v6 + 2 * u5 * v23 * v6 + 2 * u23 * v5 * v6 -
                6 * u3 * v2 * v5 * v6 - 6 * u2 * v3 * v5 * v6 +
                24 * u * v2 * v3 * v5 * v6 - 6 * u * v23 * v5 * v6 +
                2 * u3 * v25 * v6 - 6 * u * v3 * v25 * v6 + 2 * u2 * v35 * v6 -
                6 * u * v2 * v35 * v6 + 2 * u * v235 * v6 - u35 * v26 +
                2 * u5 * v3 * v26 + 2 * u3 * v5 * v26 - 6 * u * v3 * v5 * v26 +
                2 * u * v35 * v26 - u25 * v36 + 2 * u5 * v2 * v36 +
                2 * u2 * v5 * v36 - 6 * u * v2 * v5 * v36 + 2 * u * v25 * v36 -
                u5 * v236 + 2 * u * v5 * v236 - u23 * v56 + 2 * u3 * v2 * v56 +
                2 * u2 * v3 * v56 - 6 * u * v2 * v3 * v56 + 2 * u * v23 * v56 -
                u3 * v256 + 2 * u * v3 * v256 - u2 * v356 + 2 * u * v2 * v356 -
                u * v2356,
    .dual12356 =
            u12356 - u2356 * v1 - u1356 * v2 + 2 * u356 * v1 * v2 - u356 * v12 -
            u1256 * v3 + 2 * u256 * v1 * v3 + 2 * u156 * v2 * v3 -
            6 * u56 * v1 * v2 * v3 + 2 * u56 * v12 * v3 - u256 * v13 +
            2 * u56 * v2 * v13 - u156 * v23 + 2 * u56 * v1 * v23 - u56 * v123 -
            u1236 * v5 + 2 * u236 * v1 * v5 + 2 * u136 * v2 * v5 -
            6 * u36 * v1 * v2 * v5 + 2 * u36 * v12 * v5 + 2 * u126 * v3 * v5 -
            6 * u26 * v1 * v3 * v5 - 6 * u16 * v2 * v3 * v5 +
            24 * u6 * v1 * v2 * v3 * v5 - 6 * u6 * v12 * v3 * v5 +
            2 * u26 * v13 * v5 - 6 * u6 * v2 * v13 * v5 + 2 * u16 * v23 * v5 -
            6 * u6 * v1 * v23 * v5 + 2 * u6 * v123 * v5 - u236 * v15 +
            2 * u36 * v2 * v15 + 2 * u26 * v3 * v15 - 6 * u6 * v2 * v3 * v15 +
            2 * u6 * v23 * v15 - u136 * v25 + 2 * u36 * v1 * v25 +
            2 * u16 * v3 * v25 - 6 * u6 * v1 * v3 * v25 + 2 * u6 * v13 * v25 -
            u36 * v125 + 2 * u6 * v3 * v125 - u126 * v35 + 2 * u26 * v1 * v35 +
            2 * u16 * v2 * v35 - 6 * u6 * v1 * v2 * v35 + 2 * u6 * v12 * v35 -
            u26 * v135 + 2 * u6 * v2 * v135 - u16 * v235 + 2 * u6 * v1 * v235 -
            u6 * v1235 - u1235 * v6 + 2 * u235 * v1 * v6 + 2 * u135 * v2 * v6 -
            6 * u35 * v1 * v2 * v6 + 2 * u35 * v12 * v6 + 2 * u125 * v3 * v6 -
            6 * u25 * v1 * v3 * v6 - 6 * u15 * v2 * v3 * v6 +
            24 * u5 * v1 * v2 * v3 * v6 - 6 * u5 * v12 * v3 * v6 +
            2 * u25 * v13 * v6 - 6 * u5 * v2 * v13 * v6 + 2 * u15 * v23 * v6 -
            6 * u5 * v1 * v23 * v6 + 2 * u5 * v123 * v6 + 2 * u123 * v5 * v6 -
            6 * u23 * v1 * v5 * v6 - 6 * u13 * v2 * v5 * v6 +
            24 * u3 * v1 * v2 * v5 * v6 - 6 * u3 * v12 * v5 * v6 -
            6 * u12 * v3 * v5 * v6 + 24 * u2 * v1 * v3 * v5 * v6 +
            24 * u1 * v2 * v3 * v5 * v6 - 120 * u * v1 * v2 * v3 * v5 * v6 +
            24 * u * v12 * v3 * v5 * v6 - 6 * u2 * v13 * v5 * v6 +
            24 * u * v2 * v13 * v5 * v6 - 6 * u1 * v23 * v5 * v6 +
            24 * u * v1 * v23 * v5 * v6 - 6 * u * v123 * v5 * v6 +
            2 * u23 * v15 * v6 - 6 * u3 * v2 * v15 * v6 -
            6 * u2 * v3 * v15 * v6 + 24 * u * v2 * v3 * v15 * v6 -
            6 * u * v23 * v15 * v6 + 2 * u13 * v25 * v6 -
            6 * u3 * v1 * v25 * v6 - 6 * u1 * v3 * v25 * v6 +
            24 * u * v1 * v3 * v25 * v6 - 6 * u * v13 * v25 * v6 +
            2 * u3 * v125 * v6 - 6 * u * v3 * v125 * v6 + 2 * u12 * v35 * v6 -
            6 * u2 * v1 * v35 * v6 - 6 * u1 * v2 * v35 * v6 +
            24 * u * v1 * v2 * v35 * v6 - 6 * u * v12 * v35 * v6 +
            2 * u2 * v135 * v6 - 6 * u * v2 * v135 * v6 + 2 * u1 * v235 * v6 -
            6 * u * v1 * v235 * v6 + 2 * u * v1235 * v6 - u235 * v16 +
            2 * u35 * v2 * v16 + 2 * u25 * v3 * v16 - 6 * u5 * v2 * v3 * v16 +
            2 * u5 * v23 * v16 + 2 * u23 * v5 * v16 - 6 * u3 * v2 * v5 * v16 -
            6 * u2 * v3 * v5 * v16 + 24 * u * v2 * v3 * v5 * v16 -
            6 * u * v23 * v5 * v16 + 2 * u3 * v25 * v16 -
            6 * u * v3 * v25 * v16 + 2 * u2 * v35 * v16 -
            6 * u * v2 * v35 * v16 + 2 * u * v235 * v16 - u135 * v26 +
            2 * u35 * v1 * v26 + 2 * u15 * v3 * v26 - 6 * u5 * v1 * v3 * v26 +
            2 * u5 * v13 * v26 + 2 * u13 * v5 * v26 - 6 * u3 * v1 * v5 * v26 -
            6 * u1 * v3 * v5 * v26 + 24 * u * v1 * v3 * v5 * v26 -
            6 * u * v13 * v5 * v26 + 2 * u3 * v15 * v26 -
            6 * u * v3 * v15 * v26 + 2 * u1 * v35 * v26 -
            6 * u * v1 * v35 * v26 + 2 * u * v135 * v26 - u35 * v126 +
            2 * u5 * v3 * v126 + 2 * u3 * v5 * v126 - 6 * u * v3 * v5 * v126 +
            2 * u * v35 * v126 - u125 * v36 + 2 * u25 * v1 * v36 +
            2 * u15 * v2 * v36 - 6 * u5 * v1 * v2 * v36 + 2 * u5 * v12 * v36 +
            2 * u12 * v5 * v36 - 6 * u2 * v1 * v5 * v36 -
            6 * u1 * v2 * v5 * v36 + 24 * u * v1 * v2 * v5 * v36 -
            6 * u * v12 * v5 * v36 + 2 * u2 * v15 * v36 -
            6 * u * v2 * v15 * v36 + 2 * u1 * v25 * v36 -
            6 * u * v1 * v25 * v36 + 2 * u * v125 * v36 - u25 * v136 +
            2 * u5 * v2 * v136 + 2 * u2 * v5 * v136 - 6 * u * v2 * v5 * v136 +
            2 * u * v25 * v136 - u15 * v236 + 2 * u5 * v1 * v236 +
            2 * u1 * v5 * v236 - 6 * u * v1 * v5 * v236 + 2 * u * v15 * v236 -
            u5 * v1236 + 2 * u * v5 * v1236 - u123 * v56 + 2 * u23 * v1 * v56 +
            2 * u13 * v2 * v56 - 6 * u3 * v1 * v2 * v56 + 2 * u3 * v12 * v56 +
            2 * u12 * v3 * v56 - 6 * u2 * v1 * v3 * v56 -
            6 * u1 * v2 * v3 * v56 + 24 * u * v1 * v2 * v3 * v56 -
            6 * u * v12 * v3 * v56 + 2 * u2 * v13 * v56 -
            6 * u * v2 * v13 * v56 + 2 * u1 * v23 * v56 -
            6 * u * v1 * v23 * v56 + 2 * u * v123 * v56 - u23 * v156 +
            2 * u3 * v2 * v156 + 2 * u2 * v3 * v156 - 6 * u * v2 * v3 * v156 +
            2 * u * v23 * v156 - u13 * v256 + 2 * u3 * v1 * v256 +
            2 * u1 * v3 * v256 - 6 * u * v1 * v3 * v256 + 2 * u * v13 * v256 -
            u3 * v1256 + 2 * u * v3 * v1256 - u12 * v356 + 2 * u2 * v1 * v356 +
            2 * u1 * v2 * v356 - 6 * u * v1 * v2 * v356 + 2 * u * v12 * v356 -
            u2 * v1356 + 2 * u * v2 * v1356 - u1 * v2356 + 2 * u * v1 * v2356 -
            u * v12356,
    .dual456 = u456 - u56 * v4 - u46 * v5 + 2 * u6 * v4 * v5 - u6 * v45 -
               u45 * v6 + 2 * u5 * v4 * v6 + 2 * u4 * v5 * v6 -
               6 * u * v4 * v5 * v6 + 2 * u * v45 * v6 - u5 * v46 +
               2 * u * v5 * v46 - u4 * v56 + 2 * u * v4 * v56 - u * v456,
    .dual1456 = u1456 - u456 * v1 - u156 * v4 + 2 * u56 * v1 * v4 - u56 * v14 -
                u146 * v5 + 2 * u46 * v1 * v5 + 2 * u16 * v4 * v5 -
                6 * u6 * v1 * v4 * v5 + 2 * u6 * v14 * v5 - u46 * v15 +
                2 * u6 * v4 * v15 - u16 * v45 + 2 * u6 * v1 * v45 - u6 * v145 -
                u145 * v6 + 2 * u45 * v1 * v6 + 2 * u15 * v4 * v6 -
                6 * u5 * v1 * v4 * v6 + 2 * u5 * v14 * v6 + 2 * u14 * v5 * v6 -
                6 * u4 * v1 * v5 * v6 - 6 * u1 * v4 * v5 * v6 +
                24 * u * v1 * v4 * v5 * v6 - 6 * u * v14 * v5 * v6 +
                2 * u4 * v15 * v6 - 6 * u * v4 * v15 * v6 + 2 * u1 * v45 * v6 -
                6 * u * v1 * v45 * v6 + 2 * u * v145 * v6 - u45 * v16 +
                2 * u5 * v4 * v16 + 2 * u4 * v5 * v16 - 6 * u * v4 * v5 * v16 +
                2 * u * v45 * v16 - u15 * v46 + 2 * u5 * v1 * v46 +
                2 * u1 * v5 * v46 - 6 * u * v1 * v5 * v46 + 2 * u * v15 * v46 -
                u5 *