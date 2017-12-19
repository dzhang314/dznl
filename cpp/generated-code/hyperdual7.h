#ifndef DZNL_HYPERDUAL7_H
#define DZNL_HYPERDUAL7_H

struct hyperdual7 {
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
    double dual7;
    double dual17;
    double dual27;
    double dual127;
    double dual37;
    double dual137;
    double dual237;
    double dual1237;
    double dual47;
    double dual147;
    double dual247;
    double dual1247;
    double dual347;
    double dual1347;
    double dual2347;
    double dual12347;
    double dual57;
    double dual157;
    double dual257;
    double dual1257;
    double dual357;
    double dual1357;
    double dual2357;
    double dual12357;
    double dual457;
    double dual1457;
    double dual2457;
    double dual12457;
    double dual3457;
    double dual13457;
    double dual23457;
    double dual123457;
    double dual67;
    double dual167;
    double dual267;
    double dual1267;
    double dual367;
    double dual1367;
    double dual2367;
    double dual12367;
    double dual467;
    double dual1467;
    double dual2467;
    double dual12467;
    double dual3467;
    double dual13467;
    double dual23467;
    double dual123467;
    double dual567;
    double dual1567;
    double dual2567;
    double dual12567;
    double dual3567;
    double dual13567;
    double dual23567;
    double dual123567;
    double dual4567;
    double dual14567;
    double dual24567;
    double dual124567;
    double dual34567;
    double dual134567;
    double dual234567;
    double dual1234567;
};

hyperdual7 operator+(const hyperdual7 &x) {
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
            .dual7 = +x.dual7,
            .dual17 = +x.dual17,
            .dual27 = +x.dual27,
            .dual127 = +x.dual127,
            .dual37 = +x.dual37,
            .dual137 = +x.dual137,
            .dual237 = +x.dual237,
            .dual1237 = +x.dual1237,
            .dual47 = +x.dual47,
            .dual147 = +x.dual147,
            .dual247 = +x.dual247,
            .dual1247 = +x.dual1247,
            .dual347 = +x.dual347,
            .dual1347 = +x.dual1347,
            .dual2347 = +x.dual2347,
            .dual12347 = +x.dual12347,
            .dual57 = +x.dual57,
            .dual157 = +x.dual157,
            .dual257 = +x.dual257,
            .dual1257 = +x.dual1257,
            .dual357 = +x.dual357,
            .dual1357 = +x.dual1357,
            .dual2357 = +x.dual2357,
            .dual12357 = +x.dual12357,
            .dual457 = +x.dual457,
            .dual1457 = +x.dual1457,
            .dual2457 = +x.dual2457,
            .dual12457 = +x.dual12457,
            .dual3457 = +x.dual3457,
            .dual13457 = +x.dual13457,
            .dual23457 = +x.dual23457,
            .dual123457 = +x.dual123457,
            .dual67 = +x.dual67,
            .dual167 = +x.dual167,
            .dual267 = +x.dual267,
            .dual1267 = +x.dual1267,
            .dual367 = +x.dual367,
            .dual1367 = +x.dual1367,
            .dual2367 = +x.dual2367,
            .dual12367 = +x.dual12367,
            .dual467 = +x.dual467,
            .dual1467 = +x.dual1467,
            .dual2467 = +x.dual2467,
            .dual12467 = +x.dual12467,
            .dual3467 = +x.dual3467,
            .dual13467 = +x.dual13467,
            .dual23467 = +x.dual23467,
            .dual123467 = +x.dual123467,
            .dual567 = +x.dual567,
            .dual1567 = +x.dual1567,
            .dual2567 = +x.dual2567,
            .dual12567 = +x.dual12567,
            .dual3567 = +x.dual3567,
            .dual13567 = +x.dual13567,
            .dual23567 = +x.dual23567,
            .dual123567 = +x.dual123567,
            .dual4567 = +x.dual4567,
            .dual14567 = +x.dual14567,
            .dual24567 = +x.dual24567,
            .dual124567 = +x.dual124567,
            .dual34567 = +x.dual34567,
            .dual134567 = +x.dual134567,
            .dual234567 = +x.dual234567,
            .dual1234567 = +x.dual1234567,
    };
}

hyperdual7 operator-(const hyperdual7 &x) {
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
            .dual7 = -x.dual7,
            .dual17 = -x.dual17,
            .dual27 = -x.dual27,
            .dual127 = -x.dual127,
            .dual37 = -x.dual37,
            .dual137 = -x.dual137,
            .dual237 = -x.dual237,
            .dual1237 = -x.dual1237,
            .dual47 = -x.dual47,
            .dual147 = -x.dual147,
            .dual247 = -x.dual247,
            .dual1247 = -x.dual1247,
            .dual347 = -x.dual347,
            .dual1347 = -x.dual1347,
            .dual2347 = -x.dual2347,
            .dual12347 = -x.dual12347,
            .dual57 = -x.dual57,
            .dual157 = -x.dual157,
            .dual257 = -x.dual257,
            .dual1257 = -x.dual1257,
            .dual357 = -x.dual357,
            .dual1357 = -x.dual1357,
            .dual2357 = -x.dual2357,
            .dual12357 = -x.dual12357,
            .dual457 = -x.dual457,
            .dual1457 = -x.dual1457,
            .dual2457 = -x.dual2457,
            .dual12457 = -x.dual12457,
            .dual3457 = -x.dual3457,
            .dual13457 = -x.dual13457,
            .dual23457 = -x.dual23457,
            .dual123457 = -x.dual123457,
            .dual67 = -x.dual67,
            .dual167 = -x.dual167,
            .dual267 = -x.dual267,
            .dual1267 = -x.dual1267,
            .dual367 = -x.dual367,
            .dual1367 = -x.dual1367,
            .dual2367 = -x.dual2367,
            .dual12367 = -x.dual12367,
            .dual467 = -x.dual467,
            .dual1467 = -x.dual1467,
            .dual2467 = -x.dual2467,
            .dual12467 = -x.dual12467,
            .dual3467 = -x.dual3467,
            .dual13467 = -x.dual13467,
            .dual23467 = -x.dual23467,
            .dual123467 = -x.dual123467,
            .dual567 = -x.dual567,
            .dual1567 = -x.dual1567,
            .dual2567 = -x.dual2567,
            .dual12567 = -x.dual12567,
            .dual3567 = -x.dual3567,
            .dual13567 = -x.dual13567,
            .dual23567 = -x.dual23567,
            .dual123567 = -x.dual123567,
            .dual4567 = -x.dual4567,
            .dual14567 = -x.dual14567,
            .dual24567 = -x.dual24567,
            .dual124567 = -x.dual124567,
            .dual34567 = -x.dual34567,
            .dual134567 = -x.dual134567,
            .dual234567 = -x.dual234567,
            .dual1234567 = -x.dual1234567,
    };
}

hyperdual7 operator+(const hyperdual7 &x, const hyperdual7 &y) {
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
            .dual7 = x.dual7 + y.dual7,
            .dual17 = x.dual17 + y.dual17,
            .dual27 = x.dual27 + y.dual27,
            .dual127 = x.dual127 + y.dual127,
            .dual37 = x.dual37 + y.dual37,
            .dual137 = x.dual137 + y.dual137,
            .dual237 = x.dual237 + y.dual237,
            .dual1237 = x.dual1237 + y.dual1237,
            .dual47 = x.dual47 + y.dual47,
            .dual147 = x.dual147 + y.dual147,
            .dual247 = x.dual247 + y.dual247,
            .dual1247 = x.dual1247 + y.dual1247,
            .dual347 = x.dual347 + y.dual347,
            .dual1347 = x.dual1347 + y.dual1347,
            .dual2347 = x.dual2347 + y.dual2347,
            .dual12347 = x.dual12347 + y.dual12347,
            .dual57 = x.dual57 + y.dual57,
            .dual157 = x.dual157 + y.dual157,
            .dual257 = x.dual257 + y.dual257,
            .dual1257 = x.dual1257 + y.dual1257,
            .dual357 = x.dual357 + y.dual357,
            .dual1357 = x.dual1357 + y.dual1357,
            .dual2357 = x.dual2357 + y.dual2357,
            .dual12357 = x.dual12357 + y.dual12357,
            .dual457 = x.dual457 + y.dual457,
            .dual1457 = x.dual1457 + y.dual1457,
            .dual2457 = x.dual2457 + y.dual2457,
            .dual12457 = x.dual12457 + y.dual12457,
            .dual3457 = x.dual3457 + y.dual3457,
            .dual13457 = x.dual13457 + y.dual13457,
            .dual23457 = x.dual23457 + y.dual23457,
            .dual123457 = x.dual123457 + y.dual123457,
            .dual67 = x.dual67 + y.dual67,
            .dual167 = x.dual167 + y.dual167,
            .dual267 = x.dual267 + y.dual267,
            .dual1267 = x.dual1267 + y.dual1267,
            .dual367 = x.dual367 + y.dual367,
            .dual1367 = x.dual1367 + y.dual1367,
            .dual2367 = x.dual2367 + y.dual2367,
            .dual12367 = x.dual12367 + y.dual12367,
            .dual467 = x.dual467 + y.dual467,
            .dual1467 = x.dual1467 + y.dual1467,
            .dual2467 = x.dual2467 + y.dual2467,
            .dual12467 = x.dual12467 + y.dual12467,
            .dual3467 = x.dual3467 + y.dual3467,
            .dual13467 = x.dual13467 + y.dual13467,
            .dual23467 = x.dual23467 + y.dual23467,
            .dual123467 = x.dual123467 + y.dual123467,
            .dual567 = x.dual567 + y.dual567,
            .dual1567 = x.dual1567 + y.dual1567,
            .dual2567 = x.dual2567 + y.dual2567,
            .dual12567 = x.dual12567 + y.dual12567,
            .dual3567 = x.dual3567 + y.dual3567,
            .dual13567 = x.dual13567 + y.dual13567,
            .dual23567 = x.dual23567 + y.dual23567,
            .dual123567 = x.dual123567 + y.dual123567,
            .dual4567 = x.dual4567 + y.dual4567,
            .dual14567 = x.dual14567 + y.dual14567,
            .dual24567 = x.dual24567 + y.dual24567,
            .dual124567 = x.dual124567 + y.dual124567,
            .dual34567 = x.dual34567 + y.dual34567,
            .dual134567 = x.dual134567 + y.dual134567,
            .dual234567 = x.dual234567 + y.dual234567,
            .dual1234567 = x.dual1234567 + y.dual1234567,
    };
}

hyperdual7 operator-(const hyperdual7 &x, const hyperdual7 &y) {
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
            .dual7 = x.dual7 - y.dual7,
            .dual17 = x.dual17 - y.dual17,
            .dual27 = x.dual27 - y.dual27,
            .dual127 = x.dual127 - y.dual127,
            .dual37 = x.dual37 - y.dual37,
            .dual137 = x.dual137 - y.dual137,
            .dual237 = x.dual237 - y.dual237,
            .dual1237 = x.dual1237 - y.dual1237,
            .dual47 = x.dual47 - y.dual47,
            .dual147 = x.dual147 - y.dual147,
            .dual247 = x.dual247 - y.dual247,
            .dual1247 = x.dual1247 - y.dual1247,
            .dual347 = x.dual347 - y.dual347,
            .dual1347 = x.dual1347 - y.dual1347,
            .dual2347 = x.dual2347 - y.dual2347,
            .dual12347 = x.dual12347 - y.dual12347,
            .dual57 = x.dual57 - y.dual57,
            .dual157 = x.dual157 - y.dual157,
            .dual257 = x.dual257 - y.dual257,
            .dual1257 = x.dual1257 - y.dual1257,
            .dual357 = x.dual357 - y.dual357,
            .dual1357 = x.dual1357 - y.dual1357,
            .dual2357 = x.dual2357 - y.dual2357,
            .dual12357 = x.dual12357 - y.dual12357,
            .dual457 = x.dual457 - y.dual457,
            .dual1457 = x.dual1457 - y.dual1457,
            .dual2457 = x.dual2457 - y.dual2457,
            .dual12457 = x.dual12457 - y.dual12457,
            .dual3457 = x.dual3457 - y.dual3457,
            .dual13457 = x.dual13457 - y.dual13457,
            .dual23457 = x.dual23457 - y.dual23457,
            .dual123457 = x.dual123457 - y.dual123457,
            .dual67 = x.dual67 - y.dual67,
            .dual167 = x.dual167 - y.dual167,
            .dual267 = x.dual267 - y.dual267,
            .dual1267 = x.dual1267 - y.dual1267,
            .dual367 = x.dual367 - y.dual367,
            .dual1367 = x.dual1367 - y.dual1367,
            .dual2367 = x.dual2367 - y.dual2367,
            .dual12367 = x.dual12367 - y.dual12367,
            .dual467 = x.dual467 - y.dual467,
            .dual1467 = x.dual1467 - y.dual1467,
            .dual2467 = x.dual2467 - y.dual2467,
            .dual12467 = x.dual12467 - y.dual12467,
            .dual3467 = x.dual3467 - y.dual3467,
            .dual13467 = x.dual13467 - y.dual13467,
            .dual23467 = x.dual23467 - y.dual23467,
            .dual123467 = x.dual123467 - y.dual123467,
            .dual567 = x.dual567 - y.dual567,
            .dual1567 = x.dual1567 - y.dual1567,
            .dual2567 = x.dual2567 - y.dual2567,
            .dual12567 = x.dual12567 - y.dual12567,
            .dual3567 = x.dual3567 - y.dual3567,
            .dual13567 = x.dual13567 - y.dual13567,
            .dual23567 = x.dual23567 - y.dual23567,
            .dual123567 = x.dual123567 - y.dual123567,
            .dual4567 = x.dual4567 - y.dual4567,
            .dual14567 = x.dual14567 - y.dual14567,
            .dual24567 = x.dual24567 - y.dual24567,
            .dual124567 = x.dual124567 - y.dual124567,
            .dual34567 = x.dual34567 - y.dual34567,
            .dual134567 = x.dual134567 - y.dual134567,
            .dual234567 = x.dual234567 - y.dual234567,
            .dual1234567 = x.dual1234567 - y.dual1234567,
    };
}

hyperdual7 operator*(const hyperdual7 &x, const hyperdual7 &y) {
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
            .dual7 = x.dual7 * y.real + x.real * y.dual7,
            .dual17 = x.dual17 * y.real + x.dual7 * y.dual1 +
                      x.dual1 * y.dual7 + x.real * y.dual17,
            .dual27 = x.dual27 * y.real + x.dual7 * y.dual2 +
                      x.dual2 * y.dual7 + x.real * y.dual27,
            .dual127 = x.dual127 * y.real + x.dual27 * y.dual1 +
                       x.dual17 * y.dual2 + x.dual7 * y.dual12 +
                       x.dual12 * y.dual7 + x.dual2 * y.dual17 +
                       x.dual1 * y.dual27 + x.real * y.dual127,
            .dual37 = x.dual37 * y.real + x.dual7 * y.dual3 +
                      x.dual3 * y.dual7 + x.real * y.dual37,
            .dual137 = x.dual137 * y.real + x.dual37 * y.dual1 +
                       x.dual17 * y.dual3 + x.dual7 * y.dual13 +
                       x.dual13 * y.dual7 + x.dual3 * y.dual17 +
                       x.dual1 * y.dual37 + x.real * y.dual137,
            .dual237 = x.dual237 * y.real + x.dual37 * y.dual2 +
                       x.dual27 * y.dual3 + x.dual7 * y.dual23 +
                       x.dual23 * y.dual7 + x.dual3 * y.dual27 +
                       x.dual2 * y.dual37 + x.real * y.dual237,
            .dual1237 = x.dual1237 * y.real + x.dual237 * y.dual1 +
                        x.dual137 * y.dual2 + x.dual37 * y.dual12 +
                        x.dual127 * y.dual3 + x.dual27 * y.dual13 +
                        x.dual17 * y.dual23 + x.dual7 * y.dual123 +
                        x.dual123 * y.dual7 + x.dual23 * y.dual17 +
                        x.dual13 * y.dual27 + x.dual3 * y.dual127 +
                        x.dual12 * y.dual37 + x.dual2 * y.dual137 +
                        x.dual1 * y.dual237 + x.real * y.dual1237,
            .dual47 = x.dual47 * y.real + x.dual7 * y.dual4 +
                      x.dual4 * y.dual7 + x.real * y.dual47,
            .dual147 = x.dual147 * y.real + x.dual47 * y.dual1 +
                       x.dual17 * y.dual4 + x.dual7 * y.dual14 +
                       x.dual14 * y.dual7 + x.dual4 * y.dual17 +
                       x.dual1 * y.dual47 + x.real * y.dual147,
            .dual247 = x.dual247 * y.real + x.dual47 * y.dual2 +
                       x.dual27 * y.dual4 + x.dual7 * y.dual24 +
                       x.dual24 * y.dual7 + x.dual4 * y.dual27 +
                       x.dual2 * y.dual47 + x.real * y.dual247,
            .dual1247 = x.dual1247 * y.real + x.dual247 * y.dual1 +
                        x.dual147 * y.dual2 + x.dual47 * y.dual12 +
                        x.dual127 * y.dual4 + x.dual27 * y.dual14 +
                        x.dual17 * y.dual24 + x.dual7 * y.dual124 +
                        x.dual124 * y.dual7 + x.dual24 * y.dual17 +
                        x.dual14 * y.dual27 + x.dual4 * y.dual127 +
                        x.dual12 * y.dual47 + x.dual2 * y.dual147 +
                        x.dual1 * y.dual247 + x.real * y.dual1247,
            .dual347 = x.dual347 * y.real + x.dual47 * y.dual3 +
                       x.dual37 * y.dual4 + x.dual7 * y.dual34 +
                       x.dual34 * y.dual7 + x.dual4 * y.dual37 +
                       x.dual3 * y.dual47 + x.real * y.dual347,
            .dual1347 = x.dual1347 * y.real + x.dual347 * y.dual1 +
                        x.dual147 * y.dual3 + x.dual47 * y.dual13 +
                        x.dual137 * y.dual4 + x.dual37 * y.dual14 +
                        x.dual17 * y.dual34 + x.dual7 * y.dual134 +
                        x.dual134 * y.dual7 + x.dual34 * y.dual17 +
                        x.dual14 * y.dual37 + x.dual4 * y.dual137 +
                        x.dual13 * y.dual47 + x.dual3 * y.dual147 +
                        x.dual1 * y.dual347 + x.real * y.dual1347,
            .dual2347 = x.dual2347 * y.real + x.dual347 * y.dual2 +
                        x.dual247 * y.dual3 + x.dual47 * y.dual23 +
                        x.dual237 * y.dual4 + x.dual37 * y.dual24 +
                        x.dual27 * y.dual34 + x.dual7 * y.dual234 +
                        x.dual234 * y.dual7 + x.dual34 * y.dual27 +
                        x.dual24 * y.dual37 + x.dual4 * y.dual237 +
                        x.dual23 * y.dual47 + x.dual3 * y.dual247 +
                        x.dual2 * y.dual347 + x.real * y.dual2347,
            .dual12347 = x.dual12347 * y.real + x.dual2347 * y.dual1 +
                         x.dual1347 * y.dual2 + x.dual347 * y.dual12 +
                         x.dual1247 * y.dual3 + x.dual247 * y.dual13 +
                         x.dual147 * y.dual23 + x.dual47 * y.dual123 +
                         x.dual1237 * y.dual4 + x.dual237 * y.dual14 +
                         x.dual137 * y.dual24 + x.dual37 * y.dual124 +
                         x.dual127 * y.dual34 + x.dual27 * y.dual134 +
                         x.dual17 * y.dual234 + x.dual7 * y.dual1234 +
                         x.dual1234 * y.dual7 + x.dual234 * y.dual17 +
                         x.dual134 * y.dual27 + x.dual34 * y.dual127 +
                         x.dual124 * y.dual37 + x.dual24 * y.dual137 +
                         x.dual14 * y.dual237 + x.dual4 * y.dual1237 +
                         x.dual123 * y.dual47 + x.dual23 * y.dual147 +
                         x.dual13 * y.dual247 + x.dual3 * y.dual1247 +
                         x.dual12 * y.dual347 + x.dual2 * y.dual1347 +
                         x.dual1 * y.dual2347 + x.real * y.dual12347,
            .dual57 = x.dual57 * y.real + x.dual7 * y.dual5 +
                      x.dual5 * y.dual7 + x.real * y.dual57,
            .dual157 = x.dual157 * y.real + x.dual57 * y.dual1 +
                       x.dual17 * y.dual5 + x.dual7 * y.dual15 +
                       x.dual15 * y.dual7 + x.dual5 * y.dual17 +
                       x.dual1 * y.dual57 + x.real * y.dual157,
            .dual257 = x.dual257 * y.real + x.dual57 * y.dual2 +
                       x.dual27 * y.dual5 + x.dual7 * y.dual25 +
                       x.dual25 * y.dual7 + x.dual5 * y.dual27 +
                       x.dual2 * y.dual57 + x.real * y.dual257,
            .dual1257 = x.dual1257 * y.real + x.dual257 * y.dual1 +
                        x.dual157 * y.dual2 + x.dual57 * y.dual12 +
                        x.dual127 * y.dual5 + x.dual27 * y.dual15 +
                        x.dual17 * y.dual25 + x.dual7 * y.dual125 +
                        x.dual125 * y.dual7 + x.dual25 * y.dual17 +
                        x.dual15 * y.dual27 + x.dual5 * y.dual127 +
                        x.dual12 * y.dual57 + x.dual2 * y.dual157 +
                        x.dual1 * y.dual257 + x.real * y.dual1257,
            .dual357 = x.dual357 * y.real + x.dual57 * y.dual3 +
                       x.dual37 * y.dual5 + x.dual7 * y.dual35 +
                       x.dual35 * y.dual7 + x.dual5 * y.dual37 +
                       x.dual3 * y.dual57 + x.real * y.dual357,
            .dual1357 = x.dual1357 * y.real + x.dual357 * y.dual1 +
                        x.dual157 * y.dual3 + x.dual57 * y.dual13 +
                        x.dual137 * y.dual5 + x.dual37 * y.dual15 +
                        x.dual17 * y.dual35 + x.dual7 * y.dual135 +
                        x.dual135 * y.dual7 + x.dual35 * y.dual17 +
                        x.dual15 * y.dual37 + x.dual5 * y.dual137 +
                        x.dual13 * y.dual57 + x.dual3 * y.dual157 +
                        x.dual1 * y.dual357 + x.real * y.dual1357,
            .dual2357 = x.dual2357 * y.real + x.dual357 * y.dual2 +
                        x.dual257 * y.dual3 + x.dual57 * y.dual23 +
                        x.dual237 * y.dual5 + x.dual37 * y.dual25 +
                        x.dual27 * y.dual35 + x.dual7 * y.dual235 +
                        x.dual235 * y.dual7 + x.dual35 * y.dual27 +
                        x.dual25 * y.dual37 + x.dual5 * y.dual237 +
                        x.dual23 * y.dual57 + x.dual3 * y.dual257 +
                        x.dual2 * y.dual357 + x.real * y.dual2357,
            .dual12357 = x.dual12357 * y.real + x.dual2357 * y.dual1 +
                         x.dual1357 * y.dual2 + x.dual357 * y.dual12 +
                         x.dual1257 * y.dual3 + x.dual257 * y.dual13 +
                         x.dual157 * y.dual23 + x.dual57 * y.dual123 +
                         x.dual1237 * y.dual5 + x.dual237 * y.dual15 +
                         x.dual137 * y.dual25 + x.dual37 * y.dual125 +
                         x.dual127 * y.dual35 + x.dual27 * y.dual135 +
                         x.dual17 * y.dual235 + x.dual7 * y.dual1235 +
                         x.dual1235 * y.dual7 + x.dual235 * y.dual17 +
                         x.dual135 * y.dual27 + x.dual35 * y.dual127 +
                         x.dual125 * y.dual37 + x.dual25 * y.dual137 +
                         x.dual15 * y.dual237 + x.dual5 * y.dual1237 +
                         x.dual123 * y.dual57 + x.dual23 * y.dual157 +
                         x.dual13 * y.dual257 + x.dual3 * y.dual1257 +
                         x.dual12 * y.dual357 + x.dual2 * y.dual1357 +
                         x.dual1 * y.dual2357 + x.real * y.dual12357,
            .dual457 = x.dual457 * y.real + x.dual57 * y.dual4 +
                       x.dual47 * y.dual5 + x.dual7 * y.dual45 +
                       x.dual45 * y.dual7 + x.dual5 * y.dual47 +
                       x.dual4 * y.dual57 + x.real * y.dual457,
            .dual1457 = x.dual1457 * y.real + x.dual457 * y.dual1 +
                        x.dual157 * y.dual4 + x.dual57 * y.dual14 +
                        x.dual147 * y.dual5 + x.dual47 * y.dual15 +
                        x.dual17 * y.dual45 + x.dual7 * y.dual145 +
                        x.dual145 * y.dual7 + x.dual45 * y.dual17 +
                        x.dual15 * y.dual47 + x.dual5 * y.dual147 +
                        x.dual14 * y.dual57 + x.dual4 * y.dual157 +
                        x.dual1 * y.dual457 + x.real * y.dual1457,
            .dual2457 = x.dual2457 * y.real + x.dual457 * y.dual2 +
                        x.dual257 * y.dual4 + x.dual57 * y.dual24 +
                        x.dual247 * y.dual5 + x.dual47 * y.dual25 +
                        x.dual27 * y.dual45 + x.dual7 * y.dual245 +
                        x.dual245 * y.dual7 + x.dual45 * y.dual27 +
                        x.dual25 * y.dual47 + x.dual5 * y.dual247 +
                        x.dual24 * y.dual57 + x.dual4 * y.dual257 +
                        x.dual2 * y.dual457 + x.real * y.dual2457,
            .dual12457 = x.dual12457 * y.real + x.dual2457 * y.dual1 +
                         x.dual1457 * y.dual2 + x.dual457 * y.dual12 +
                         x.dual1257 * y.dual4 + x.dual257 * y.dual14 +
                         x.dual157 * y.dual24 + x.dual57 * y.dual124 +
                         x.dual1247 * y.dual5 + x.dual247 * y.dual15 +
                         x.dual147 * y.dual25 + x.dual47 * y.dual125 +
                         x.dual127 * y.dual45 + x.dual27 * y.dual145 +
                         x.dual17 * y.dual245 + x.dual7 * y.dual1245 +
                         x.dual1245 * y.dual7 + x.dual245 * y.dual17 +
                         x.dual145 * y.dual27 + x.dual45 * y.dual127 +
                         x.dual125 * y.dual47 + x.dual25 * y.dual147 +
                         x.dual15 * y.dual247 + x.dual5 * y.dual1247 +
                         x.dual124 * y.dual57 + x.dual24 * y.dual157 +
                         x.dual14 * y.dual257 + x.dual4 * y.dual1257 +
                         x.dual12 * y.dual457 + x.dual2 * y.dual1457 +
                         x.dual1 * y.dual2457 + x.real * y.dual12457,
            .dual3457 = x.dual3457 * y.real + x.dual457 * y.dual3 +
                        x.dual357 * y.dual4 + x.dual57 * y.dual34 +
                        x.dual347 * y.dual5 + x.dual47 * y.dual35 +
                        x.dual37 * y.dual45 + x.dual7 * y.dual345 +
                        x.dual345 * y.dual7 + x.dual45 * y.dual37 +
                        x.dual35 * y.dual47 + x.dual5 * y.dual347 +
                        x.dual34 * y.dual57 + x.dual4 * y.dual357 +
                        x.dual3 * y.dual457 + x.real * y.dual3457,
            .dual13457 = x.dual13457 * y.real + x.dual3457 * y.dual1 +
                         x.dual1457 * y.dual3 + x.dual457 * y.dual13 +
                         x.dual1357 * y.dual4 + x.dual357 * y.dual14 +
                         x.dual157 * y.dual34 + x.dual57 * y.dual134 +
                         x.dual1347 * y.dual5 + x.dual347 * y.dual15 +
                         x.dual147 * y.dual35 + x.dual47 * y.dual135 +
                         x.dual137 * y.dual45 + x.dual37 * y.dual145 +
                         x.dual17 * y.dual345 + x.dual7 * y.dual1345 +
                         x.dual1345 * y.dual7 + x.dual345 * y.dual17 +
                         x.dual145 * y.dual37 + x.dual45 * y.dual137 +
                         x.dual135 * y.dual47 + x.dual35 * y.dual147 +
                         x.dual15 * y.dual347 + x.dual5 * y.dual1347 +
                         x.dual134 * y.dual57 + x.dual34 * y.dual157 +
                         x.dual14 * y.dual357 + x.dual4 * y.dual1357 +
                         x.dual13 * y.dual457 + x.dual3 * y.dual1457 +
                         x.dual1 * y.dual3457 + x.real * y.dual13457,
            .dual23457 = x.dual23457 * y.real + x.dual3457 * y.dual2 +
                         x.dual2457 * y.dual3 + x.dual457 * y.dual23 +
                         x.dual2357 * y.dual4 + x.dual357 * y.dual24 +
                         x.dual257 * y.dual34 + x.dual57 * y.dual234 +
                         x.dual2347 * y.dual5 + x.dual347 * y.dual25 +
                         x.dual247 * y.dual35 + x.dual47 * y.dual235 +
                         x.dual237 * y.dual45 + x.dual37 * y.dual245 +
                         x.dual27 * y.dual345 + x.dual7 * y.dual2345 +
                         x.dual2345 * y.dual7 + x.dual345 * y.dual27 +
                         x.dual245 * y.dual37 + x.dual45 * y.dual237 +
                         x.dual235 * y.dual47 + x.dual35 * y.dual247 +
                         x.dual25 * y.dual347 + x.dual5 * y.dual2347 +
                         x.dual234 * y.dual57 + x.dual34 * y.dual257 +
                         x.dual24 * y.dual357 + x.dual4 * y.dual2357 +
                         x.dual23 * y.dual457 + x.dual3 * y.dual2457 +
                         x.dual2 * y.dual3457 + x.real * y.dual23457,
            .dual123457 = x.dual123457 * y.real + x.dual23457 * y.dual1 +
                          x.dual13457 * y.dual2 + x.dual3457 * y.dual12 +
                          x.dual12457 * y.dual3 + x.dual2457 * y.dual13 +
                          x.dual1457 * y.dual23 + x.dual457 * y.dual123 +
                          x.dual12357 * y.dual4 + x.dual2357 * y.dual14 +
                          x.dual1357 * y.dual24 + x.dual357 * y.dual124 +
                          x.dual1257 * y.dual34 + x.dual257 * y.dual134 +
                          x.dual157 * y.dual234 + x.dual57 * y.dual1234 +
                          x.dual12347 * y.dual5 + x.dual2347 * y.dual15 +
                          x.dual1347 * y.dual25 + x.dual347 * y.dual125 +
                          x.dual1247 * y.dual35 + x.dual247 * y.dual135 +
                          x.dual147 * y.dual235 + x.dual47 * y.dual1235 +
                          x.dual1237 * y.dual45 + x.dual237 * y.dual145 +
                          x.dual137 * y.dual245 + x.dual37 * y.dual1245 +
                          x.dual127 * y.dual345 + x.dual27 * y.dual1345 +
                          x.dual17 * y.dual2345 + x.dual7 * y.dual12345 +
                          x.dual12345 * y.dual7 + x.dual2345 * y.dual17 +
                          x.dual1345 * y.dual27 + x.dual345 * y.dual127 +
                          x.dual1245 * y.dual37 + x.dual245 * y.dual137 +
                          x.dual145 * y.dual237 + x.dual45 * y.dual1237 +
                          x.dual1235 * y.dual47 + x.dual235 * y.dual147 +
                          x.dual135 * y.dual247 + x.dual35 * y.dual1247 +
                          x.dual125 * y.dual347 + x.dual25 * y.dual1347 +
                          x.dual15 * y.dual2347 + x.dual5 * y.dual12347 +
                          x.dual1234 * y.dual57 + x.dual234 * y.dual157 +
                          x.dual134 * y.dual257 + x.dual34 * y.dual1257 +
                          x.dual124 * y.dual357 + x.dual24 * y.dual1357 +
                          x.dual14 * y.dual2357 + x.dual4 * y.dual12357 +
                          x.dual123 * y.dual457 + x.dual23 * y.dual1457 +
                          x.dual13 * y.dual2457 + x.dual3 * y.dual12457 +
                          x.dual12 * y.dual3457 + x.dual2 * y.dual13457 +
                          x.dual1 * y.dual23457 + x.real * y.dual123457,
            .dual67 = x.dual67 * y.real + x.dual7 * y.dual6 +
                      x.dual6 * y.dual7 + x.real * y.dual67,
            .dual167 = x.dual167 * y.real + x.dual67 * y.dual1 +
                       x.dual17 * y.dual6 + x.dual7 * y.dual16 +
                       x.dual16 * y.dual7 + x.dual6 * y.dual17 +
                       x.dual1 * y.dual67 + x.real * y.dual167,
            .dual267 = x.dual267 * y.real + x.dual67 * y.dual2 +
                       x.dual27 * y.dual6 + x.dual7 * y.dual26 +
                       x.dual26 * y.dual7 + x.dual6 * y.dual27 +
                       x.dual2 * y.dual67 + x.real * y.dual267,
            .dual1267 = x.dual1267 * y.real + x.dual267 * y.dual1 +
                        x.dual167 * y.dual2 + x.dual67 * y.dual12 +
                        x.dual127 * y.dual6 + x.dual27 * y.dual16 +
                        x.dual17 * y.dual26 + x.dual7 * y.dual126 +
                        x.dual126 * y.dual7 + x.dual26 * y.dual17 +
                        x.dual16 * y.dual27 + x.dual6 * y.dual127 +
                        x.dual12 * y.dual67 + x.dual2 * y.dual167 +
                        x.dual1 * y.dual267 + x.real * y.dual1267,
            .dual367 = x.dual367 * y.real + x.dual67 * y.dual3 +
                       x.dual37 * y.dual6 + x.dual7 * y.dual36 +
                       x.dual36 * y.dual7 + x.dual6 * y.dual37 +
                       x.dual3 * y.dual67 + x.real * y.dual367,
            .dual1367 = x.dual1367 * y.real + x.dual367 * y.dual1 +
                        x.dual167 * y.dual3 + x.dual67 * y.dual13 +
                        x.dual137 * y.dual6 + x.dual37 * y.dual16 +
                        x.dual17 * y.dual36 + x.dual7 * y.dual136 +
                        x.dual136 * y.dual7 + x.dual36 * y.dual17 +
                        x.dual16 * y.dual37 + x.dual6 * y.dual137 +
                        x.dual13 * y.dual67 + x.dual3 * y.dual167 +
                        x.dual1 * y.dual367 + x.real * y.dual1367,
            .dual2367 = x.dual2367 * y.real + x.dual367 * y.dual2 +
                        x.dual267 * y.dual3 + x.dual67 * y.dual23 +
                        x.dual237 * y.dual6 + x.dual37 * y.dual26 +
                        x.dual27 * y.dual36 + x.dual7 * y.dual236 +
                        x.dual236 * y.dual7 + x.dual36 * y.dual27 +
                        x.dual26 * y.dual37 + x.dual6 * y.dual237 +
                        x.dual23 * y.dual67 + x.dual3 * y.dual267 +
                        x.dual2 * y.dual367 + x.real * y.dual2367,
            .dual12367 = x.dual12367 * y.real + x.dual2367 * y.dual1 +
                         x.dual1367 * y.dual2 + x.dual367 * y.dual12 +
                         x.dual1267 * y.dual3 + x.dual267 * y.dual13 +
                         x.dual167 * y.dual23 + x.dual67 * y.dual123 +
                         x.dual1237 * y.dual6 + x.dual237 * y.dual16 +
                         x.dual137 * y.dual26 + x.dual37 * y.dual126 +
                         x.dual127 * y.dual36 + x.dual27 * y.dual136 +
                         x.dual17 * y.dual236 + x.dual7 * y.dual1236 +
                         x.dual1236 * y.dual7 + x.dual236 * y.dual17 +
                         x.dual136 * y.dual27 + x.dual36 * y.dual127 +
                         x.dual126 * y.dual37 + x.dual26 * y.dual137 +
                         x.dual16 * y.dual237 + x.dual6 * y.dual1237 +
                         x.dual123 * y.dual67 + x.dual23 * y.dual167 +
                         x.dual13 * y.dual267 + x.dual3 * y.dual1267 +
                         x.dual12 * y.dual367 + x.dual2 * y.dual1367 +
                         x.dual1 * y.dual2367 + x.real * y.dual12367,
            .dual467 = x.dual467 * y.real + x.dual67 * y.dual4 +
                       x.dual47 * y.dual6 + x.dual7 * y.dual46 +
                       x.dual46 * y.dual7 + x.dual6 * y.dual47 +
                       x.dual4 * y.dual67 + x.real * y.dual467,
            .dual1467 = x.dual1467 * y.real + x.dual467 * y.dual1 +
                        x.dual167 * y.dual4 + x.dual67 * y.dual14 +
                        x.dual147 * y.dual6 + x.dual47 * y.dual16 +
                        x.dual17 * y.dual46 + x.dual7 * y.dual146 +
                        x.dual146 * y.dual7 + x.dual46 * y.dual17 +
                        x.dual16 * y.dual47 + x.dual6 * y.dual147 +
                        x.dual14 * y.dual67 + x.dual4 * y.dual167 +
                        x.dual1 * y.dual467 + x.real * y.dual1467,
            .dual2467 = x.dual2467 * y.real + x.dual467 * y.dual2 +
                        x.dual267 * y.dual4 + x.dual67 * y.dual24 +
                        x.dual247 * y.dual6 + x.dual47 * y.dual26 +
                        x.dual27 * y.dual46 + x.dual7 * y.dual246 +
                        x.dual246 * y.dual7 + x.dual46 * y.dual27 +
                        x.dual26 * y.dual47 + x.dual6 * y.dual247 +
                        x.dual24 * y.dual67 + x.dual4 * y.dual267 +
                        x.dual2 * y.dual467 + x.real * y.dual2467,
            .dual12467 = x.dual12467 * y.real + x.dual2467 * y.dual1 +
                         x.dual1467 * y.dual2 + x.dual467 * y.dual12 +
                         x.dual1267 * y.dual4 + x.dual267 * y.dual14 +
                         x.dual167 * y.dual24 + x.dual67 * y.dual124 +
                         x.dual1247 * y.dual6 + x.dual247 * y.dual16 +
                         x.dual147 * y.dual26 + x.dual47 * y.dual126 +
                         x.dual127 * y.dual46 + x.dual27 * y.dual146 +
                         x.dual17 * y.dual246 + x.dual7 * y.dual1246 +
                         x.dual1246 * y.dual7 + x.dual246 * y.dual17 +
                         x.dual146 * y.dual27 + x.dual46 * y.dual127 +
                         x.dual126 * y.dual47 + x.dual26 * y.dual147 +
                         x.dual16 * y.dual247 + x.dual6 * y.dual1247 +
                         x.dual124 * y.dual67 + x.dual24 * y.dual167 +
                         x.dual14 * y.dual267 + x.dual4 * y.dual1267 +
                         x.dual12 * y.dual467 + x.dual2 * y.dual1467 +
                         x.dual1 * y.dual2467 + x.real * y.dual12467,
            .dual3467 = x.dual3467 * y.real + x.dual467 * y.dual3 +
                        x.dual367 * y.dual4 + x.dual67 * y.dual34 +
                        x.dual347 * y.dual6 + x.dual47 * y.dual36 +
                        x.dual37 * y.dual46 + x.dual7 * y.dual346 +
                        x.dual346 * y.dual7 + x.dual46 * y.dual37 +
                        x.dual36 * y.dual47 + x.dual6 * y.dual347 +
                        x.dual34 * y.dual67 + x.dual4 * y.dual367 +
                        x.dual3 * y.dual467 + x.real * y.dual3467,
            .dual13467 = x.dual13467 * y.real + x.dual3467 * y.dual1 +
                         x.dual1467 * y.dual3 + x.dual467 * y.dual13 +
                         x.dual1367 * y.dual4 + x.dual367 * y.dual14 +
                         x.dual167 * y.dual34 + x.dual67 * y.dual134 +
                         x.dual1347 * y.dual6 + x.dual347 * y.dual16 +
                         x.dual147 * y.dual36 + x.dual47 * y.dual136 +
                         x.dual137 * y.dual46 + x.dual37 * y.dual146 +
                         x.dual17 * y.dual346 + x.dual7 * y.dual1346 +
                         x.dual1346 * y.dual7 + x.dual346 * y.dual17 +
                         x.dual146 * y.dual37 + x.dual46 * y.dual137 +
                         x.dual136 * y.dual47 + x.dual36 * y.dual147 +
                         x.dual16 * y.dual347 + x.dual6 * y.dual1347 +
                         x.dual134 * y.dual67 + x.dual34 * y.dual167 +
                         x.dual14 * y.dual367 + x.dual4 * y.dual1367 +
                         x.dual13 * y.dual467 + x.dual3 * y.dual1467 +
                         x.dual1 * y.dual3467 + x.real * y.dual13467,
            .dual23467 = x.dual23467 * y.real + x.dual3467 * y.dual2 +
                         x.dual2467 * y.dual3 + x.dual467 * y.dual23 +
                         x.dual2367 * y.dual4 + x.dual367 * y.dual24 +
                         x.dual267 * y.dual34 + x.dual67 * y.dual234 +
                         x.dual2347 * y.dual6 + x.dual347 * y.dual26 +
                         x.dual247 * y.dual36 + x.dual47 * y.dual236 +
                         x.dual237 * y.dual46 + x.dual37 * y.dual246 +
                         x.dual27 * y.dual346 + x.dual7 * y.dual2346 +
                         x.dual2346 * y.dual7 + x.dual346 * y.dual27 +
                         x.dual246 * y.dual37 + x.dual46 * y.dual237 +
                         x.dual236 * y.dual47 + x.dual36 * y.dual247 +
                         x.dual26 * y.dual347 + x.dual6 * y.dual2347 +
                         x.dual234 * y.dual67 + x.dual34 * y.dual267 +
                         x.dual24 * y.dual367 + x.dual4 * y.dual2367 +
                         x.dual23 * y.dual467 + x.dual3 * y.dual2467 +
                         x.dual2 * y.dual3467 + x.real * y.dual23467,
            .dual123467 = x.dual123467 * y.real + x.dual23467 * y.dual1 +
                          x.dual13467 * y.dual2 + x.dual3467 * y.dual12 +
                          x.dual12467 * y.dual3 + x.dual2467 * y.dual13 +
                          x.dual1467 * y.dual23 + x.dual467 * y.dual123 +
                          x.dual12367 * y.dual4 + x.dual2367 * y.dual14 +
                          x.dual1367 * y.dual24 + x.dual367 * y.dual124 +
                          x.dual1267 * y.dual34 + x.dual267 * y.dual134 +
                          x.dual167 * y.dual234 + x.dual67 * y.dual1234 +
                          x.dual12347 * y.dual6 + x.dual2347 * y.dual16 +
                          x.dual1347 * y.dual26 + x.dual347 * y.dual126 +
                          x.dual1247 * y.dual36 + x.dual247 * y.dual136 +
                          x.dual147 * y.dual236 + x.dual47 * y.dual1236 +
                          x.dual1237 * y.dual46 + x.dual237 * y.dual146 +
                          x.dual137 * y.dual246 + x.dual37 * y.dual1246 +
                          x.dual127 * y.dual346 + x.dual27 * y.dual1346 +
                          x.dual17 * y.dual2346 + x.dual7 * y.dual12346 +
                          x.dual12346 * y.dual7 + x.dual2346 * y.dual17 +
                          x.dual1346 * y.dual27 + x.dual346 * y.dual127 +
                          x.dual1246 * y.dual37 + x.dual246 * y.dual137 +
                          x.dual146 * y.dual237 + x.dual46 * y.dual1237 +
                          x.dual1236 * y.dual47 + x.dual236 * y.dual147 +
                          x.dual136 * y.dual247 + x.dual36 * y.dual1247 +
                          x.dual126 * y.dual347 + x.dual26 * y.dual1347 +
                          x.dual16 * y.dual2347 + x.dual6 * y.dual12347 +
                          x.dual1234 * y.dual67 + x.dual234 * y.dual167 +
                          x.dual134 * y.dual267 + x.dual34 * y.dual1267 +
                          x.dual124 * y.dual367 + x.dual24 * y.dual1367 +
                          x.dual14 * y.dual2367 + x.dual4 * y.dual12367 +
                          x.dual123 * y.dual467 + x.dual23 * y.dual1467 +
                          x.dual13 * y.dual2467 + x.dual3 * y.dual12467 +
                          x.dual12 * y.dual3467 + x.dual2 * y.dual13467 +
                          x.dual1 * y.dual23467 + x.real * y.dual123467,
            .dual567 = x.dual567 * y.real + x.dual67 * y.dual5 +
                       x.dual57 * y.dual6 + x.dual7 * y.dual56 +
                       x.dual56 * y.dual7 + x.dual6 * y.dual57 +
                       x.dual5 * y.dual67 + x.real * y.dual567,
            .dual1567 = x.dual1567 * y.real + x.dual567 * y.dual1 +
                        x.dual167 * y.dual5 + x.dual67 * y.dual15 +
                        x.dual157 * y.dual6 + x.dual57 * y.dual16 +
                        x.dual17 * y.dual56 + x.dual7 * y.dual156 +
                        x.dual156 * y.dual7 + x.dual56 * y.dual17 +
                        x.dual16 * y.dual57 + x.dual6 * y.dual157 +
                        x.dual15 * y.dual67 + x.dual5 * y.dual167 +
                        x.dual1 * y.dual567 + x.real * y.dual1567,
            .dual2567 = x.dual2567 * y.real + x.dual567 * y.dual2 +
                        x.dual267 * y.dual5 + x.dual67 * y.dual25 +
                        x.dual257 * y.dual6 + x.dual57 * y.dual26 +
                        x.dual27 * y.dual56 + x.dual7 * y.dual256 +
                        x.dual256 * y.dual7 + x.dual56 * y.dual27 +
                        x.dual26 * y.dual57 + x.dual6 * y.dual257 +
                        x.dual25 * y.dual67 + x.dual5 * y.dual267 +
                        x.dual2 * y.dual567 + x.real * y.dual2567,
            .dual12567 = x.dual12567 * y.real + x.dual2567 * y.dual1 +
                         x.dual1567 * y.dual2 + x.dual567 * y.dual12 +
                         x.dual1267 * y.dual5 + x.dual267 * y.dual15 +
                         x.dual167 * y.dual25 + x.dual67 * y.dual125 +
                         x.dual1257 * y.dual6 + x.dual257 * y.dual16 +
                         x.dual157 * y.dual26 + x.dual57 * y.dual126 +
                         x.dual127 * y.dual56 + x.dual27 * y.dual156 +
                         x.dual17 * y.dual256 + x.dual7 * y.dual1256 +
                         x.dual1256 * y.dual7 + x.dual256 * y.dual17 +
                         x.dual156 * y.dual27 + x.dual56 * y.dual127 +
                         x.dual126 * y.dual57 + x.dual26 * y.dual157 +
                         x.dual16 * y.dual257 + x.dual6 * y.dual1257 +
                         x.dual125 * y.dual67 + x.dual25 * y.dual167 +
                         x.dual15 * y.dual267 + x.dual5 * y.dual1267 +
                         x.dual12 * y.dual567 + x.dual2 * y.dual1567 +
                         x.dual1 * y.dual2567 + x.real * y.dual12567,
            .dual3567 = x.dual3567 * y.real + x.dual567 * y.dual3 +
                        x.dual367 * y.dual5 + x.dual67 * y.dual35 +
                        x.dual357 * y.dual6 + x.dual57 * y.dual36 +
                        x.dual37 * y.dual56 + x.dual7 * y.dual356 +
                        x.dual356 * y.dual7 + x.dual56 * y.dual37 +
                        x.dual36 * y.dual57 + x.dual6 * y.dual357 +
                        x.dual35 * y.dual67 + x.dual5 * y.dual367 +
                        x.dual3 * y.dual567 + x.real * y.dual3567,
            .dual13567 = x.dual13567 * y.real + x.dual3567 * y.dual1 +
                         x.dual1567 * y.dual3 + x.dual567 * y.dual13 +
                         x.dual1367 * y.dual5 + x.dual367 * y.dual15 +
                         x.dual167 * y.dual35 + x.dual67 * y.dual135 +
                         x.dual1357 * y.dual6 + x.dual357 * y.dual16 +
                         x.dual157 * y.dual36 + x.dual57 * y.dual136 +
                         x.dual137 * y.dual56 + x.dual37 * y.dual156 +
                         x.dual17 * y.dual356 + x.dual7 * y.dual1356 +
                         x.dual1356 * y.dual7 + x.dual356 * y.dual17 +
                         x.dual156 * y.dual37 + x.dual56 * y.dual137 +
                         x.dual136 * y.dual57 + x.dual36 * y.dual157 +
                         x.dual16 * y.dual357 + x.dual6 * y.dual1357 +
                         x.dual135 * y.dual67 + x.dual35 * y.dual167 +
                         x.dual15 * y.dual367 + x.dual5 * y.dual1367 +
                         x.dual13 * y.dual567 + x.dual3 * y.dual1567 +
                         x.dual1 * y.dual3567 + x.real * y.dual13567,
            .dual23567 = x.dual23567 * y.real + x.dual3567 * y.dual2 +
                         x.dual2567 * y.dual3 + x.dual567 * y.dual23 +
                         x.dual2367 * y.dual5 + x.dual367 * y.dual25 +
                         x.dual267 * y.dual35 + x.dual67 * y.dual235 +
                         x.dual2357 * y.dual6 + x.dual357 * y.dual26 +
                         x.dual257 * y.dual36 + x.dual57 * y.dual236 +
                         x.dual237 * y.dual56 + x.dual37 * y.dual256 +
                         x.dual27 * y.dual356 + x.dual7 * y.dual2356 +
                         x.dual2356 * y.dual7 + x.dual356 * y.dual27 +
                         x.dual256 * y.dual37 + x.dual56 * y.dual237 +
                         x.dual236 * y.dual57 + x.dual36 * y.dual257 +
                         x.dual26 * y.dual357 + x.dual6 * y.dual2357 +
                         x.dual235 * y.dual67 + x.dual35 * y.dual267 +
                         x.dual25 * y.dual367 + x.dual5 * y.dual2367 +
                         x.dual23 * y.dual567 + x.dual3 * y.dual2567 +
                         x.dual2 * y.dual3567 + x.real * y.dual23567,
            .dual123567 = x.dual123567 * y.real + x.dual23567 * y.dual1 +
                          x.dual13567 * y.dual2 + x.dual3567 * y.dual12 +
                          x.dual12567 * y.dual3 + x.dual2567 * y.dual13 +
                          x.dual1567 * y.dual23 + x.dual567 * y.dual123 +
                          x.dual12367 * y.dual5 + x.dual2367 * y.dual15 +
                          x.dual1367 * y.dual25 + x.dual367 * y.dual125 +
                          x.dual1267 * y.dual35 + x.dual267 * y.dual135 +
                          x.dual167 * y.dual235 + x.dual67 * y.dual1235 +
                          x.dual12357 * y.dual6 + x.dual2357 * y.dual16 +
                          x.dual1357 * y.dual26 + x.dual357 * y.dual126 +
                          x.dual1257 * y.dual36 + x.dual257 * y.dual136 +
                          x.dual157 * y.dual236 + x.dual57 * y.dual1236 +
                          x.dual1237 * y.dual56 + x.dual237 * y.dual156 +
                          x.dual137 * y.dual256 + x.dual37 * y.dual1256 +
                          x.dual127 * y.dual356 + x.dual27 * y.dual1356 +
                          x.dual17 * y.dual2356 + x.dual7 * y.dual12356 +
                          x.dual12356 * y.dual7 + x.dual2356 * y.dual17 +
                          x.dual1356 * y.dual27 + x.dual356 * y.dual127 +
                          x.dual1256 * y.dual37 + x.dual256 * y.dual137 +
                          x.dual156 * y.dual237 + x.dual56 * y.dual1237 +
                          x.dual1236 * y.dual57 + x.dual236 * y.dual157 +
                          x.dual136 * y.dual257 + x.dual36 * y.dual1257 +
                          x.dual126 * y.dual357 + x.dual26 * y.dual1357 +
                          x.dual16 * y.dual2357 + x.dual6 * y.dual12357 +
                          x.dual1235 * y.dual67 + x.dual235 * y.dual167 +
                          x.dual135 * y.dual267 + x.dual35 * y.dual1267 +
                          x.dual125 * y.dual367 + x.dual25 * y.dual1367 +
                          x.dual15 * y.dual2367 + x.dual5 * y.dual12367 +
                          x.dual123 * y.dual567 + x.dual23 * y.dual1567 +
                          x.dual13 * y.dual2567 + x.dual3 * y.dual12567 +
                          x.dual12 * y.dual3567 + x.dual2 * y.dual13567 +
                          x.dual1 * y.dual23567 + x.real * y.dual123567,
            .dual4567 = x.dual4567 * y.real + x.dual567 * y.dual4 +
                        x.dual467 * y.dual5 + x.dual67 * y.dual45 +
                        x.dual457 * y.dual6 + x.dual57 * y.dual46 +
                        x.dual47 * y.dual56 + x.dual7 * y.dual456 +
                        x.dual456 * y.dual7 + x.dual56 * y.dual47 +
                        x.dual46 * y.dual57 + x.dual6 * y.dual457 +
                        x.dual45 * y.dual67 + x.dual5 * y.dual467 +
                        x.dual4 * y.dual567 + x.real * y.dual4567,
            .dual14567 = x.dual14567 * y.real + x.dual4567 * y.dual1 +
                         x.dual1567 * y.dual4 + x.dual567 * y.dual14 +
                         x.dual1467 * y.dual5 + x.dual467 * y.dual15 +
                         x.dual167 * y.dual45 + x.dual67 * y.dual145 +
                         x.dual1457 * y.dual6 + x.dual457 * y.dual16 +
                         x.dual157 * y.dual46 + x.dual57 * y.dual146 +
                         x.dual147 * y.dual56 + x.dual47 * y.dual156 +
                         x.dual17 * y.dual456 + x.dual7 * y.dual1456 +
                         x.dual1456 * y.dual7 + x.dual456 * y.dual17 +
                         x.dual156 * y.dual47 + x.dual56 * y.dual147 +
                         x.dual146 * y.dual57 + x.dual46 * y.dual157 +
                         x.dual16 * y.dual457 + x.dual6 * y.dual1457 +
                         x.dual145 * y.dual67 + x.dual45 * y.dual167 +
                         x.dual15 * y.dual467 + x.dual5 * y.dual1467 +
                         x.dual14 * y.dual567 + x.dual4 * y.dual1567 +
                         x.dual1 * y.dual4567 + x.real * y.dual14567,
            .dual24567 = x.dual24567 * y.real + x.dual4567 * y.dual2 +
                         x.dual2567 * y.dual4 + x.dual567 * y.dual24 +
                         x.dual2467 * y.dual5 + x.dual467 * y.dual25 +
                         x.dual267 * y.dual45 + x.dual67 * y.dual245 +
                         x.dual2457 * y.dual6 + x.dual457 * y.dual26 +
                         x.dual257 * y.dual46 + x.dual57 * y.dual246 +
                         x.dual247 * y.dual56 + x.dual47 * y.dual256 +
                         x.dual27 * y.dual456 + x.dual7 * y.dual2456 +
                         x.dual2456 * y.dual7 + x.dual456 * y.dual27 +
                         x.dual256 * y.dual47 + x.dual56 * y.dual247 +
                         x.dual246 * y.dual57 + x.dual46 * y.dual257 +
                         x.dual26 * y.dual457 + x.dual6 * y.dual2457 +
                         x.dual245 * y.dual67 + x.dual45 * y.dual267 +
                         x.dual25 * y.dual467 + x.dual5 * y.dual2467 +
                         x.dual24 * y.dual567 + x.dual4 * y.dual2567 +
                         x.dual2 * y.dual4567 + x.real * y.dual24567,
            .dual124567 = x.dual124567 * y.real + x.dual24567 * y.dual1 +
                          x.dual14567 * y.dual2 + x.dual4567 * y.dual12 +
                          x.dual12567 * y.dual4 + x.dual2567 * y.dual14 +
                          x.dual1567 * y.dual24 + x.dual567 * y.dual124 +
                          x.dual12467 * y.dual5 + x.dual2467 * y.dual15 +
                          x.dual1467 * y.dual25 + x.dual467 * y.dual125 +
                          x.dual1267 * y.dual45 + x.dual267 * y.dual145 +
                          x.dual167 * y.dual245 + x.dual67 * y.dual1245 +
                          x.dual12457 * y.dual6 + x.dual2457 * y.dual16 +
                          x.dual1457 * y.dual26 + x.dual457 * y.dual126 +
                          x.dual1257 * y.dual46 + x.dual257 * y.dual146 +
                          x.dual157 * y.dual246 + x.dual57 * y.dual1246 +
                          x.dual1247 * y.dual56 + x.dual247 * y.dual156 +
                          x.dual147 * y.dual256 + x.dual47 * y.dual1256 +
                          x.dual127 * y.dual456 + x.dual27 * y.dual1456 +
                          x.dual17 * y.dual2456 + x.dual7 * y.dual12456 +
                          x.dual12456 * y.dual7 + x.dual2456 * y.dual17 +
                          x.dual1456 * y.dual27 + x.dual456 * y.dual127 +
                          x.dual1256 * y.dual47 + x.dual256 * y.dual147 +
                          x.dual156 * y.dual247 + x.dual56 * y.dual1247 +
                          x.dual1246 * y.dual57 + x.dual246 * y.dual157 +
                          x.dual146 * y.dual257 + x.dual46 * y.dual1257 +
                          x.dual126 * y.dual457 + x.dual26 * y.dual1457 +
                          x.dual16 * y.dual2457 + x.dual6 * y.dual12457 +
                          x.dual1245 * y.dual67 + x.dual245 * y.dual167 +
                          x.dual145 * y.dual267 + x.dual45 * y.dual1267 +
                          x.dual125 * y.dual467 + x.dual25 * y.dual1467 +
                          x.dual15 * y.dual2467 + x.dual5 * y.dual12467 +
                          x.dual124 * y.dual567 + x.dual24 * y.dual1567 +
                          x.dual14 * y.dual2567 + x.dual4 * y.dual12567 +
                          x.dual12 * y.dual4567 + x.dual2 * y.dual14567 +
                          x.dual1 * y.dual24567 + x.real * y.dual124567,
            .dual34567 = x.dual34567 * y.real + x.dual4567 * y.dual3 +
                         x.dual3567 * y.dual4 + x.dual567 * y.dual34 +
                         x.dual3467 * y.dual5 + x.dual467 * y.dual35 +
                         x.dual367 * y.dual45 + x.dual67 * y.dual345 +
                         x.dual3457 * y.dual6 + x.dual457 * y.dual36 +
                         x.dual357 * y.dual46 + x.dual57 * y.dual346 +
                         x.dual347 * y.dual56 + x.dual47 * y.dual356 +
                         x.dual37 * y.dual456 + x.dual7 * y.dual3456 +
                         x.dual3456 * y.dual7 + x.dual456 * y.dual37 +
                         x.dual356 * y.dual47 + x.dual56 * y.dual347 +
                         x.dual346 * y.dual57 + x.dual46 * y.dual357 +
                         x.dual36 * y.dual457 + x.dual6 * y.dual3457 +
                         x.dual345 * y.dual67 + x.dual45 * y.dual367 +
                         x.dual35 * y.dual467 + x.dual5 * y.dual3467 +
                         x.dual34 * y.dual567 + x.dual4 * y.dual3567 +
                         x.dual3 * y.dual4567 + x.real * y.dual34567,
            .dual134567 = x.dual134567 * y.real + x.dual34567 * y.dual1 +
                          x.dual14567 * y.dual3 + x.dual4567 * y.dual13 +
                          x.dual13567 * y.dual4 + x.dual3567 * y.dual14 +
                          x.dual1567 * y.dual34 + x.dual567 * y.dual134 +
                          x.dual13467 * y.dual5 + x.dual3467 * y.dual15 +
                          x.dual1467 * y.dual35 + x.dual467 * y.dual135 +
                          x.dual1367 * y.dual45 + x.dual367 * y.dual145 +
                          x.dual167 * y.dual345 + x.dual67 * y.dual1345 +
                          x.dual13457 * y.dual6 + x.dual3457 * y.dual16 +
                          x.dual1457 * y.dual36 + x.dual457 * y.dual136 +
                          x.dual1357 * y.dual46 + x.dual357 * y.dual146 +
                          x.dual157 * y.dual346 + x.dual57 * y.dual1346 +
                          x.dual1347 * y.dual56 + x.dual347 * y.dual156 +
                          x.dual147 * y.dual356 + x.dual47 * y.dual1356 +
                          x.dual137 * y.dual456 + x.dual37 * y.dual1456 +
                          x.dual17 * y.dual3456 + x.dual7 * y.dual13456 +
                          x.dual13456 * y.dual7 + x.dual3456 * y.dual17 +
                          x.dual1456 * y.dual37 + x.dual456 * y.dual137 +
                          x.dual1356 * y.dual47 + x.dual356 * y.dual147 +
                          x.dual156 * y.dual347 + x.dual56 * y.dual1347 +
                          x.dual1346 * y.dual57 + x.dual346 * y.dual157 +
                          x.dual146 * y.dual357 + x.dual46 * y.dual1357 +
                          x.dual136 * y.dual457 + x.dual36 * y.dual1457 +
                          x.dual16 * y.dual3457 + x.dual6 * y.dual13457 +
                          x.dual1345 * y.dual67 + x.dual345 * y.dual167 +
                          x.dual145 * y.dual367 + x.dual45 * y.dual1367 +
                          x.dual135 * y.dual467 + x.dual35 * y.dual1467 +
                          x.dual15 * y.dual3467 + x.dual5 * y.dual13467 +
                          x.dual134 * y.dual567 + x.dual34 * y.dual1567 +
                          x.dual14 * y.dual3567 + x.dual4 * y.dual13567 +
                          x.dual13 * y.dual4567 + x.dual3 * y.dual14567 +
                          x.dual1 * y.dual34567 + x.real * y.dual134567,
            .dual234567 = x.dual234567 * y.real + x.dual34567 * y.dual2 +
                          x.dual24567 * y.dual3 + x.dual4567 * y.dual23 +
                          x.dual23567 * y.dual4 + x.dual3567 * y.dual24 +
                          x.dual2567 * y.dual34 + x.dual567 * y.dual234 +
                          x.dual23467 * y.dual5 + x.dual3467 * y.dual25 +
                          x.dual2467 * y.dual35 + x.dual467 * y.dual235 +
                          x.dual2367 * y.dual45 + x.dual367 * y.dual245 +
                          x.dual267 * y.dual345 + x.dual67 * y.dual2345 +
                          x.dual23457 * y.dual6 + x.dual3457 * y.dual26 +
                          x.dual2457 * y.dual36 + x.dual457 * y.dual236 +
                          x.dual2357 * y.dual46 + x.dual357 * y.dual246 +
                          x.dual257 * y.dual346 + x.dual57 * y.dual2346 +
                          x.dual2347 * y.dual56 + x.dual347 * y.dual256 +
                          x.dual247 * y.dual356 + x.dual47 * y.dual2356 +
                          x.dual237 * y.dual456 + x.dual37 * y.dual2456 +
                          x.dual27 * y.dual3456 + x.dual7 * y.dual23456 +
                          x.dual23456 * y.dual7 + x.dual3456 * y.dual27 +
                          x.dual2456 * y.dual37 + x.dual456 * y.dual237 +
                          x.dual2356 * y.dual47 + x.dual356 * y.dual247 +
                          x.dual256 * y.dual347 + x.dual56 * y.dual2347 +
                          x.dual2346 * y.dual57 + x.dual346 * y.dual257 +
                          x.dual246 * y.dual357 + x.dual46 * y.dual2357 +
                          x.dual236 * y.dual457 + x.dual36 * y.dual2457 +
                          x.dual26 * y.dual3457 + x.dual6 * y.dual23457 +
                          x.dual2345 * y.dual67 + x.dual345 * y.dual267 +
                          x.dual245 * y.dual367 + x.dual45 * y.dual2367 +
                          x.dual235 * y.dual467 + x.dual35 * y.dual2467 +
                          x.dual25 * y.dual3467 + x.dual5 * y.dual23467 +
                          x.dual234 * y.dual567 + x.dual34 * y.dual2567 +
                          x.dual24 * y.dual3567 + x.dual4 * y.dual23567 +
                          x.dual23 * y.dual4567 + x.dual3 * y.dual24567 +
                          x.dual2 * y.dual34567 + x.real * y.dual234567,
            .dual1234567 = x.dual1234567 * y.real + x.dual234567 * y.dual1 +
                           x.dual134567 * y.dual2 + x.dual34567 * y.dual12 +
                           x.dual124567 * y.dual3 + x.dual24567 * y.dual13 +
                           x.dual14567 * y.dual23 + x.dual4567 * y.dual123 +
                           x.dual123567 * y.dual4 + x.dual23567 * y.dual14 +
                           x.dual13567 * y.dual24 + x.dual3567 * y.dual124 +
                           x.dual12567 * y.dual34 + x.dual2567 * y.dual134 +
                           x.dual1567 * y.dual234 + x.dual567 * y.dual1234 +
                           x.dual123467 * y.dual5 + x.dual23467 * y.dual15 +
                           x.dual13467 * y.dual25 + x.dual3467 * y.dual125 +
                           x.dual12467 * y.dual35 + x.dual2467 * y.dual135 +
                           x.dual1467 * y.dual235 + x.dual467 * y.dual1235 +
                           x.dual12367 * y.dual45 + x.dual2367 * y.dual145 +
                           x.dual1367 * y.dual245 + x.dual367 * y.dual1245 +
                           x.dual1267 * y.dual345 + x.dual267 * y.dual1345 +
                           x.dual167 * y.dual2345 + x.dual67 * y.dual12345 +
                           x.dual123457 * y.dual6 + x.dual23457 * y.dual16 +
                           x.dual13457 * y.dual26 + x.dual3457 * y.dual126 +
                           x.dual12457 * y.dual36 + x.dual2457 * y.dual136 +
                           x.dual1457 * y.dual236 + x.dual457 * y.dual1236 +
                           x.dual12357 * y.dual46 + x.dual2357 * y.dual146 +
                           x.dual1357 * y.dual246 + x.dual357 * y.dual1246 +
                           x.dual1257 * y.dual346 + x.dual257 * y.dual1346 +
                           x.dual157 * y.dual2346 + x.dual57 * y.dual12346 +
                           x.dual12347 * y.dual56 + x.dual2347 * y.dual156 +
                           x.dual1347 * y.dual256 + x.dual347 * y.dual1256 +
                           x.dual1247 * y.dual356 + x.dual247 * y.dual1356 +
                           x.dual147 * y.dual2356 + x.dual47 * y.dual12356 +
                           x.dual1237 * y.dual456 + x.dual237 * y.dual1456 +
                           x.dual137 * y.dual2456 + x.dual37 * y.dual12456 +
                           x.dual127 * y.dual3456 + x.dual27 * y.dual13456 +
                           x.dual17 * y.dual23456 + x.dual7 * y.dual123456 +
                           x.dual123456 * y.dual7 + x.dual23456 * y.dual17 +
                           x.dual13456 * y.dual27 + x.dual3456 * y.dual127 +
                           x.dual12456 * y.dual37 + x.dual2456 * y.dual137 +
                           x.dual1456 * y.dual237 + x.dual456 * y.dual1237 +
                           x.dual12356 * y.dual47 + x.dual2356 * y.dual147 +
                           x.dual1356 * y.dual247 + x.dual356 * y.dual1247 +
                           x.dual1256 * y.dual347 + x.dual256 * y.dual1347 +
                           x.dual156 * y.dual2347 + x.dual56 * y.dual12347 +
                           x.dual12346 * y.dual57 + x.dual2346 * y.dual157 +
                           x.dual1346 * y.dual257 + x.dual346 * y.dual1257 +
                           x.dual1246 * y.dual357 + x.dual246 * y.dual1357 +
                           x.dual146 * y.dual2357 + x.dual46 * y.dual12357 +
                           x.dual1236 * y.dual457 + x.dual236 * y.dual1457 +
                           x.dual136 * y.dual2457 + x.dual36 * y.dual12457 +
                           x.dual126 * y.dual3457 + x.dual26 * y.dual13457 +
                           x.dual16 * y.dual23457 + x.dual6 * y.dual123457 +
                           x.dual12345 * y.dual67 + x.dual2345 * y.dual167 +
                           x.dual1345 * y.dual267 + x.dual345 * y.dual1267 +
                           x.dual1245 * y.dual367 + x.dual245 * y.dual1367 +
                           x.dual145 * y.dual2367 + x.dual45 * y.dual12367 +
                           x.dual1235 * y.dual467 + x.dual235 * y.dual1467 +
                           x.dual135 * y.dual2467 + x.dual35 * y.dual12467 +
                           x.dual125 * y.dual3467 + x.dual25 * y.dual13467 +
                           x.dual15 * y.dual23467 + x.dual5 * y.dual123467 +
                           x.dual1234 * y.dual567 + x.dual234 * y.dual1567 +
                           x.dual134 * y.dual2567 + x.dual34 * y.dual12567 +
                           x.dual124 * y.dual3567 + x.dual24 * y.dual13567 +
                           x.dual14 * y.dual23567 + x.dual4 * y.dual123567 +
                           x.dual123 * y.dual4567 + x.dual23 * y.dual14567 +
                           x.dual13 * y.dual24567 + x.dual3 * y.dual124567 +
                           x.dual12 * y.dual34567 + x.dual2 * y.dual134567 +
                           x.dual1 * y.dual234567 + x.real * y.dual1234567,
    };
}

hyperdual7 operator/(const hyperdual7 &x, const hyperdual7 &y) {
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
    const auto u7 = x.dual7 / y.real;
    const auto u17 = x.dual17 / y.real;
    const auto u27 = x.dual27 / y.real;
    const auto u127 = x.dual127 / y.real;
    const auto u37 = x.dual37 / y.real;
    const auto u137 = x.dual137 / y.real;
    const auto u237 = x.dual237 / y.real;
    const auto u1237 = x.dual1237 / y.real;
    const auto u47 = x.dual47 / y.real;
    const auto u147 = x.dual147 / y.real;
    const auto u247 = x.dual247 / y.real;
    const auto u1247 = x.dual1247 / y.real;
    const auto u347 = x.dual347 / y.real;
    const auto u1347 = x.dual1347 / y.real;
    const auto u2347 = x.dual2347 / y.real;
    const auto u12347 = x.dual12347 / y.real;
    const auto u57 = x.dual57 / y.real;
    const auto u157 = x.dual157 / y.real;
    const auto u257 = x.dual257 / y.real;
    const auto u1257 = x.dual1257 / y.real;
    const auto u357 = x.dual357 / y.real;
    const auto u1357 = x.dual1357 / y.real;
    const auto u2357 = x.dual2357 / y.real;
    const auto u12357 = x.dual12357 / y.real;
    const auto u457 = x.dual457 / y.real;
    const auto u1457 = x.dual1457 / y.real;
    const auto u2457 = x.dual2457 / y.real;
    const auto u12457 = x.dual12457 / y.real;
    const auto u3457 = x.dual3457 / y.real;
    const auto u13457 = x.dual13457 / y.real;
    const auto u23457 = x.dual23457 / y.real;
    const auto u123457 = x.dual123457 / y.real;
    const auto u67 = x.dual67 / y.real;
    const auto u167 = x.dual167 / y.real;
    const auto u267 = x.dual267 / y.real;
    const auto u1267 = x.dual1267 / y.real;
    const auto u367 = x.dual367 / y.real;
    const auto u1367 = x.dual1367 / y.real;
    const auto u2367 = x.dual2367 / y.real;
    const auto u12367 = x.dual12367 / y.real;
    const auto u467 = x.dual467 / y.real;
    const auto u1467 = x.dual1467 / y.real;
    const auto u2467 = x.dual2467 / y.real;
    const auto u12467 = x.dual12467 / y.real;
    const auto u3467 = x.dual3467 / y.real;
    const auto u13467 = x.dual13467 / y.real;
    const auto u23467 = x.dual23467 / y.real;
    const auto u123467 = x.dual123467 / y.real;
    const auto u567 = x.dual567 / y.real;
    const auto u1567 = x.dual1567 / y.real;
    const auto u2567 = x.dual2567 / y.real;
    const auto u12567 = x.dual12567 / y.real;
    const auto u3567 = x.dual3567 / y.real;
    const auto u13567 = x.dual13567 / y.real;
    const auto u23567 = x.dual23567 / y.real;
    const auto u123567 = x.dual123567 / y.real;
    const auto u4567 = x.dual4567 / y.real;
    const auto u14567 = x.dual14567 / y.real;
    const auto u24567 = x.dual24567 / y.real;
    const auto u124567 = x.dual124567 / y.real;
    const auto u34567 = x.dual34567 / y.real;
    const auto u134567 = x.dual134567 / y.real;
    const auto u234567 = x.dual234567 / y.real;
    const auto u1234567 = x.dual1234567 / y.real;
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
    const auto v7 = y.dual7 / y.real;
    const auto v17 = y.dual17 / y.real;
    const auto v27 = y.dual27 / y.real;
    const auto v127 = y.dual127 / y.real;
    const auto v37 = y.dual37 / y.real;
    const auto v137 = y.dual137 / y.real;
    const auto v237 = y.dual237 / y.real;
    const auto v1237 = y.dual1237 / y.real;
    const auto v47 = y.dual47 / y.real;
    const auto v147 = y.dual147 / y.real;
    const auto v247 = y.dual247 / y.real;
    const auto v1247 = y.dual1247 / y.real;
    const auto v347 = y.dual347 / y.real;
    const auto v1347 = y.dual1347 / y.real;
    const auto v2347 = y.dual2347 / y.real;
    const auto v12347 = y.dual12347 / y.real;
    const auto v57 = y.dual57 / y.real;
    const auto v157 = y.dual157 / y.real;
    const auto v257 = y.dual257 / y.real;
    const auto v1257 = y.dual1257 / y.real;
    const auto v357 = y.dual357 / y.real;
    const auto v1357 = y.dual1357 / y.real;
    const auto v2357 = y.dual2357 / y.real;
    const auto v12357 = y.dual12357 / y.real;
    const auto v457 = y.dual457 / y.real;
    const auto v1457 = y.dual1457 / y.real;
    const auto v2457 = y.dual2457 / y.real;
    const auto v12457 = y.dual12457 / y.real;
    const auto v3457 = y.dual3457 / y.real;
    const auto v13457 = y.dual13457 / y.real;
    const auto v23457 = y.dual23457 / y.real;
    const auto v123457 = y.dual123457 / y.real;
    const auto v67 = y.dual67 / y.real;
    const auto v167 = y.dual167 / y.real;
    const auto v267 = y.dual267 / y.real;
    const auto v1267 = y.dual1267 / y.real;
    const auto v367 = y.dual367 / y.real;
    const auto v1367 = y.dual1367 / y.real;
    const auto v2367 = y.dual2367 / y.real;
    const auto v12367 = y.dual12367 / y.real;
    const auto v467 = y.dual467 / y.real;
    const auto v1467 = y.dual1467 / y.real;
    const auto v2467 = y.dual2467 / y.real;
    const auto v12467 = y.dual12467 / y.real;
    const auto v3467 = y.dual3467 / y.real;
    const auto v13467 = y.dual13467 / y.real;
    const auto v23467 = y.dual23467 / y.real;
    const auto v123467 = y.dual123467 / y.real;
    const auto v567 = y.dual567 / y.real;
    const auto v1567 = y.dual1567 / y.real;
    const auto v2567 = y.dual2567 / y.real;
    const auto v12567 = y.dual12567 / y.real;
    const auto v3567 = y.dual3567 / y.real;
    const auto v13567 = y.dual13567 / y.real;
    const auto v23567 = y.dual23567 / y.real;
    const auto v123567 = y.dual123567 / y.real;
    const auto v4567 = y.dual4567 / y.real;
    const auto v14567 = y.dual14567 / y.real;
    const auto v24567 = y.dual24567 / y.real;
    const auto v124567 = y.dual124567 / y.real;
    const auto v34567 = y.dual34567 / y.real;
    const auto v134567 = y.dual134567 / y.real;
    const auto v234567 = y.dual234567 / y.real;
    const auto v1234567 = y.dual1234567 / y.real;
    return {
            .real = u,
            .dual1 = u1 - u * v1,
            .dual2 = u2 - u * v2,
            .dual12 = u12 - u2 * v1 - u1 * v2 + 2 * u * v1 * v2 - u * v12,
            .dual3 = u3 - u * v3,
            .dual13 = u13 - u3 * v1 - u1 * v3 + 2 * u * v1 * v3 - u * v13,
            .dual23 = u23 - u3 * v2 - u2 * v3 + 2 * u * v2 * v3 - u * v23,
            .dual123 = u123 - u23 * v1 - u13 * v2 + 2 * u3 * v1 * v2 -
                       u3 * v12 - u12 * v3 + 2 * u2 * v1 * v3 +
                       2 * u1 * v2 * v3 - 6 * u * v1 * v2 * v3 +
                       2 * u * v12 * v3 - u2 * v13 + 2 * u * v2 * v13 -
                       u1 * v23 + 2 * u * v1 * v23 - u * v123,
            .dual4 = u4 - u * v4,
            .dual14 = u14 - u4 * v1 - u1 * v4 + 2 * u * v1 * v4 - u * v14,
            .dual24 = u24 - u4 * v2 - u2 * v4 + 2 * u * v2 * v4 - u * v24,
            .dual124 = u124 - u24 * v1 - u14 * v2 + 2 * u4 * v1 * v2 -
                       u4 * v12 - u12 * v4 + 2 * u2 * v1 * v4 +
                       2 * u1 * v2 * v4 - 6 * u * v1 * v2 * v4 +
                       2 * u * v12 * v4 - u2 * v14 + 2 * u * v2 * v14 -
                       u1 * v24 + 2 * u * v1 * v24 - u * v124,
            .dual34 = u34 - u4 * v3 - u3 * v4 + 2 * u * v3 * v4 - u * v34,
            .dual134 = u134 - u34 * v1 - u14 * v3 + 2 * u4 * v1 * v3 -
                       u4 * v13 - u13 * v4 + 2 * u3 * v1 * v4 +
                       2 * u1 * v3 * v4 - 6 * u * v1 * v3 * v4 +
                       2 * u * v13 * v4 - u3 * v14 + 2 * u * v3 * v14 -
                       u1 * v34 + 2 * u * v1 * v34 - u * v134,
            .dual234 = u234 - u34 * v2 - u24 * v3 + 2 * u4 * v2 * v3 -
                       u4 * v23 - u23 * v4 + 2 * u3 * v2 * v4 +
                       2 * u2 * v3 * v4 - 6 * u * v2 * v3 * v4 +
                       2 * u * v23 * v4 - u3 * v24 + 2 * u * v3 * v24 -
                       u2 * v34 + 2 * u * v2 * v34 - u * v234,
            .dual1234 = u1234 - u234 * v1 - u134 * v2 + 2 * u34 * v1 * v2 -
                        u34 * v12 - u124 * v3 + 2 * u24 * v1 * v3 +
                        2 * u14 * v2 * v3 - 6 * u4 * v1 * v2 * v3 +
                        2 * u4 * v12 * v3 - u24 * v13 + 2 * u4 * v2 * v13 -
                        u14 * v23 + 2 * u4 * v1 * v23 - u4 * v123 - u123 * v4 +
                        2 * u23 * v1 * v4 + 2 * u13 * v2 * v4 -
                        6 * u3 * v1 * v2 * v4 + 2 * u3 * v12 * v4 +
                        2 * u12 * v3 * v4 - 6 * u2 * v1 * v3 * v4 -
                        6 * u1 * v2 * v3 * v4 + 24 * u * v1 * v2 * v3 * v4 -
                        6 * u * v12 * v3 * v4 + 2 * u2 * v13 * v4 -
                        6 * u * v2 * v13 * v4 + 2 * u1 * v23 * v4 -
                        6 * u * v1 * v23 * v4 + 2 * u * v123 * v4 - u23 * v14 +
                        2 * u3 * v2 * v14 + 2 * u2 * v3 * v14 -
                        6 * u * v2 * v3 * v14 + 2 * u * v23 * v14 - u13 * v24 +
                        2 * u3 * v1 * v24 + 2 * u1 * v3 * v24 -
                        6 * u * v1 * v3 * v24 + 2 * u * v13 * v24 - u3 * v124 +
                        2 * u * v3 * v124 - u12 * v34 + 2 * u2 * v1 * v34 +
                        2 * u1 * v2 * v34 - 6 * u * v1 * v2 * v34 +
                        2 * u * v12 * v34 - u2 * v134 + 2 * u * v2 * v134 -
                        u1 * v234 + 2 * u * v1 * v234 - u * v1234,
            .dual5 = u5 - u * v5,
            .dual15 = u15 - u5 * v1 - u1 * v5 + 2 * u * v1 * v5 - u * v15,
            .dual25 = u25 - u5 * v2 - u2 * v5 + 2 * u * v2 * v5 - u * v25,
            .dual125 = u125 - u25 * v1 - u15 * v2 + 2 * u5 * v1 * v2 -
                       u5 * v12 - u12 * v5 + 2 * u2 * v1 * v5 +
                       2 * u1 * v2 * v5 - 6 * u * v1 * v2 * v5 +
                       2 * u * v12 * v5 - u2 * v15 + 2 * u * v2 * v15 -
                       u1 * v25 + 2 * u * v1 * v25 - u * v125,
            .dual35 = u35 - u5 * v3 - u3 * v5 + 2 * u * v3 * v5 - u * v35,
            .dual135 = u135 - u35 * v1 - u15 * v3 + 2 * u5 * v1 * v3 -
                       u5 * v13 - u13 * v5 + 2 * u3 * v1 * v5 +
                       2 * u1 * v3 * v5 - 6 * u * v1 * v3 * v5 +
                       2 * u * v13 * v5 - u3 * v15 + 2 * u * v3 * v15 -
                       u1 * v35 + 2 * u * v1 * v35 - u * v135,
            .dual235 = u235 - u35 * v2 - u25 * v3 + 2 * u5 * v2 * v3 -
                       u5 * v23 - u23 * v5 + 2 * u3 * v2 * v5 +
                       2 * u2 * v3 * v5 - 6 * u * v2 * v3 * v5 +
                       2 * u * v23 * v5 - u3 * v25 + 2 * u * v3 * v25 -
                       u2 * v35 + 2 * u * v2 * v35 - u * v235,
            .dual1235 = u1235 - u235 * v1 - u135 * v2 + 2 * u35 * v1 * v2 -
                        u35 * v12 - u125 * v3 + 2 * u25 * v1 * v3 +
                        2 * u15 * v2 * v3 - 6 * u5 * v1 * v2 * v3 +
                        2 * u5 * v12 * v3 - u25 * v13 + 2 * u5 * v2 * v13 -
                        u15 * v23 + 2 * u5 * v1 * v23 - u5 * v123 - u123 * v5 +
                        2 * u23 * v1 * v5 + 2 * u13 * v2 * v5 -
                        6 * u3 * v1 * v2 * v5 + 2 * u3 * v12 * v5 +
                        2 * u12 * v3 * v5 - 6 * u2 * v1 * v3 * v5 -
                        6 * u1 * v2 * v3 * v5 + 24 * u * v1 * v2 * v3 * v5 -
                        6 * u * v12 * v3 * v5 + 2 * u2 * v13 * v5 -
                        6 * u * v2 * v13 * v5 + 2 * u1 * v23 * v5 -
                        6 * u * v1 * v23 * v5 + 2 * u * v123 * v5 - u23 * v15 +
                        2 * u3 * v2 * v15 + 2 * u2 * v3 * v15 -
                        6 * u * v2 * v3 * v15 + 2 * u * v23 * v15 - u13 * v25 +
                        2 * u3 * v1 * v25 + 2 * u1 * v3 * v25 -
                        6 * u * v1 * v3 * v25 + 2 * u * v13 * v25 - u3 * v125 +
                        2 * u * v3 * v125 - u12 * v35 + 2 * u2 * v1 * v35 +
                        2 * u1 * v2 * v35 - 6 * u * v1 * v2 * v35 +
                        2 * u * v12 * v35 - u2 * v135 + 2 * u * v2 * v135 -
                        u1 * v235 + 2 * u * v1 * v235 - u * v1235,
            .dual45 = u45 - u5 * v4 - u4 * v5 + 2 * u * v4 * v5 - u * v45,
            .dual145 = u145 - u45 * v1 - u15 * v4 + 2 * u5 * v1 * v4 -
                       u5 * v14 - u14 * v5 + 2 * u4 * v1 * v5 +
                       2 * u1 * v4 * v5 - 6 * u * v1 * v4 * v5 +
                       2 * u * v14 * v5 - u4 * v15 + 2 * u * v4 * v15 -
                       u1 * v45 + 2 * u * v1 * v45 - u * v145,
            .dual245 = u245 - u45 * v2 - u25 * v4 + 2 * u5 * v2 * v4 -
                       u5 * v24 - u24 * v5 + 2 * u4 * v2 * v5 +
                       2 * u2 * v4 * v5 - 6 * u * v2 * v4 * v5 +
                       2 * u * v24 * v5 - u4 * v25 + 2 * u * v4 * v25 -
                       u2 * v45 + 2 * u * v2 * v45 - u * v245,
            .dual1245 = u1245 - u245 * v1 - u145 * v2 + 2 * u45 * v1 * v2 -
                        u45 * v12 - u125 * v4 + 2 * u25 * v1 * v4 +
                        2 * u15 * v2 * v4 - 6 * u5 * v1 * v2 * v4 +
                        2 * u5 * v12 * v4 - u25 * v14 + 2 * u5 * v2 * v14 -
                        u15 * v24 + 2 * u5 * v1 * v24 - u5 * v124 - u124 * v5 +
                        2 * u24 * v1 * v5 + 2 * u14 * v2 * v5 -
                        6 * u4 * v1 * v2 * v5 + 2 * u4 * v12 * v5 +
                        2 * u12 * v4 * v5 - 6 * u2 * v1 * v4 * v5 -
                        6 * u1 * v2 * v4 * v5 + 24 * u * v1 * v2 * v4 * v5 -
                        6 * u * v12 * v4 * v5 + 2 * u2 * v14 * v5 -
                        6 * u * v2 * v14 * v5 + 2 * u1 * v24 * v5 -
                        6 * u * v1 * v24 * v5 + 2 * u * v124 * v5 - u24 * v15 +
                        2 * u4 * v2 * v15 + 2 * u2 * v4 * v15 -
                        6 * u * v2 * v4 * v15 + 2 * u * v24 * v15 - u14 * v25 +
                        2 * u4 * v1 * v25 + 2 * u1 * v4 * v25 -
                        6 * u * v1 * v4 * v25 + 2 * u * v14 * v25 - u4 * v125 +
                        2 * u * v4 * v125 - u12 * v45 + 2 * u2 * v1 * v45 +
                        2 * u1 * v2 * v45 - 6 * u * v1 * v2 * v45 +
                        2 * u * v12 * v45 - u2 * v145 + 2 * u * v2 * v145 -
                        u1 * v245 + 2 * u * v1 * v245 - u * v1245,
            .dual345 = u345 - u45 * v3 - u35 * v4 + 2 * u5 * v3 * v4 -
                       u5 * v34 - u34 * v5 + 2 * u4 * v3 * v5 +
                       2 * u3 * v4 * v5 - 6 * u * v3 * v4 * v5 +
                       2 * u * v34 * v5 - u4 * v35 + 2 * u * v4 * v35 -
                       u3 * v45 + 2 * u * v3 * v45 - u * v345,
            .dual1345 = u1345 - u345 * v1 - u145 * v3 + 2 * u45 * v1 * v3 -
                        u45 * v13 - u135 * v4 + 2 * u35 * v1 * v4 +
                        2 * u15 * v3 * v4 - 6 * u5 * v1 * v3 * v4 +
                        2 * u5 * v13 * v4 - u35 * v14 + 2 * u5 * v3 * v14 -
                        u15 * v34 + 2 * u5 * v1 * v34 - u5 * v134 - u134 * v5 +
                        2 * u34 * v1 * v5 + 2 * u14 * v3 * v5 -
                        6 * u4 * v1 * v3 * v5 + 2 * u4 * v13 * v5 +
                        2 * u13 * v4 * v5 - 6 * u3 * v1 * v4 * v5 -
                        6 * u1 * v3 * v4 * v5 + 24 * u * v1 * v3 * v4 * v5 -
                        6 * u * v13 * v4 * v5 + 2 * u3 * v14 * v5 -
                        6 * u * v3 * v14 * v5 + 2 * u1 * v34 * v5 -
                        6 * u * v1 * v34 * v5 + 2 * u * v134 * v5 - u34 * v15 +
                        2 * u4 * v3 * v15 + 2 * u3 * v4 * v15 -
                        6 * u * v3 * v4 * v15 + 2 * u * v34 * v15 - u14 * v35 +
                        2 * u4 * v1 * v35 + 2 * u1 * v4 * v35 -
                        6 * u * v1 * v4 * v35 + 2 * u * v14 * v35 - u4 * v135 +
                        2 * u * v4 * v135 - u13 * v45 + 2 * u3 * v1 * v45 +
                        2 * u1 * v3 * v45 - 6 * u * v1 * v3 * v45 +
                        2 * u * v13 * v45 - u3 * v145 + 2 * u * v3 * v145 -
                        u1 * v345 + 2 * u * v1 * v345 - u * v1345,
            .dual2345 = u2345 - u345 * v2 - u245 * v3 + 2 * u45 * v2 * v3 -
                        u45 * v23 - u235 * v4 + 2 * u35 * v2 * v4 +
                        2 * u25 * v3 * v4 - 6 * u5 * v2 * v3 * v4 +
                        2 * u5 * v23 * v4 - u35 * v24 + 2 * u5 * v3 * v24 -
                        u25 * v34 + 2 * u5 * v2 * v34 - u5 * v234 - u234 * v5 +
                        2 * u34 * v2 * v5 + 2 * u24 * v3 * v5 -
                        6 * u4 * v2 * v3 * v5 + 2 * u4 * v23 * v5 +
                        2 * u23 * v4 * v5 - 6 * u3 * v2 * v4 * v5 -
                        6 * u2 * v3 * v4 * v5 + 24 * u * v2 * v3 * v4 * v5 -
                        6 * u * v23 * v4 * v5 + 2 * u3 * v24 * v5 -
                        6 * u * v3 * v24 * v5 + 2 * u2 * v34 * v5 -
                        6 * u * v2 * v34 * v5 + 2 * u * v234 * v5 - u34 * v25 +
                        2 * u4 * v3 * v25 + 2 * u3 * v4 * v25 -
                        6 * u * v3 * v4 * v25 + 2 * u * v34 * v25 - u24 * v35 +
                        2 * u4 * v2 * v35 + 2 * u2 * v4 * v35 -
                        6 * u * v2 * v4 * v35 + 2 * u * v24 * v35 - u4 * v235 +
                        2 * u * v4 * v235 - u23 * v45 + 2 * u3 * v2 * v45 +
                        2 * u2 * v3 * v45 - 6 * u * v2 * v3 * v45 +
                        2 * u * v23 * v45 - u3 * v245 + 2 * u * v3 * v245 -
                        u2 * v345 + 2 * u * v2 * v345 - u * v2345,
            .dual12345 =
                    u12345 - u2345 * v1 - u1345 * v2 + 2 * u345 * v1 * v2 -
                    u345 * v12 - u1245 * v3 + 2 * u245 * v1 * v3 +
                    2 * u145 * v2 * v3 - 6 * u45 * v1 * v2 * v3 +
                    2 * u45 * v12 * v3 - u245 * v13 + 2 * u45 * v2 * v13 -
                    u145 * v23 + 2 * u45 * v1 * v23 - u45 * v123 - u1235 * v4 +
                    2 * u235 * v1 * v4 + 2 * u135 * v2 * v4 -
                    6 * u35 * v1 * v2 * v4 + 2 * u35 * v12 * v4 +
                    2 * u125 * v3 * v4 - 6 * u25 * v1 * v3 * v4 -
                    6 * u15 * v2 * v3 * v4 + 24 * u5 * v1 * v2 * v3 * v4 -
                    6 * u5 * v12 * v3 * v4 + 2 * u25 * v13 * v4 -
                    6 * u5 * v2 * v13 * v4 + 2 * u15 * v23 * v4 -
                    6 * u5 * v1 * v23 * v4 + 2 * u5 * v123 * v4 - u235 * v14 +
                    2 * u35 * v2 * v14 + 2 * u25 * v3 * v14 -
                    6 * u5 * v2 * v3 * v14 + 2 * u5 * v23 * v14 - u135 * v24 +
                    2 * u35 * v1 * v24 + 2 * u15 * v3 * v24 -
                    6 * u5 * v1 * v3 * v24 + 2 * u5 * v13 * v24 - u35 * v124 +
                    2 * u5 * v3 * v124 - u125 * v34 + 2 * u25 * v1 * v34 +
                    2 * u15 * v2 * v34 - 6 * u5 * v1 * v2 * v34 +
                    2 * u5 * v12 * v34 - u25 * v134 + 2 * u5 * v2 * v134 -
                    u15 * v234 + 2 * u5 * v1 * v234 - u5 * v1234 - u1234 * v5 +
                    2 * u234 * v1 * v5 + 2 * u134 * v2 * v5 -
                    6 * u34 * v1 * v2 * v5 + 2 * u34 * v12 * v5 +
                    2 * u124 * v3 * v5 - 6 * u24 * v1 * v3 * v5 -
                    6 * u14 * v2 * v3 * v5 + 24 * u4 * v1 * v2 * v3 * v5 -
                    6 * u4 * v12 * v3 * v5 + 2 * u24 * v13 * v5 -
                    6 * u4 * v2 * v13 * v5 + 2 * u14 * v23 * v5 -
                    6 * u4 * v1 * v23 * v5 + 2 * u4 * v123 * v5 +
                    2 * u123 * v4 * v5 - 6 * u23 * v1 * v4 * v5 -
                    6 * u13 * v2 * v4 * v5 + 24 * u3 * v1 * v2 * v4 * v5 -
                    6 * u3 * v12 * v4 * v5 - 6 * u12 * v3 * v4 * v5 +
                    24 * u2 * v1 * v3 * v4 * v5 + 24 * u1 * v2 * v3 * v4 * v5 -
                    120 * u * v1 * v2 * v3 * v4 * v5 +
                    24 * u * v12 * v3 * v4 * v5 - 6 * u2 * v13 * v4 * v5 +
                    24 * u * v2 * v13 * v4 * v5 - 6 * u1 * v23 * v4 * v5 +
                    24 * u * v1 * v23 * v4 * v5 - 6 * u * v123 * v4 * v5 +
                    2 * u23 * v14 * v5 - 6 * u3 * v2 * v14 * v5 -
                    6 * u2 * v3 * v14 * v5 + 24 * u * v2 * v3 * v14 * v5 -
                    6 * u * v23 * v14 * v5 + 2 * u13 * v24 * v5 -
                    6 * u3 * v1 * v24 * v5 - 6 * u1 * v3 * v24 * v5 +
                    24 * u * v1 * v3 * v24 * v5 - 6 * u * v13 * v24 * v5 +
                    2 * u3 * v124 * v5 - 6 * u * v3 * v124 * v5 +
                    2 * u12 * v34 * v5 - 6 * u2 * v1 * v34 * v5 -
                    6 * u1 * v2 * v34 * v5 + 24 * u * v1 * v2 * v34 * v5 -
                    6 * u * v12 * v34 * v5 + 2 * u2 * v134 * v5 -
                    6 * u * v2 * v134 * v5 + 2 * u1 * v234 * v5 -
                    6 * u * v1 * v234 * v5 + 2 * u * v1234 * v5 - u234 * v15 +
                    2 * u34 * v2 * v15 + 2 * u24 * v3 * v15 -
                    6 * u4 * v2 * v3 * v15 + 2 * u4 * v23 * v15 +
                    2 * u23 * v4 * v15 - 6 * u3 * v2 * v4 * v15 -
                    6 * u2 * v3 * v4 * v15 + 24 * u * v2 * v3 * v4 * v15 -
                    6 * u * v23 * v4 * v15 + 2 * u3 * v24 * v15 -
                    6 * u * v3 * v24 * v15 + 2 * u2 * v34 * v15 -
                    6 * u * v2 * v34 * v15 + 2 * u * v234 * v15 - u134 * v25 +
                    2 * u34 * v1 * v25 + 2 * u14 * v3 * v25 -
                    6 * u4 * v1 * v3 * v25 + 2 * u4 * v13 * v25 +
                    2 * u13 * v4 * v25 - 6 * u3 * v1 * v4 * v25 -
                    6 * u1 * v3 * v4 * v25 + 24 * u * v1 * v3 * v4 * v25 -
                    6 * u * v13 * v4 * v25 + 2 * u3 * v14 * v25 -
                    6 * u * v3 * v14 * v25 + 2 * u1 * v34 * v25 -
                    6 * u * v1 * v34 * v25 + 2 * u * v134 * v25 - u34 * v125 +
                    2 * u4 * v3 * v125 + 2 * u3 * v4 * v125 -
                    6 * u * v3 * v4 * v125 + 2 * u * v34 * v125 - u124 * v35 +
                    2 * u24 * v1 * v35 + 2 * u14 * v2 * v35 -
                    6 * u4 * v1 * v2 * v35 + 2 * u4 * v12 * v35 +
                    2 * u12 * v4 * v35 - 6 * u2 * v1 * v4 * v35 -
                    6 * u1 * v2 * v4 * v35 + 24 * u * v1 * v2 * v4 * v35 -
                    6 * u * v12 * v4 * v35 + 2 * u2 * v14 * v35 -
                    6 * u * v2 * v14 * v35 + 2 * u1 * v24 * v35 -
                    6 * u * v1 * v24 * v35 + 2 * u * v124 * v35 - u24 * v135 +
                    2 * u4 * v2 * v135 + 2 * u2 * v4 * v135 -
                    6 * u * v2 * v4 * v135 + 2 * u * v24 * v135 - u14 * v235 +
                    2 * u4 * v1 * v235 + 2 * u1 * v4 * v235 -
                    6 * u * v1 * v4 * v235 + 2 * u * v14 * v235 - u4 * v1235 +
                    2 * u * v4 * v1235 - u123 * v45 + 2 * u23 * v1 * v45 +
                    2 * u13 * v2 * v45 - 6 * u3 * v1 * v2 * v45 +
                    2 * u3 * v12 * v45 + 2 * u12 * v3 * v45 -
                    6 * u2 * v1 * v3 * v45 - 6 * u1 * v2 * v3 * v45 +
                    24 * u * v1 * v2 * v3 * v45 - 6 * u * v12 * v3 * v45 +
                    2 * u2 * v13 * v45 - 6 * u * v2 * v13 * v45 +
                    2 * u1 * v23 * v45 - 6 * u * v1 * v23 * v45 +
                    2 * u * v123 * v45 - u23 * v145 + 2 * u3 * v2 * v145 +
                    2 * u2 * v3 * v145 - 6 * u * v2 * v3 * v145 +
                    2 * u * v23 * v145 - u13 * v245 + 2 * u3 * v1 * v245 +
                    2 * u1 * v3 * v245 - 6 * u * v1 * v3 * v245 +
                    2 * u * v13 * v245 - u3 * v1245 + 2 * u * v3 * v1245 -
                    u12 * v345 + 2 * u2 * v1 * v345 + 2 * u1 * v2 * v345 -
                    6 * u * v1 * v2 * v345 + 2 * u * v12 * v345 - u2 * v1345 +
                    2 * u * v2 * v1345 - u1 * v2345 + 2 * u * v1 * v2345 -
                    u * v12345,
            .dual6 = u6 - u * v6,
            .dual16 = u16 - u6 * v1 - u1 * v6 + 2 * u * v1 * v6 - u * v16,
            .dual26 = u26 - u6 * v2 - u2 * v6 + 2 * u * v2 * v6 - u * v26,
            .dual126 = u126 - u26 * v1 - u16 * v2 + 2 * u6 * v1 * v2 -
                       u6 * v12 - u12 * v6 + 2 * u2 * v1 * v6 +
                       2 * u1 * v2 * v6 - 6 * u * v1 * v2 * v6 +
                       2 * u * v12 * v6 - u2 * v16 + 2 * u * v2 * v16 -
                       u1 * v26 + 2 * u * v1 * v26 - u * v126,
            .dual36 = u36 - u6 * v3 - u3 * v6 + 2 * u * v3 * v6 - u * v36,
            .dual136 = u136 - u36 * v1 - u16 * v3 + 2 * u6 * v1 * v3 -
                       u6 * v13 - u13 * v6 + 2 * u3 * v1 * v6 +
                       2 * u1 * v3 * v6 - 6 * u * v1 * v3 * v6 +
                       2 * u * v13 * v6 - u3 * v16 + 2 * u * v3 * v16 -
                       u1 * v36 + 2 * u * v1 * v36 - u * v136,
            .dual236 = u236 - u36 * v2 - u26 * v3 + 2 * u6 * v2 * v3 -
                       u6 * v23 - u23 * v6 + 2 * u3 * v2 * v6 +
                       2 * u2 * v3 * v6 - 6 * u * v2 * v3 * v6 +
                       2 * u * v23 * v6 - u3 * v26 + 2 * u * v3 * v26 -
                       u2 * v36 + 2 * u * v2 * v36 - u * v236,
            .dual1236 = u1236 - u236 * v1 - u136 * v2 + 2 * u36 * v1 * v2 -
                        u36 * v12 - u126 * v3 + 2 * u26 * v1 * v3 +
                        2 * u16 * v2 * v3 - 6 * u6 * v1 * v2 * v3 +
                        2 * u6 * v12 * v3 - u26 * v13 + 2 * u6 * v2 * v13 -
                        u16 * v23 + 2 * u6 * v1 * v23 - u6 * v123 - u123 * v6 +
                        2 * u23 * v1 * v6 + 2 * u13 * v2 * v6 -
                        6 * u3 * v1 * v2 * v6 + 2 * u3 * v12 * v6 +
                        2 * u12 * v3 * v6 - 6 * u2 * v1 * v3 * v6 -
                        6 * u1 * v2 * v3 * v6 + 24 * u * v1 * v2 * v3 * v6 -
                        6 * u * v12 * v3 * v6 + 2 * u2 * v13 * v6 -
                        6 * u * v2 * v13 * v6 + 2 * u1 * v23 * v6 -
                        6 * u * v1 * v23 * v6 + 2 * u * v123 * v6 - u23 * v16 +
                        2 * u3 * v2 * v16 + 2 * u2 * v3 * v16 -
                        6 * u * v2 * v3 * v16 + 2 * u * v23 * v16 - u13 * v26 +
                        2 * u3 * v1 * v26 + 2 * u1 * v3 * v26 -
                        6 * u * v1 * v3 * v26 + 2 * u * v13 * v26 - u3 * v126 +
                        2 * u * v3 * v126 - u12 * v36 + 2 * u2 * v1 * v36 +
                        2 * u1 * v2 * v36 - 6 * u * v1 * v2 * v36 +
                        2 * u * v12 * v36 - u2 * v136 + 2 * u * v2 * v136 -
                        u1 * v236 + 2 * u * v1 * v236 - u * v1236,
            .dual46 = u46 - u6 * v4 - u4 * v6 + 2 * u * v4 * v6 - u * v46,
            .dual146 = u146 - u46 * v1 - u16 * v4 + 2 * u6 * v1 * v4 -
                       u6 * v14 - u14 * v6 + 2 * u4 * v1 * v6 +
                       2 * u1 * v4 * v6 - 6 * u * v1 * v4 * v6 +
                       2 * u * v14 * v6 - u4 * v16 + 2 * u * v4 * v16 -
                       u1 * v46 + 2 * u * v1 * v46 - u * v146,
            .dual246 = u246 - u46 * v2 - u26 * v4 + 2 * u6 * v2 * v4 -
                       u6 * v24 - u24 * v6 + 2 * u4 * v2 * v6 +
                       2 * u2 * v4 * v6 - 6 * u * v2 * v4 * v6 +
                       2 * u * v24 * v6 - u4 * v26 + 2 * u * v4 * v26 -
                       u2 * v46 + 2 * u * v2 * v46 - u * v246,
            .dual1246 = u1246 - u246 * v1 - u146 * v2 + 2 * u46 * v1 * v2 -
                        u46 * v12 - u126 * v4 + 2 * u26 * v1 * v4 +
                        2 * u16 * v2 * v4 - 6 * u6 * v1 * v2 * v4 +
                        2 * u6 * v12 * v4 - u26 * v14 + 2 * u6 * v2 * v14 -
                        u16 * v24 + 2 * u6 * v1 * v24 - u6 * v124 - u124 * v6 +
                        2 * u24 * v1 * v6 + 2 * u14 * v2 * v6 -
                        6 * u4 * v1 * v2 * v6 + 2 * u4 * v12 * v6 +
                        2 * u12 * v4 * v6 - 6 * u2 * v1 * v4 * v6 -
                        6 * u1 * v2 * v4 * v6 + 24 * u * v1 * v2 * v4 * v6 -
                        6 * u * v12 * v4 * v6 + 2 * u2 * v14 * v6 -
                        6 * u * v2 * v14 * v6 + 2 * u1 * v24 * v6 -
                        6 * u * v1 * v24 * v6 + 2 * u * v124 * v6 - u24 * v16 +
                        2 * u4 * v2 * v16 + 2 * u2 * v4 * v16 -
                        6 * u * v2 * v4 * v16 + 2 * u * v24 * v16 - u14 * v26 +
                        2 * u4 * v1 * v26 + 2 * u1 * v4 * v26 -
                        6 * u * v1 * v4 * v26 + 2 * u * v14 * v26 - u4 * v126 +
                        2 * u * v4 * v126 - u12 * v46 + 2 * u2 * v1 * v46 +
                        2 * u1 * v2 * v46 - 6 * u * v1 * v2 * v46 +
                        2 * u * v12 * v46 - u2 * v146 + 2 * u * v2 * v146 -
                        u1 * v246 + 2 * u * v1 * v246 - u * v1246,
            .dual346 = u346 - u46 * v3 - u36 * v4 + 2 * u6 * v3 * v4 -
                       u6 * v34 - u34 * v6 + 2 * u4 * v3 * v6 +
                       2 * u3 * v4 * v6 - 6 * u * v3 * v4 * v6 +
                       2 * u * v34 * v6 - u4 * v36 + 2 * u * v4 * v36 -
                       u3 * v46 + 2 * u * v3 * v46 - u * v346,
            .dual1346 = u1346 - u346 * v1 - u146 * v3 + 2 * u46 * v1 * v3 -
                        u46 * v13 - u136 * v4 + 2 * u36 * v1 * v4 +
                        2 * u16 * v3 * v4 - 6 * u6 * v1 * v3 * v4 +
                        2 * u6 * v13 * v4 - u36 * v14 + 2 * u6 * v3 * v14 -
                        u16 * v34 + 2 * u6 * v1 * v34 - u6 * v134 - u134 * v6 +
                        2 * u34 * v1 * v6 + 2 * u14 * v3 * v6 -
                        6 * u4 * v1 * v3 * v6 + 2 * u4 * v13 * v6 +
                        2 * u13 * v4 * v6 - 6 * u3 * v1 * v4 * v6 -
                        6 * u1 * v3 * v4 * v6 + 24 * u * v1 * v3 * v4 * v6 -
                        6 * u * v13 * v4 * v6 + 2 * u3 * v14 * v6 -
                        6 * u * v3 * v14 * v6 + 2 * u1 * v34 * v6 -
                        6 * u * v1 * v34 * v6 + 2 * u * v134 * v6 - u34 * v16 +
                        2 * u4 * v3 * v16 + 2 * u3 * v4 * v16 -
                        6 * u * v3 * v4 * v16 + 2 * u * v34 * v16 - u14 * v36 +
                        2 * u4 * v1 * v36 + 2 * u1 * v4 * v36 -
                        6 * u * v1 * v4 * v36 + 2 * u * v14 * v36 - u4 * v136 +
                        2 * u * v4 * v136 - u13 * v46 + 2 * u3 * v1 * v46 +
                        2 * u1 * v3 * v46 - 6 * u * v1 * v3 * v46 +
                        2 * u * v13 * v46 - u3 * v146 + 2 * u * v3 * v146 -
                        u1 * v346 + 2 * u * v1 * v346 - u * v1346,
            .dual2346 = u2346 - u346 * v2 - u246 * v3 + 2 * u46 * v2 * v3 -
                        u46 * v23 - u236 * v4 + 2 * u36 * v2 * v4 +
                        2 * u26 * v3 * v4 - 6 * u6 * v2 * v3 * v4 +
                        2 * u6 * v23 * v4 - u36 * v24 + 2 * u6 * v3 * v24 -
                        u26 * v34 + 2 * u6 * v2 * v34 - u6 * v234 - u234 * v6 +
                        2 * u34 * v2 * v6 + 2 * u24 * v3 * v6 -
                        6 * u4 * v2 * v3 * v6 + 2 * u4 * v23 * v6 +
                        2 * u23 * v4 * v6 - 6 * u3 * v2 * v4 * v6 -
                        6 * u2 * v3 * v4 * v6 + 24 * u * v2 * v3 * v4 * v6 -
                        6 * u * v23 * v4 * v6 + 2 * u3 * v24 * v6 -
                        6 * u * v3 * v24 * v6 + 2 * u2 * v34 * v6 -
                        6 * u * v2 * v34 * v6 + 2 * u * v234 * v6 - u34 * v26 +
                        2 * u4 * v3 * v26 + 2 * u3 * v4 * v26 -
                        6 * u * v3 * v4 * v26 + 2 * u * v34 * v26 - u24 * v36 +
                        2 * u4 * v2 * v36 + 2 * u2 * v4 * v36 -
                        6 * u * v2 * v4 * v36 + 2 * u * v24 * v36 - u4 * v236 +
                        2 * u * v4 * v236 - u23 * v46 + 2 * u3 * v2 * v46 +
                        2 * u2 * v3 * v46 - 6 * u * v2 * v3 * v46 +
                        2 * u * v23 * v46 - u3 * v246 + 2 * u * v3 * v246 -
                        u2 * v346 + 2 * u * v2 * v346 - u * v2346,
            .dual12346 =
                    u12346 - u2346 * v1 - u1346 * v2 + 2 * u346 * v1 * v2 -
                    u346 * v12 - u1246 * v3 + 2 * u246 * v1 * v3 +
                    2 * u146 * v2 * v3 - 6 * u46 * v1 * v2 * v3 +
                    2 * u46 * v12 * v3 - u246 * v13 + 2 * u46 * v2 * v13 -
                    u146 * v23 + 2 * u46 * v1 * v23 - u46 * v123 - u1236 * v4 +
                    2 * u236 * v1 * v4 + 2 * u136 * v2 * v4 -
                    6 * u36 * v1 * v2 * v4 + 2 * u36 * v12 * v4 +
                    2 * u126 * v3 * v4 - 6 * u26 * v1 * v3 * v4 -
                    6 * u16 * v2 * v3 * v4 + 24 * u6 * v1 * v2 * v3 * v4 -
                    6 * u6 * v12 * v3 * v4 + 2 * u26 * v13 * v4 -
                    6 * u6 * v2 * v13 * v4 + 2 * u16 * v23 * v4 -
                    6 * u6 * v1 * v23 * v4 + 2 * u6 * v123 * v4 - u236 * v14 +
                    2 * u36 * v2 * v14 + 2 * u26 * v3 * v14 -
                    6 * u6 * v2 * v3 * v14 + 2 * u6 * v23 * v14 - u136 * v24 +
                    2 * u36 * v1 * v24 + 2 * u16 * v3 * v24 -
                    6 * u6 * v1 * v3 * v24 + 2 * u6 * v13 * v24 - u36 * v124 +
                    2 * u6 * v3 * v124 - u126 * v34 + 2 * u26 * v1 * v34 +
                    2 * u16 * v2 * v34 - 6 * u6 * v1 * v2 * v34 +
                    2 * u6 * v12 * v34 - u26 * v134 + 2 * u6 * v2 * v134 -
                    u16 * v234 + 2 * u6 * v1 * v234 - u6 * v1234 - u1234 * v6 +
                    2 * u234 * v1 * v6 + 2 * u134 * v2 * v6 -
                    6 * u34 * v1 * v2 * v6 + 2 * u34 * v12 * v6 +
                    2 * u124 * v3 * v6 - 6 * u24 * v1 * v3 * v6 -
                    6 * u14 * v2 * v3 * v6 + 24 * u4 * v1 * v2 * v3 * v6 -
                    6 * u4 * v12 * v3 * v6 + 2 * u24 * v13 * v6 -
                    6 * u4 * v2 * v13 * v6 + 2 * u14 * v23 * v6 -
                    6 * u4 * v1 * v23 * v6 + 2 * u4 * v123 * v6 +
                    2 * u123 * v4 * v6 - 6 * u23 * v1 * v4 * v6 -
                    6 * u13 * v2 * v4 * v6 + 24 * u3 * v1 * v2 * v4 * v6 -
                    6 * u3 * v12 * v4 * v6 - 6 * u12 * v3 * v4 * v6 +
                    24 * u2 * v1 * v3 * v4 * v6 + 24 * u1 * v2 * v3 * v4 * v6 -
                    120 * u * v1 * v2 * v3 * v4 * v6 +
                    24 * u * v12 * v3 * v4 * v6 - 6 * u2 * v13 * v4 * v6 +
                    24 * u * v2 * v13 * v4 * v6 - 6 * u1 * v23 * v4 * v6 +
                    24 * u * v1 * v23 * v4 * v6 - 6 * u * v123 * v4 * v6 +
                    2 * u23 * v14 * v6 - 6 * u3 * v2 * v14 * v6 -
                    6 * u2 * v3 * v14 * v6 + 24 * u * v2 * v3 * v14 * v6 -
                    6 * u * v23 * v14 * v6 + 2 * u13 * v24 * v6 -
                    6 * u3 * v1 * v24 * v6 - 6 * u1 * v3 * v24 * v6 +
                    24 * u * v1 * v3 * v24 * v6 - 6 * u * v13 * v24 * v6 +
                    2 * u3 * v124 * v6 - 6 * u * v3 * v124 * v6 +
                    2 * u12 * v34 * v6 - 6 * u2 * v1 * v34 * v6 -
                    6 * u1 * v2 * v34 * v6 + 24 * u * v1 * v2 * v34 * v6 -
                    6 * u * v12 * v34 * v6 + 2 * u2 * v134 * v6 -
                    6 * u * v2 * v134 * v6 + 2 * u1 * v234 * v6 -
                    6 * u * v1 * v234 * v6 + 2 * u * v1234 * v6 - u234 * v16 +
                    2 * u34 * v2 * v16 + 2 * u24 * v3 * v16 -
                    6 * u4 * v2 * v3 * v16 + 2 * u4 * v23 * v16 +
                    2 * u23 * v4 * v16 - 6 * u3 * v2 * v4 * v16 -
                    6 * u2 * v3 * v4 * v16 + 24 * u * v2 * v3 * v4 * v16 -
                    6 * u * v23 * v4 * v16 + 2 * u3 * v24 * v16 -
                    6 * u * v3 * v24 * v16 + 2 * u2 * v34 * v16 -
                    6 * u * v2 * v34 * v16 + 2 * u * v234 * v16 - u134 * v26 +
                    2 * u34 * v1 * v26 + 2 * u14 * v3 * v26 -
                    6 * u4 * v1 * v3 * v26 + 2 * u4 * v13 * v26 +
                    2 * u13 * v4 * v26 - 6 * u3 * v1 * v4 * v26 -
                    6 * u1 * v3 * v4 * v26 + 24 * u * v1 * v3 * v4 * v26 -
                    6 * u * v13 * v4 * v26 + 2 * u3 * v14 * v26 -
                    6 * u * v3 * v14 * v26 + 2 * u1 * v34 * v26 -
                    6 * u * v1 * v34 * v26 + 2 * u * v134 * v26 - u34 * v126 +
                    2 * u4 * v3 * v126 + 2 * u3 * v4 * v126 -
                    6 * u * v3 * v4 * v126 + 2 * u * v34 * v126 - u124 * v36 +
                    2 * u24 * v1 * v36 + 2 * u14 * v2 * v36 -
                    6 * u4 * v1 * v2 * v36 + 2 * u4 * v12 * v36 +
                    2 * u12 * v4 * v36 - 6 * u2 * v1 * v4 * v36 -
                    6 * u1 * v2 * v4 * v36 + 24 * u * v1 * v2 * v4 * v36 -
                    6 * u * v12 * v4 * v36 + 2 * u2 * v14 * v36 -
                    6 * u * v2 * v14 * v36 + 2 * u1 * v24 * v36 -
                    6 * u * v1 * v24 * v36 + 2 * u * v124 * v36 - u24 * v136 +
                    2 * u4 * v2 * v136 + 2 * u2 * v4 * v136 -
                    6 * u * v2 * v4 * v136 + 2 * u * v24 * v136 - u14 * v236 +
                    2 * u4 * v1 * v236 + 2 * u1 * v4 * v236 -
                    6 * u * v1 * v4 * v236 + 2 * u * v14 * v236 - u4 * v1236 +
                    2 * u * v4 * v1236 - u123 * v46 + 2 * u23 * v1 * v46 +
                    2 * u13 * v2 * v46 - 6 * u3 * v1 * v2 * v46 +
                    2 * u3 * v12 * v46 + 2 * u12 * v3 * v46 -
                    6 * u2 * v1 * v3 * v46 - 6 * u1 * v2 * v3 * v46 +
                    24 * u * v1 * v2 * v3 * v46 - 6 * u * v12 * v3 * v46 +
                    2 * u2 * v13 * v46 - 6 * u * v2 * v13 * v46 +
                    2 * u1 * v23 * v46 - 6 * u * v1 * v23 * v46 +
                    2 * u * v123 * v46 - u23 * v146 + 2 * u3 * v2 * v146 +
                    2 * u2 * v3 * v146 - 6 * u * v2 * v3 * v146 +
                    2 * u * v23 * v146 - u13 * v246 + 2 * u3 * v1 * v246 +
                    2 * u1 * v3 * v246 - 6 * u * v1 * v3 * v246 +
                    2 * u * v13 * v246 - u3 * v1246 + 2 * u * v3 * v1246 -
                    u12 * v346 + 2 * u2 * v1 * v346 + 2 * u1 * v2 * v346 -
                    6 * u * v1 * v2 * v346 + 2 * u * v12 * v346 - u2 * v1346 +
                    2 * u * v2 * v1346 - u1 * v2346 + 2 * u * v1 * v2346 -
                    u * v12346,
            .dual56 = u56 - u6 * v5 - u5 * v6 + 2 * u * v5 * v6 - u * v56,
            .dual156 = u156 - u56 * v1 - u16 * v5 + 2 * u6 * v1 * v5 -
                       u6 * v15 - u15 * v6 + 2 * u5 * v1 * v6 +
                       2 * u1 * v5 * v6 - 6 * u * v1 * v5 * v6 +
                       2 * u * v15 * v6 - u5 * v16 + 2 * u * v5 * v16 -
                       u1 * v56 + 2 * u * v1 * v56 - u * v156,
            .dual256 = u256 - u56 * v2 - u26 * v5 + 2 * u6 * v2 * v5 -
                       u6 * v25 - u25 * v6 + 2 * u5 * v2 * v6 +
                       2 * u2 * v5 * v6 - 6 * u * v2 * v5 * v6 +
                       2 * u * v25 * v6 - u5 * v26 + 2 * u * v5 * v26 -
                       u2 * v56 + 2 * u * v2 * v56 - u * v256,
            .dual1256 = u1256 - u256 * v1 - u156 * v2 + 2 * u56 * v1 * v2 -
                        u56 * v12 - u126 * v5 + 2 * u26 * v1 * v5 +
                        2 * u16 * v2 * v5 - 6 * u6 * v1 * v2 * v5 +
                        2 * u6 * v12 * v5 - u26 * v15 + 2 * u6 * v2 * v15 -
                        u16 * v25 + 2 * u6 * v1 * v25 - u6 * v125 - u125 * v6 +
                        2 * u25 * v1 * v6 + 2 * u15 * v2 * v6 -
                        6 * u5 * v1 * v2 * v6 + 2 * u5 * v12 * v6 +
                        2 * u12 * v5 * v6 - 6 * u2 * v1 * v5 * v6 -
                        6 * u1 * v2 * v5 * v6 + 24 * u * v1 * v2 * v5 * v6 -
                        6 * u * v12 * v5 * v6 + 2 * u2 * v15 * v6 -
                        6 * u * v2 * v15 * v6 + 2 * u1 * v25 * v6 -
                        6 * u * v1 * v25 * v6 + 2 * u * v125 * v6 - u25 * v16 +
                        2 * u5 * v2 * v16 + 2 * u2 * v5 * v16 -
                        6 * u * v2 * v5 * v16 + 2 * u * v25 * v16 - u15 * v26 +
                        2 * u5 * v1 * v26 + 2 * u1 * v5 * v26 -
                        6 * u * v1 * v5 * v26 + 2 * u * v15 * v26 - u5 * v126 +
                        2 * u * v5 * v126 - u12 * v56 + 2 * u2 * v1 * v56 +
                        2 * u1 * v2 * v56 - 6 * u * v1 * v2 * v56 +
                        2 * u * v12 * v56 - u2 * v156 + 2 * u * v2 * v156 -
                        u1 * v256 + 2 * u * v1 * v256 - u * v1256,
            .dual356 = u356 - u56 * v3 - u36 * v5 + 2 * u6 * v3 * v5 -
                       u6 * v35 - u35 * v6 + 2 * u5 * v3 * v6 +
                       2 * u3 * v5 * v6 - 6 * u * v3 * v5 * v6 +
                       2 * u * v35 * v6 - u5 * v36 + 2 * u * v5 * v36 -
                       u3 * v56 + 2 * u * v3 * v56 - u * v356,
            .dual1356 = u1356 - u356 * v1 - u156 * v3 + 2 * u56 * v1 * v3 -
                        u56 * v13 - u136 * v5 + 2 * u36 * v1 * v5 +
                        2 * u16 * v3 * v5 - 6 * u6 * v1 * v3 * v5 +
                        2 * u6 * v13 * v5 - u36 * v15 + 2 * u6 * v3 * v15 -
                        u16 * v35 + 2 * u6 * v1 * v35 - u6 * v135 - u135 * v6 +
                        2 * u35 * v1 * v6 + 2 * u15 * v3 * v6 -
                        6 * u5 * v1 * v3 * v6 + 2 * u5 * v13 * v6 +
                        2 * u13 * v5 * v6 - 6 * u3 * v1 * v5 * v6 -
                        6 * u1 * v3 * v5 * v6 + 24 * u * v1 * v3 * v5 * v6 -
                        6 * u * v13 * v5 * v6 + 2 * u3 * v15 * v6 -
                        6 * u * v3 * v15 * v6 + 2 * u1 * v35 * v6 -
                        6 * u * v1 * v35 * v6 + 2 * u * v135 * v6 - u35 * v16 +
                        2 * u5 * v3 * v16 + 2 * u3 * v5 * v16 -
                        6 * u * v3 * v5 * v16 + 2 * u * v35 * v16 - u15 * v36 +
                        2 * u5 * v1 * v36 + 2 * u1 * v5 * v36 -
                        6 * u * v1 * v5 * v36 + 2 * u * v15 * v36 - u5 * v136 +
                        2 * u * v5 * v136 - u13 * v56 + 2 * u3 * v1 * v56 +
                        2 * u1 * v3 * v56 - 6 * u * v1 * v3 * v56 +
                        2 * u * v13 * v56 - u3 * v156 + 2 * u * v3 * v156 -
                        u1 * v356 + 2 * u * v1 * v356 - u * v1356,
            .dual2356 = u2356 - u356 * v2 - u256 * v3 + 2 * u56 * v2 * v3 -
                        u56 * v23 - u236 * v5 + 2 * u36 * v2 * v5 +
                        2 * u26 * v3 * v5 - 6 * u6 * v2 * v3 * v5 +
                        2 * u6 * v23 * v5 - u36 * v25 + 2 * u6 * v3 * v25 -
                        u26 * v35 + 2 * u6 * v2 * v35 - u6 * v235 - u235 * v6 +
                        2 * u35 * v2 * v6 + 2 * u25 * v3 * v6 -
                        6 * u5 * v2 * v3 * v6 + 2 * u5 * v23 * v6 +
                        2 * u23 * v5 * v6 - 6 * u3 * v2 * v5 * v6 -
                        6 * u2 * v3 * v5 * v6 + 24 * u * v2 * v3 * v5 * v6 -
                        6 * u * v23 * v5 * v6 + 2 * u3 * v25 * v6 -
                        6 * u * v3 * v25 * v6 + 2 * u2 * v35 * v6 -
                        6 * u * v2 * v35 * v6 + 2 * u * v235 * v6 - u35 * v26 +
                        2 * u5 * v3 * v26 + 2 * u3 * v5 * v26 -
                        6 * u * v3 * v5 * v26 + 2 * u * v35 * v26 - u25 * v36 +
                        2 * u5 * v2 * v36 + 2 * u2 * v5 * v36 -
                        6 * u * v2 * v5 * v36 + 2 * u * v25 * v36 - u5 * v236 +
                        2 * u * v5 * v236 - u23 * v56 + 2 * u3 * v2 * v56 +
                        2 * u2 * v3 * v56 - 6 * u * v2 * v3 * v56 +
                        2 * u * v23 * v56 - u3 * v256 + 2 * u * v3 * v256 -
                        u2 * v356 + 2 * u * v2 * v356 - u * v2356,
            .dual12356 =
                    u12356 - u2356 * v1 - u1356 * v2 + 2 * u356 * v1 * v2 -
                    u356 * v12 - u1256 * v3 + 2 * u256 * v1 * v3 +
                    2 * u156 * v2 * v3 - 6 * u56 * v1 * v2 * v3 +
                    2 * u56 * v12 * v3 - u256 * v13 + 2 * u56 * v2 * v13 -
                    u156 * v23 + 2 * u56 * v1 * v23 - u56 * v123 - u1236 * v5 +
                    2 * u236 * v1 * v5 + 2 * u136 * v2 * v5 -
                    6 * u36 * v1 * v2 * v5 + 2 * u36 * v12 * v5 +
                    2 * u126 * v3 * v5 - 6 * u26 * v1 * v3 * v5 -
                    6 * u16 * v2 * v3 * v5 + 24 * u6 * v1 * v2 * v3 * v5 -
                    6 * u6 * v12 * v3 * v5 + 2 * u26 * v13 * v5 -
                    6 * u6 * v2 * v13 * v5 + 2 * u16 * v23 * v5 -
                    6 * u6 * v1 * v23 * v5 + 2 * u6 * v123 * v5 - u236 * v15 +
                    2 * u36 * v2 * v15 + 2 * u26 * v3 * v15 -
                    6 * u6 * v2 * v3 * v15 + 2 * u6 * v23 * v15 - u136 * v25 +
                    2 * u36 * v1 * v25 + 2 * u16 * v3 * v25 -
                    6 * u6 * v1 * v3 * v25 + 2 * u6 * v13 * v25 - u36 * v125 +
                    2 * u6 * v3 * v125 - u126 * v35 + 2 * u26 * v1 * v35 +
                    2 * u16 * v2 * v35 - 6 * u6 * v1 * v2 * v35 +
                    2 * u6 * v12 * v35 - u26 * v135 + 2 * u6 * v2 * v135 -
                    u16 * v235 + 2 * u6 * v1 * v235 - u6 * v1235 - u1235 * v6 +
                    2 * u235 * v1 * v6 + 2 * u135 * v2 * v6 -
                    6 * u35 * v1 * v2 * v6 + 2 * u35 * v12 * v6 +
                    2 * u125 * v3 * v6 - 6 * u25 * v1 * v3 * v6 -
                    6 * u15 * v2 * v3 * v6 + 24 * u5 * v1 * v2 * v3 * v6 -
                    6 * u5 * v12 * v3 * v6 + 2 * u25 * v13 * v6 -
                    6 * u5 * v2 * v13 * v6 + 2 * u15 * v23 * v6 -
                    6 * u5 * v1 * v23 * v6 + 2 * u5 * v123 * v6 +
                    2 * u123 * v5 * v6 - 6 * u23 * v1 * v5 * v6 -
                    6 * u13 * v2 * v5 * v6 + 24 * u3 * v1 * v2 * v5 * v6 -
                    6 * u3 * v12 * v5 * v6 - 6 * u12 * v3 * v5 * v6 +
                    24 * u2 * v1 * v3 * v5 * v6 + 24 * u1 * v2 * v3 * v5 * v6 -
                    120 * u * v1 * v2 * v3 * v5 * v6 +
                    24 * u * v12 * v3 * v5 * v6 - 6 * u2 * v13 * v5 * v6 +
                    24 * u * v2 * v13 * v5 * v6 - 6 * u1 * v23 * v5 * v6 +
                    24 * u * v1 * v23 * v5 * v6 - 6 * u * v123 * v5 * v6 +
                    2 * u23 * v15 * v6 - 6 * u3 * v2 * v15 * v6 -
                    6 * u2 * v3 * v15 * v6 + 24 * u * v2 * v3 * v15 * v6 -
                    6 * u * v23 * v15 * v6 + 2 * u13 * v25 * v6 -
                    6 * u3 * v1 * v25 * v6 - 6 * u1 * v3 * v25 * v6 +
                    24 * u * v1 * v3 * v25 * v6 - 6 * u * v13 * v25 * v6 +
                    2 * u3 * v125 * v6 - 6 * u * v3 * v125 * v6 +
                    2 * u12 * v35 * v6 - 6 * u2 * v1 * v35 * v6 -
                    6 * u1 * v2 * v35 * v6 + 24 * u * v1 * v2 * v35 * v6 -
                    6 * u * v12 * v35 * v6 + 2 * u2 * v135 * v6 -
                    6 * u * v2 * v135 * v6 + 2 * u1 * v235 * v6 -
                    6 * u * v1 * v235 * v6 + 2 * u * v1235 * v6 - u235 * v16 +
                    2 * u35 * v2 * v16 + 2 * u25 * v3 * v16 -
                    6 * u5 * v2 * v3 * v16 + 2 * u5 * v23 * v16 +
                    2 * u23 * v5 * v16 - 6 * u3 * v2 * v5 * v16 -
                    6 * u2 * v3 * v5 * v16 + 24 * u * v2 * v3 * v5 * v16 -
                    6 * u * v23 * v5 * v16 + 2 * u3 * v25 * v16 -
                    6 * u * v3 * v25 * v16 + 2 * u2 * v35 * v16 -
                    6 * u * v2 * v35 * v16 + 2 * u * v235 * v16 - u135 * v26 +
                    2 * u35 * v1 * v26 + 2 * u15 * v3 * v26 -
                    6 * u5 * v1 * v3 * v26 + 2 * u5 * v13 * v26 +
                    2 * u13 * v5 * v26 - 6 * u3 * v1 * v5 * v26 -
                    6 * u1 * v3 * v5 * v26 + 24 * u * v1 * v3 * v5 * v26 -
                    6 * u * v13 * v5 * v26 + 2 * u3 * v15 * v26 -
                    6 * u * v3 * v15 * v26 + 2 * u1 * v35 * v26 -
                    6 * u * v1 * v35 * v26 + 2 * u * v135 * v26 - u35 * v126 +
                    2 * u5 * v3 * v126 + 2 * u3 * v5 * v126 -
                    6 * u * v3 * v5 * v126 + 2 * u * v35 * v126 - u125 * v36 +
                    2 * u25 * v1 * v36 + 2 * u15 * v2 * v36 -
                    6 * u5 * v1 * v2 * v36 + 2 * u5 * v12 * v36 +
                    2 * u12 * v5 * v36 - 6 * u2 * v1 * v5 * v36 -
                    6 * u1 * v2 * v5 * v36 + 24 * u * v1 * v2 * v5 * v36 -
                    6 * u * v12 * v5 * v36 + 2 * u2 * v15 * v36 -
                    6 * u * v2 * v15 * v36 + 2 * u1 * v25 * v36 -
                    6 * u * v1 * v25 * v36 + 2 * u * v125 * v36 - u25 * v136 +
                    2 * u5 * v2 * v136 + 2 * u2 * v5 * v136 -
                    6 * u * v2 * v5 * v136 + 2 * u * v25 * v136 - u15 * v236 +
                    2 * u5 * v1 * v236 + 2 * u1 * v5 * v236 -
                    6 * u * v1 * v5 * v236 + 2 * u * v15 * v236 - u5 * v1236 +
                    2 * u * v5 * v1236 - u123 * v56 + 2 * u23 * v1 * v56 +
                    2 * u13 * v2 * v56 - 6 * u3 * v1 * v2 * v56 +
                    2 * u3 * v12 * v56 + 2 * u12 * v3 * v56 -
                    6 * u2 * v1 * v3 * v56 - 6 * u1 * v2 * v3 * v56 +
                    24 * u * v1 * v2 * v3 * v56 - 6 * u * v12 * v3 * v56 +
                    2 * u2 * v13 * v56 - 6 * u * v2 * v13 * v56 +
                    2 * u1 * v23 * v56 - 6 * u * v1 * v23 * v56 +
                    2 * u * v123 * v56 - u23 * v156 + 2 * u3 * v2 * v156 +
                    2 * u2 * v3 * v156 - 6 * u * v2 * v3 * v156 +
                    2 * u * v23 * v156 - u13 * v256 + 2 * u3 * v1 * v256 +
                    2 * u1 * v3 * v256 - 6 * u * v1 * v3 * v256 +
                    2 * u * v13 * v256 - u3 * v1256 + 2 * u * v3 * v1256 -
                    u12 * v356 + 2 * u2 * v1 * v356 + 2 * u1 * v2 * v356 -
                    6 * u * v1 * v2 * v356 + 2 * u * v12 * v356 - u2 * v1356 +
                    2 * u * v2 * v1356 - u1 * v2356 + 2 * u * v1 * v2356 -
                    u * v12356,
            .dual456 = u456 - u56 * v4 - u46 * v5 + 2 * u6 * v4 * v5 -
                       u6 * v45 - u45 * v6 + 2 * u5 * v4 * v6 +
                       2 * u4 * v5 * v6 - 6 * u * v4 * v5 * v6 +
                       2 * u * v45 * v6 - u5 * v46 + 2 * u * v5 * v46 -
                       u4 * v56 + 2 * u * v4 * v56 - u * v456,
            .dual1456 = u1456 - u456 * v1 - u156 * v4 + 2 * u56 * v1 * v4 -
                        u56 * v14 - u146 * v5 + 2 * u46 * v1 * v5 +
                        2 * u16 * v4 * v5 - 6 * u6 * v1 * v4 * v5 +
                        2 * u6 * v14 * v5 - u46 * v15 + 2 * u6 * v4 * v15 -
                        u16 * v45 + 2 * u6 * v1 * v45 - u6 * v145 - u145 * v6 +
                        2 * u45 * v1 * v6 + 2 * u15 * v4 * v6 -
                        6 * u5 * v1 * v4 * v6 + 2 * u5 * v14 * v6 +
                        2 * u14 * v5 * v6 - 6 * u4 * v1 * v5 * v6 -
                        6 * u1 * v4 * v5 * v6 + 24 * u * v1 * v4 * v5 * v6 -
                        6 * u * v14 * v5 * v6 + 2 * u4 * v15 * v6 -
                        6 * u * v4 * v15 * v6 + 2 * u1 * v45 * v6 -
                        6 * u * v1 * v45 * v6 + 2 * u * v145 * v6 - u45 * v16 +
                        2 * u5 * v4 * v16 + 2 * u4 * v5 * v16 -
                        6 * u * v4 * v5 * v16 + 2 * u * v45 * v16 - u15 * v46 +
                        2 * u5 * v1 * v46 + 2 * u1 * v5 * v46 -
                        6 * u * v1 * v5 * v46 + 2 * u * v15 * v46 - u5 * v146 +
                        2 * u * v5 * v146 - u14 * v56 + 2 * u4 * v1 * v56 +
                        2 * u1 * v4 * v56 - 6 * u * v1 * v4 * v56 +
                        2 * u * v14 * v56 - u4 * v156 + 2 * u * v4 * v156 -
                        u1 * v456 + 2 * u * v1 * v456 - u * v1456,
            .dual2456 = u2456 - u456 * v2 - u256 * v4 + 2 * u56 * v2 * v4 -
                        u56 * v24 - u246 * v5 + 2 * u46 * v2 * v5 +
                        2 * u26 * v4 * v5 - 6 * u6 * v2 * v4 * v5 +
                        2 * u6 * v24 * v5 - u46 * v25 + 2 * u6 * v4 * v25 -
                        u26 * v45 + 2 * u6 * v2 * v45 - u6 * v245 - u245 * v6 +
                        2 * u45 * v2 * v6 + 2 * u25 * v4 * v6 -
                        6 * u5 * v2 * v4 * v6 + 2 * u5 * v24 * v6 +
                        2 * u24 * v5 * v6 - 6 * u4 * v2 * v5 * v6 -
                        6 * u2 * v4 * v5 * v6 + 24 * u * v2 * v4 * v5 * v6 -
                        6 * u * v24 * v5 * v6 + 2 * u4 * v25 * v6 -
                        6 * u * v4 * v25 * v6 + 2 * u2 * v45 * v6 -
                        6 * u * v2 * v45 * v6 + 2 * u * v245 * v6 - u45 * v26 +
                        2 * u5 * v4 * v26 + 2 * u4 * v5 * v26 -
                        6 * u * v4 * v5 * v26 + 2 * u * v45 * v26 - u25 * v46 +
                        2 * u5 * v2 * v46 + 2 * u2 * v5 * v46 -
                        6 * u * v2 * v5 * v46 + 2 * u * v25 * v46 - u5 * v246 +
                        2 * u * v5 * v246 - u24 * v56 + 2 * u4 * v2 * v56 +
                        2 * u2 * v4 * v56 - 6 * u * v2 * v4 * v56 +
                        2 * u * v24 * v56 - u4 * v256 + 2 * u * v4 * v256 -
                        u2 * v456 + 2 * u * v2 * v456 - u * v2456,
            .dual12456 =
                    u12456 - u2456 * v1 - u1456 * v2 + 2 * u456 * v1 * v2 -
                    u456 * v12 - u1256 * v4 + 2 * u256 * v1 * v4 +
                    2 * u156 * v2 * v4 - 6 * u56 * v1 * v2 * v4 +
                    2 * u56 * v12 * v4 - u256 * v14 + 2 * u56 * v2 * v14 -
                    u156 * v24 + 2 * u56 * v1 * v24 - u56 * v124 - u1246 * v5 +
                    2 * u246 * v1 * v5 + 2 * u146 * v2 * v5 -
                    6 * u46 * v1 * v2 * v5 + 2 * u46 * v12 * v5 +
                    2 * u126 * v4 * v5 - 6 * u26 * v1 * v4 * v5 -
                    6 * u16 * v2 * v4 * v5 + 24 * u6 * v1 * v2 * v4 * v5 -
                    6 * u6 * v12 * v4 * v5 + 2 * u26 * v14 * v5 -
                    6 * u6 * v2 * v14 * v5 + 2 * u16 * v24 * v5 -
                    6 * u6 * v1 * v24 * v5 + 2 * u6 * v124 * v5 - u246 * v15 +
                    2 * u46 * v2 * v15 + 2 * u26 * v4 * v15 -
                    6 * u6 * v2 * v4 * v15 + 2 * u6 * v24 * v15 - u146 * v25 +
                    2 * u46 * v1 * v25 + 2 * u16 * v4 * v25 -
                    6 * u6 * v1 * v4 * v25 + 2 * u6 * v14 * v25 - u46 * v125 +
                    2 * u6 * v4 * v125 - u126 * v45 + 2 * u26 * v1 * v45 +
                    2 * u16 * v2 * v45 - 6 * u6 * v1 * v2 * v45 +
                    2 * u6 * v12 * v45 - u26 * v145 + 2 * u6 * v2 * v145 -
                    u16 * v245 + 2 * u6 * v1 * v245 - u6 * v1245 - u1245 * v6 +
                    2 * u245 * v1 * v6 + 2 * u145 * v2 * v6 -
                    6 * u45 * v1 * v2 * v6 + 2 * u45 * v12 * v6 +
                    2 * u125 * v4 * v6 - 6 * u25 * v1 * v4 * v6 -
                    6 * u15 * v2 * v4 * v6 + 24 * u5 * v1 * v2 * v4 * v6 -
                    6 * u5 * v12 * v4 * v6 + 2 * u25 * v14 * v6 -
                    6 * u5 * v2 * v14 * v6 + 2 * u15 * v24 * v6 -
                    6 * u5 * v1 * v24 * v6 + 2 * u5 * v124 * v6 +
                    2 * u124 * v5 * v6 - 6 * u24 * v1 * v5 * v6 -
                    6 * u14 * v2 * v5 * v6 + 24 * u4 * v1 * v2 * v5 * v6 -
                    6 * u4 * v12 * v5 * v6 - 6 * u12 * v4 * v5 * v6 +
                    24 * u2 * v1 * v4 * v5 * v6 + 24 * u1 * v2 * v4 * v5 * v6 -
                    120 * u * v1 * v2 * v4 * v5 * v6 +
                    24 * u * v12 * v4 * v5 * v6 - 6 * u2 * v14 * v5 * v6 +
                    24 * u * v2 * v14 * v5 * v6 - 6 * u1 * v24 * v5 * v6 +
                    24 * u * v1 * v24 * v5 * v6 - 6 * u * v124 * v5 * v6 +
                    2 * u24 * v15 * v6 - 6 * u4 * v2 * v15 * v6 -
                    6 * u2 * v4 * v15 * v6 + 24 * u * v2 * v4 * v15 * v6 -
                    6 * u * v24 * v15 * v6 + 2 * u14 * v25 * v6 -
                    6 * u4 * v1 * v25 * v6 - 6 * u1 * v4 * v25 * v6 +
                    24 * u * v1 * v4 * v25 * v6 - 6 * u * v14 * v25 * v6 +
                    2 * u4 * v125 * v6 - 6 * u * v4 * v125 * v6 +
                    2 * u12 * v45 * v6 - 6 * u2 * v1 * v45 * v6 -
                    6 * u1 * v2 * v45 * v6 + 24 * u * v1 * v2 * v45 * v6 -
                    6 * u * v12 * v45 * v6 + 2 * u2 * v145 * v6 -
                    6 * u * v2 * v145 * v6 + 2 * u1 * v245 * v6 -
                    6 * u * v1 * v245 * v6 + 2 * u * v1245 * v6 - u245 * v16 +
                    2 * u45 * v2 * v16 + 2 * u25 * v4 * v16 -
                    6 * u5 * v2 * v4 * v16 + 2 * u5 * v24 * v16 +
                    2 * u24 * v5 * v16 - 6 * u4 * v2 * v5 * v16 -
                    6 * u2 * v4 * v5 * v16 + 24 * u * v2 * v4 * v5 * v16 -
                    6 * u * v24 * v5 * v16 + 2 * u4 * v25 * v16 -
                    6 * u * v4 * v25 * v16 + 2 * u2 * v45 * v16 -
                    6 * u * v2 * v45 * v16 + 2 * u * v245 * v16 - u145 * v26 +
                    2 * u45 * v1 * v26 + 2 * u15 * v4 * v26 -
                    6 * u5 * v1 * v4 * v26 + 2 * u5 * v14 * v26 +
                    2 * u14 * v5 * v26 - 6 * u4 * v1 * v5 * v26 -
                    6 * u1 * v4 * v5 * v26 + 24 * u * v1 * v4 * v5 * v26 -
                    6 * u * v14 * v5 * v26 + 2 * u4 * v15 * v26 -
                    6 * u * v4 * v15 * v26 + 2 * u1 * v45 * v26 -
                    6 * u * v1 * v45 * v26 + 2 * u * v145 * v26 - u45 * v126 +
                    2 * u5 * v4 * v126 + 2 * u4 * v5 * v126 -
                    6 * u * v4 * v5 * v126 + 2 * u * v45 * v126 - u125 * v46 +
                    2 * u25 * v1 * v46 + 2 * u15 * v2 * v46 -
                    6 * u5 * v1 * v2 * v46 + 2 * u5 * v12 * v46 +
                    2 * u12 * v5 * v46 - 6 * u2 * v1 * v5 * v46 -
                    6 * u1 * v2 * v5 * v46 + 24 * u * v1 * v2 * v5 * v46 -
                    6 * u * v12 * v5 * v46 + 2 * u2 * v15 * v46 -
                    6 * u * v2 * v15 * v46 + 2 * u1 * v25 * v46 -
                    6 * u * v1 * v25 * v46 + 2 * u * v125 * v46 - u25 * v146 +
                    2 * u5 * v2 * v146 + 2 * u2 * v5 * v146 -
                    6 * u * v2 * v5 * v146 + 2 * u * v25 * v146 - u15 * v246 +
                    2 * u5 * v1 * v246 + 2 * u1 * v5 * v246 -
                    6 * u * v1 * v5 * v246 + 2 * u * v15 * v246 - u5 * v1246 +
                    2 * u * v5 * v1246 - u124 * v56 + 2 * u24 * v1 * v56 +
                    2 * u14 * v2 * v56 - 6 * u4 * v1 * v2 * v56 +
                    2 * u4 * v12 * v56 + 2 * u12 * v4 * v56 -
                    6 * u2 * v1 * v4 * v56 - 6 * u1 * v2 * v4 * v56 +
                    24 * u * v1 * v2 * v4 * v56 - 6 * u * v12 * v4 * v56 +
                    2 * u2 * v14 * v56 - 6 * u * v2 * v14 * v56 +
                    2 * u1 * v24 * v56 - 6 * u * v1 * v24 * v56 +
                    2 * u * v124 * v56 - u24 * v156 + 2 * u4 * v2 * v156 +
                    2 * u2 * v4 * v156 - 6 * u * v2 * v4 * v156 +
                    2 * u * v24 * v156 - u14 * v256 + 2 * u4 * v1 * v256 +
                    2 * u1 * v4 * v256 - 6 * u * v1 * v4 * v256 +
                    2 * u * v14 * v256 - u4 * v1256 + 2 * u * v4 * v1256 -
                    u12 * v456 + 2 * u2 * v1 * v456 + 2 * u1 * v2 * v456 -
                    6 * u * v1 * v2 * v456 + 2 * u * v12 * v456 - u2 * v1456 +
                    2 * u * v2 * v1456 - u1 * v2456 + 2 * u * v1 * v2456 -
                    u * v12456,
            .dual3456 = u3456 - u456 * v3 - u356 * v4 + 2 * u56 * v3 * v4 -
                        u56 * v34 - u346 * v5 + 2 * u46 * v3 * v5 +
                        2 * u36 * v4 * v5 - 6 * u6 * v3 * v4 * v5 +
                        2 * u6 * v34 * v5 - u46 * v35 + 2 * u6 * v4 * v35 -
                        u36 * v45 + 2 * u6 * v3 * v45 - u6 * v345 - u345 * v6 +
                        2 * u45 * v3 * v6 + 2 * u35 * v4 * v6 -
                        6 * u5 * v3 * v4 * v6 + 2 * u5 * v34 * v6 +
                        2 * u34 * v5 * v6 - 6 * u4 * v3 * v5 * v6 -
                        6 * u3 * v4 * v5 * v6 + 24 * u * v3 * v4 * v5 * v6 -
                        6 * u * v34 * v5 * v6 + 2 * u4 * v35 * v6 -
                        6 * u * v4 * v35 * v6 + 2 * u3 * v45 * v6 -
                        6 * u * v3 * v45 * v6 + 2 * u * v345 * v6 - u45 * v36 +
                        2 * u5 * v4 * v36 + 2 * u4 * v5 * v36 -
                        6 * u * v4 * v5 * v36 + 2 * u * v45 * v36 - u35 * v46 +
                        2 * u5 * v3 * v46 + 2 * u3 * v5 * v46 -
                        6 * u * v3 * v5 * v46 + 2 * u * v35 * v46 - u5 * v346 +
                        2 * u * v5 * v346 - u34 * v56 + 2 * u4 * v3 * v56 +
                        2 * u3 * v4 * v56 - 6 * u * v3 * v4 * v56 +
                        2 * u * v34 * v56 - u4 * v356 + 2 * u * v4 * v356 -
                        u3 * v456 + 2 * u * v3 * v456 - u * v3456,
            .dual13456 =
                    u13456 - u3456 * v1 - u1456 * v3 + 2 * u456 * v1 * v3 -
                    u456 * v13 - u1356 * v4 + 2 * u356 * v1 * v4 +
                    2 * u156 * v3 * v4 - 6 * u56 * v1 * v3 * v4 +
                    2 * u56 * v13 * v4 - u356 * v14 + 2 * u56 * v3 * v14 -
                    u156 * v34 + 2 * u56 * v1 * v34 - u56 * v134 - u1346 * v5 +
                    2 * u346 * v1 * v5 + 2 * u146 * v3 * v5 -
                    6 * u46 * v1 * v3 * v5 + 2 * u46 * v13 * v5 +
                    2 * u136 * v4 * v5 - 6 * u36 * v1 * v4 * v5 -
                    6 * u16 * v3 * v4 * v5 + 24 * u6 * v1 * v3 * v4 * v5 -
                    6 * u6 * v13 * v4 * v5 + 2 * u36 * v14 * v5 -
                    6 * u6 * v3 * v14 * v5 + 2 * u16 * v34 * v5 -
                    6 * u6 * v1 * v34 * v5 + 2 * u6 * v134 * v5 - u346 * v15 +
                    2 * u46 * v3 * v15 + 2 * u36 * v4 * v15 -
                    6 * u6 * v3 * v4 * v15 + 2 * u6 * v34 * v15 - u146 * v35 +
                    2 * u46 * v1 * v35 + 2 * u16 * v4 * v35 -
                    6 * u6 * v1 * v4 * v35 + 2 * u6 * v14 * v35 - u46 * v135 +
                    2 * u6 * v4 * v135 - u136 * v45 + 2 * u36 * v1 * v45 +
                    2 * u16 * v3 * v45 - 6 * u6 * v1 * v3 * v45 +
                    2 * u6 * v13 * v45 - u36 * v145 + 2 * u6 * v3 * v145 -
                    u16 * v345 + 2 * u6 * v1 * v345 - u6 * v1345 - u1345 * v6 +
                    2 * u345 * v1 * v6 + 2 * u145 * v3 * v6 -
                    6 * u45 * v1 * v3 * v6 + 2 * u45 * v13 * v6 +
                    2 * u135 * v4 * v6 - 6 * u35 * v1 * v4 * v6 -
                    6 * u15 * v3 * v4 * v6 + 24 * u5 * v1 * v3 * v4 * v6 -
                    6 * u5 * v13 * v4 * v6 + 2 * u35 * v14 * v6 -
                    6 * u5 * v3 * v14 * v6 + 2 * u15 * v34 * v6 -
                    6 * u5 * v1 * v34 * v6 + 2 * u5 * v134 * v6 +
                    2 * u134 * v5 * v6 - 6 * u34 * v1 * v5 * v6 -
                    6 * u14 * v3 * v5 * v6 + 24 * u4 * v1 * v3 * v5 * v6 -
                    6 * u4 * v13 * v5 * v6 - 6 * u13 * v4 * v5 * v6 +
                    24 * u3 * v1 * v4 * v5 * v6 + 24 * u1 * v3 * v4 * v5 * v6 -
                    120 * u * v1 * v3 * v4 * v5 * v6 +
                    24 * u * v13 * v4 * v5 * v6 - 6 * u3 * v14 * v5 * v6 +
                    24 * u * v3 * v14 * v5 * v6 - 6 * u1 * v34 * v5 * v6 +
                    24 * u * v1 * v34 * v5 * v6 - 6 * u * v134 * v5 * v6 +
                    2 * u34 * v15 * v6 - 6 * u4 * v3 * v15 * v6 -
                    6 * u3 * v4 * v15 * v6 + 24 * u * v3 * v4 * v15 * v6 -
                    6 * u * v34 * v15 * v6 + 2 * u14 * v35 * v6 -
                    6 * u4 * v1 * v35 * v6 - 6 * u1 * v4 * v35 * v6 +
                    24 * u * v1 * v4 * v35 * v6 - 6 * u * v14 * v35 * v6 +
                    2 * u4 * v135 * v6 - 6 * u * v4 * v135 * v6 +
                    2 * u13 * v45 * v6 - 6 * u3 * v1 * v45 * v6 -
                    6 * u1 * v3 * v45 * v6 + 24 * u * v1 * v3 * v45 * v6 -
                    6 * u * v13 * v45 * v6 + 2 * u3 * v145 * v6 -
                    6 * u * v3 * v145 * v6 + 2 * u1 * v345 * v6 -
                    6 * u * v1 * v345 * v6 + 2 * u * v1345 * v6 - u345 * v16 +
                    2 * u45 * v3 * v16 + 2 * u35 * v4 * v16 -
                    6 * u5 * v3 * v4 * v16 + 2 * u5 * v34 * v16 +
                    2 * u34 * v5 * v16 - 6 * u4 * v3 * v5 * v16 -
                    6 * u3 * v4 * v5 * v16 + 24 * u * v3 * v4 * v5 * v16 -
                    6 * u * v34 * v5 * v16 + 2 * u4 * v35 * v16 -
                    6 * u * v4 * v35 * v16 + 2 * u3 * v45 * v16 -
                    6 * u * v3 * v45 * v16 + 2 * u * v345 * v16 - u145 * v36 +
                    2 * u45 * v1 * v36 + 2 * u15 * v4 * v36 -
                    6 * u5 * v1 * v4 * v36 + 2 * u5 * v14 * v36 +
                    2 * u14 * v5 * v36 - 6 * u4 * v1 * v5 * v36 -
                    6 * u1 * v4 * v5 * v36 + 24 * u * v1 * v4 * v5 * v36 -
                    6 * u * v14 * v5 * v36 + 2 * u4 * v15 * v36 -
                    6 * u * v4 * v15 * v36 + 2 * u1 * v45 * v36 -
                    6 * u * v1 * v45 * v36 + 2 * u * v145 * v36 - u45 * v136 +
                    2 * u5 * v4 * v136 + 2 * u4 * v5 * v136 -
                    6 * u * v4 * v5 * v136 + 2 * u * v45 * v136 - u135 * v46 +
                    2 * u35 * v1 * v46 + 2 * u15 * v3 * v46 -
                    6 * u5 * v1 * v3 * v46 + 2 * u5 * v13 * v46 +
                    2 * u13 * v5 * v46 - 6 * u3 * v1 * v5 * v46 -
                    6 * u1 * v3 * v5 * v46 + 24 * u * v1 * v3 * v5 * v46 -
                    6 * u * v13 * v5 * v46 + 2 * u3 * v15 * v46 -
                    6 * u * v3 * v15 * v46 + 2 * u1 * v35 * v46 -
                    6 * u * v1 * v35 * v46 + 2 * u * v135 * v46 - u35 * v146 +
                    2 * u5 * v3 * v146 + 2 * u3 * v5 * v146 -
                    6 * u * v3 * v5 * v146 + 2 * u * v35 * v146 - u15 * v346 +
                    2 * u5 * v1 * v346 + 2 * u1 * v5 * v346 -
                    6 * u * v1 * v5 * v346 + 2 * u * v15 * v346 - u5 * v1346 +
                    2 * u * v5 * v1346 - u134 * v56 + 2 * u34 * v1 * v56 +
                    2 * u14 * v3 * v56 - 6 * u4 * v1 * v3 * v56 +
                    2 * u4 * v13 * v56 + 2 * u13 * v4 * v56 -
                    6 * u3 * v1 * v4 * v56 - 6 * u1 * v3 * v4 * v56 +
                    24 * u * v1 * v3 * v4 * v56 - 6 * u * v13 * v4 * v56 +
                    2 * u3 * v14 * v56 - 6 * u * v3 * v14 * v56 +
                    2 * u1 * v34 * v56 - 6 * u * v1 * v34 * v56 +
                    2 * u * v134 * v56 - u34 * v156 + 2 * u4 * v3 * v156 +
                    2 * u3 * v4 * v156 - 6 * u * v3 * v4 * v156 +
                    2 * u * v34 * v156 - u14 * v356 + 2 * u4 * v1 * v356 +
                    2 * u1 * v4 * v356 - 6 * u * v1 * v4 * v356 +
                    2 * u * v14 * v356 - u4 * v1356 + 2 * u * v4 * v1356 -
                    u13 * v456 + 2 * u3 * v1 * v456 + 2 * u1 * v3 * v456 -
                    6 * u * v1 * v3 * v456 + 2 * u * v13 * v456 - u3 * v1456 +
                    2 * u * v3 * v1456 - u1 * v3456 + 2 * u * v1 * v3456 -
                    u * v13456,
            .dual23456 =
                    u23456 - u3456 * v2 - u2456 * v3 + 2 * u456 * v2 * v3 -
                    u456 * v23 - u2356 * v4 + 2 * u356 * v2 * v4 +
                    2 * u256 * v3 * v4 - 6 * u56 * v2 * v3 * v4 +
                    2 * u56 * v23 * v4 - u356 * v24 + 2 * u56 * v3 * v24 -
                    u256 * v34 + 2 * u56 * v2 * v34 - u56 * v234 - u2346 * v5 +
                    2 * u346 * v2 * v5 + 2 * u246 * v3 * v5 -
                    6 * u46 * v2 * v3 * v5 + 2 * u46 * v23 * v5 +
                    2 * u236 * v4 * v5 - 6 * u36 * v2 * v4 * v5 -
                    6 * u26 * v3 * v4 * v5 + 24 * u6 * v2 * v3 * v4 * v5 -
                    6 * u6 * v23 * v4 * v5 + 2 * u36 * v24 * v5 -
                    6 * u6 * v3 * v24 * v5 + 2 * u26 * v34 * v5 -
                    6 * u6 * v2 * v34 * v5 + 2 * u6 * v234 * v5 - u346 * v25 +
                    2 * u46 * v3 * v25 + 2 * u36 * v4 * v25 -
                    6 * u6 * v3 * v4 * v25 + 2 * u6 * v34 * v25 - u246 * v35 +
                    2 * u46 * v2 * v35 + 2 * u26 * v4 * v35 -
                    6 * u6 * v2 * v4 * v35 + 2 * u6 * v24 * v35 - u46 * v235 +
                    2 * u6 * v4 * v235 - u236 * v45 + 2 * u36 * v2 * v45 +
                    2 * u26 * v3 * v45 - 6 * u6 * v2 * v3 * v45 +
                    2 * u6 * v23 * v45 - u36 * v245 + 2 * u6 * v3 * v245 -
                    u26 * v345 + 2 * u6 * v2 * v345 - u6 * v2345 - u2345 * v6 +
                    2 * u345 * v2 * v6 + 2 * u245 * v3 * v6 -
                    6 * u45 * v2 * v3 * v6 + 2 * u45 * v23 * v6 +
                    2 * u235 * v4 * v6 - 6 * u35 * v2 * v4 * v6 -
                    6 * u25 * v3 * v4 * v6 + 24 * u5 * v2 * v3 * v4 * v6 -
                    6 * u5 * v23 * v4 * v6 + 2 * u35 * v24 * v6 -
                    6 * u5 * v3 * v24 * v6 + 2 * u25 * v34 * v6 -
                    6 * u5 * v2 * v34 * v6 + 2 * u5 * v234 * v6 +
                    2 * u234 * v5 * v6 - 6 * u34 * v2 * v5 * v6 -
                    6 * u24 * v3 * v5 * v6 + 24 * u4 * v2 * v3 * v5 * v6 -
                    6 * u4 * v23 * v5 * v6 - 6 * u23 * v4 * v5 * v6 +
                    24 * u3 * v2 * v4 * v5 * v6 + 24 * u2 * v3 * v4 * v5 * v6 -
                    120 * u * v2 * v3 * v4 * v5 * v6 +
                    24 * u * v23 * v4 * v5 * v6 - 6 * u3 * v24 * v5 * v6 +
                    24 * u * v3 * v24 * v5 * v6 - 6 * u2 * v34 * v5 * v6 +
                    24 * u * v2 * v34 * v5 * v6 - 6 * u * v234 * v5 * v6 +
                    2 * u34 * v25 * v6 - 6 * u4 * v3 * v25 * v6 -
                    6 * u3 * v4 * v25 * v6 + 24 * u * v3 * v4 * v25 * v6 -
                    6 * u * v34 * v25 * v6 + 2 * u24 * v35 * v6 -
                    6 * u4 * v2 * v35 * v6 - 6 * u2 * v4 * v35 * v6 +
                    24 * u * v2 * v4 * v35 * v6 - 6 * u * v24 * v35 * v6 +
                    2 * u4 * v235 * v6 - 6 * u * v4 * v235 * v6 +
                    2 * u23 * v45 * v6 - 6 * u3 * v2 * v45 * v6 -
                    6 * u2 * v3 * v45 * v6 + 24 * u * v2 * v3 * v45 * v6 -
                    6 * u * v23 * v45 * v6 + 2 * u3 * v245 * v6 -
                    6 * u * v3 * v245 * v6 + 2 * u2 * v345 * v6 -
                    6 * u * v2 * v345 * v6 + 2 * u * v2345 * v6 - u345 * v26 +
                    2 * u45 * v3 * v26 + 2 * u35 * v4 * v26 -
                    6 * u5 * v3 * v4 * v26 + 2 * u5 * v34 * v26 +
                    2 * u34 * v5 * v26 - 6 * u4 * v3 * v5 * v26 -
                    6 * u3 * v4 * v5 * v26 + 24 * u * v3 * v4 * v5 * v26 -
                    6 * u * v34 * v5 * v26 + 2 * u4 * v35 * v26 -
                    6 * u * v4 * v35 * v26 + 2 * u3 * v45 * v26 -
                    6 * u * v3 * v45 * v26 + 2 * u * v345 * v26 - u245 * v36 +
                    2 * u45 * v2 * v36 + 2 * u25 * v4 * v36 -
                    6 * u5 * v2 * v4 * v36 + 2 * u5 * v24 * v36 +
                    2 * u24 * v5 * v36 - 6 * u4 * v2 * v5 * v36 -
                    6 * u2 * v4 * v5 * v36 + 24 * u * v2 * v4 * v5 * v36 -
                    6 * u * v24 * v5 * v36 + 2 * u4 * v25 * v36 -
                    6 * u * v4 * v25 * v36 + 2 * u2 * v45 * v36 -
                    6 * u * v2 * v45 * v36 + 2 * u * v245 * v36 - u45 * v236 +
                    2 * u5 * v4 * v236 + 2 * u4 * v5 * v236 -
                    6 * u * v4 * v5 * v236 + 2 * u * v45 * v236 - u235 * v46 +
                    2 * u35 * v2 * v46 + 2 * u25 * v3 * v46 -
                    6 * u5 * v2 * v3 * v46 + 2 * u5 * v23 * v46 +
                    2 * u23 * v5 * v46 - 6 * u3 * v2 * v5 * v46 -
                    6 * u2 * v3 * v5 * v46 + 24 * u * v2 * v3 * v5 * v46 -
                    6 * u * v23 * v5 * v46 + 2 * u3 * v25 * v46 -
                    6 * u * v3 * v25 * v46 + 2 * u2 * v35 * v46 -
                    6 * u * v2 * v35 * v46 + 2 * u * v235 * v46 - u35 * v246 +
                    2 * u5 * v3 * v246 + 2 * u3 * v5 * v246 -
                    6 * u * v3 * v5 * v246 + 2 * u * v35 * v246 - u25 * v346 +
                    2 * u5 * v2 * v346 + 2 * u2 * v5 * v346 -
                    6 * u * v2 * v5 * v346 + 2 * u * v25 * v346 - u5 * v2346 +
                    2 * u * v5 * v2346 - u234 * v56 + 2 * u34 * v2 * v56 +
                    2 * u24 * v3 * v56 - 6 * u4 * v2 * v3 * v56 +
                    2 * u4 * v23 * v56 + 2 * u23 * v4 * v56 -
                    6 * u3 * v2 * v4 * v56 - 6 * u2 * v3 * v4 * v56 +
                    24 * u * v2 * v3 * v4 * v56 - 6 * u * v23 * v4 * v56 +
                    2 * u3 * v24 * v56 - 6 * u * v3 * v24 * v56 +
                    2 * u2 * v34 * v56 - 6 * u * v2 * v34 * v56 +
                    2 * u * v234 * v56 - u34 * v256 + 2 * u4 * v3 * v256 +
                    2 * u3 * v4 * v256 - 6 * u * v3 * v4 * v256 +
                    2 * u * v34 * v256 - u24 * v356 + 2 * u4 * v2 * v356 +
                    2 * u2 * v4 * v356 - 6 * u * v2 * v4 * v356 +
                    2 * u * v24 * v356 - u4 * v2356 + 2 * u * v4 * v2356 -
                    u23 * v456 + 2 * u3 * v2 * v456 + 2 * u2 * v3 * v456 -
                    6 * u * v2 * v3 * v456 + 2 * u * v23 * v456 - u3 * v2456 +
                    2 * u * v3 * v2456 - u2 * v3456 + 2 * u * v2 * v3456 -
                    u * v23456,
            .dual123456 =
                    u123456 - u23456 * v1 - u13456 * v2 + 2 * u3456 * v1 * v2 -
                    u3456 * v12 - u12456 * v3 + 2 * u2456 * v1 * v3 +
                    2 * u1456 * v2 * v3 - 6 * u456 * v1 * v2 * v3 +
                    2 * u456 * v12 * v3 - u2456 * v13 + 2 * u456 * v2 * v13 -
                    u1456 * v23 + 2 * u456 * v1 * v23 - u456 * v123 -
                    u12356 * v4 + 2 * u2356 * v1 * v4 + 2 * u1356 * v2 * v4 -
                    6 * u356 * v1 * v2 * v4 + 2 * u356 * v12 * v4 +
                    2 * u1256 * v3 * v4 - 6 * u256 * v1 * v3 * v4 -
                    6 * u156 * v2 * v3 * v4 + 24 * u56 * v1 * v2 * v3 * v4 -
                    6 * u56 * v12 * v3 * v4 + 2 * u256 * v13 * v4 -
                    6 * u56 * v2 * v13 * v4 + 2 * u156 * v23 * v4 -
                    6 * u56 * v1 * v23 * v4 + 2 * u56 * v123 * v4 -
                    u2356 * v14 + 2 * u356 * v2 * v14 + 2 * u256 * v3 * v14 -
                    6 * u56 * v2 * v3 * v14 + 2 * u56 * v23 * v14 -
                    u1356 * v24 + 2 * u356 * v1 * v24 + 2 * u156 * v3 * v24 -
                    6 * u56 * v1 * v3 * v24 + 2 * u56 * v13 * v24 -
                    u356 * v124 + 2 * u56 * v3 * v124 - u1256 * v34 +
                    2 * u256 * v1 * v34 + 2 * u156 * v2 * v34 -
                    6 * u56 * v1 * v2 * v34 + 2 * u56 * v12 * v34 -
                    u256 * v134 + 2 * u56 * v2 * v134 - u156 * v234 +
                    2 * u56 * v1 * v234 - u56 * v1234 - u12346 * v5 +
                    2 * u2346 * v1 * v5 + 2 * u1346 * v2 * v5 -
                    6 * u346 * v1 * v2 * v5 + 2 * u346 * v12 * v5 +
                    2 * u1246 * v3 * v5 - 6 * u246 * v1 * v3 * v5 -
                    6 * u146 * v2 * v3 * v5 + 24 * u46 * v1 * v2 * v3 * v5 -
                    6 * u46 * v12 * v3 * v5 + 2 * u246 * v13 * v5 -
                    6 * u46 * v2 * v13 * v5 + 2 * u146 * v23 * v5 -
                    6 * u46 * v1 * v23 * v5 + 2 * u46 * v123 * v5 +
                    2 * u1236 * v4 * v5 - 6 * u236 * v1 * v4 * v5 -
                    6 * u136 * v2 * v4 * v5 + 24 * u36 * v1 * v2 * v4 * v5 -
                    6 * u36 * v12 * v4 * v5 - 6 * u126 * v3 * v4 * v5 +
                    24 * u26 * v1 * v3 * v4 * v5 +
                    24 * u16 * v2 * v3 * v4 * v5 -
                    120 * u6 * v1 * v2 * v3 * v4 * v5 +
                    24 * u6 * v12 * v3 * v4 * v5 - 6 * u26 * v13 * v4 * v5 +
                    24 * u6 * v2 * v13 * v4 * v5 - 6 * u16 * v23 * v4 * v5 +
                    24 * u6 * v1 * v23 * v4 * v5 - 6 * u6 * v123 * v4 * v5 +
                    2 * u236 * v14 * v5 - 6 * u36 * v2 * v14 * v5 -
                    6 * u26 * v3 * v14 * v5 + 24 * u6 * v2 * v3 * v14 * v5 -
                    6 * u6 * v23 * v14 * v5 + 2 * u136 * v24 * v5 -
                    6 * u36 * v1 * v24 * v5 - 6 * u16 * v3 * v24 * v5 +
                    24 * u6 * v1 * v3 * v24 * v5 - 6 * u6 * v13 * v24 * v5 +
                    2 * u36 * v124 * v5 - 6 * u6 * v3 * v124 * v5 +
                    2 * u126 * v34 * v5 - 6 * u26 * v1 * v34 * v5 -
                    6 * u16 * v2 * v34 * v5 + 24 * u6 * v1 * v2 * v34 * v5 -
                    6 * u6 * v12 * v34 * v5 + 2 * u26 * v134 * v5 -
                    6 * u6 * v2 * v134 * v5 + 2 * u16 * v234 * v5 -
                    6 * u6 * v1 * v234 * v5 + 2 * u6 * v1234 * v5 -
                    u2346 * v15 + 2 * u346 * v2 * v15 + 2 * u246 * v3 * v15 -
                    6 * u46 * v2 * v3 * v15 + 2 * u46 * v23 * v15 +
                    2 * u236 * v4 * v15 - 6 * u36 * v2 * v4 * v15 -
                    6 * u26 * v3 * v4 * v15 + 24 * u6 * v2 * v3 * v4 * v15 -
                    6 * u6 * v23 * v4 * v15 + 2 * u36 * v24 * v15 -
                    6 * u6 * v3 * v24 * v15 + 2 * u26 * v34 * v15 -
                    6 * u6 * v2 * v34 * v15 + 2 * u6 * v234 * v15 -
                    u1346 * v25 + 2 * u346 * v1 * v25 + 2 * u146 * v3 * v25 -
                    6 * u46 * v1 * v3 * v25 + 2 * u46 * v13 * v25 +
                    2 * u136 * v4 * v25 - 6 * u36 * v1 * v4 * v25 -
                    6 * u16 * v3 * v4 * v25 + 24 * u6 * v1 * v3 * v4 * v25 -
                    6 * u6 * v13 * v4 * v25 + 2 * u36 * v14 * v25 -
                    6 * u6 * v3 * v14 * v25 + 2 * u16 * v34 * v25 -
                    6 * u6 * v1 * v34 * v25 + 2 * u6 * v134 * v25 -
                    u346 * v125 + 2 * u46 * v3 * v125 + 2 * u36 * v4 * v125 -
                    6 * u6 * v3 * v4 * v125 + 2 * u6 * v34 * v125 -
                    u1246 * v35 + 2 * u246 * v1 * v35 + 2 * u146 * v2 * v35 -
                    6 * u46 * v1 * v2 * v35 + 2 * u46 * v12 * v35 +
                    2 * u126 * v4 * v35 - 6 * u26 * v1 * v4 * v35 -
                    6 * u16 * v2 * v4 * v35 + 24 * u6 * v1 * v2 * v4 * v35 -
                    6 * u6 * v12 * v4 * v35 + 2 * u26 * v14 * v35 -
                    6 * u6 * v2 * v14 * v35 + 2 * u16 * v24 * v35 -
                    6 * u6 * v1 * v24 * v35 + 2 * u6 * v124 * v35 -
                    u246 * v135 + 2 * u46 * v2 * v135 + 2 * u26 * v4 * v135 -
                    6 * u6 * v2 * v4 * v135 + 2 * u6 * v24 * v135 -
                    u146 * v235 + 2 * u46 * v1 * v235 + 2 * u16 * v4 * v235 -
                    6 * u6 * v1 * v4 * v235 + 2 * u6 * v14 * v235 -
                    u46 * v1235 + 2 * u6 * v4 * v1235 - u1236 * v45 +
                    2 * u236 * v1 * v45 + 2 * u136 * v2 * v45 -
                    6 * u36 * v1 * v2 * v45 + 2 * u36 * v12 * v45 +
                    2 * u126 * v3 * v45 - 6 * u26 * v1 * v3 * v45 -
                    6 * u16 * v2 * v3 * v45 + 24 * u6 * v1 * v2 * v3 * v45 -
                    6 * u6 * v12 * v3 * v45 + 2 * u26 * v13 * v45 -
                    6 * u6 * v2 * v13 * v45 + 2 * u16 * v23 * v45 -
                    6 * u6 * v1 * v23 * v45 + 2 * u6 * v123 * v45 -
                    u236 * v145 + 2 * u36 * v2 * v145 + 2 * u26 * v3 * v145 -
                    6 * u6 * v2 * v3 * v145 + 2 * u6 * v23 * v145 -
                    u136 * v245 + 2 * u36 * v1 * v245 + 2 * u16 * v3 * v245 -
                    6 * u6 * v1 * v3 * v245 + 2 * u6 * v13 * v245 -
                    u36 * v1245 + 2 * u6 * v3 * v1245 - u126 * v345 +
                    2 * u26 * v1 * v345 + 2 * u16 * v2 * v345 -
                    6 * u6 * v1 * v2 * v345 + 2 * u6 * v12 * v345 -
                    u26 * v1345 + 2 * u6 * v2 * v1345 - u16 * v2345 +
                    2 * u6 * v1 * v2345 - u6 * v12345 - u12345 * v6 +
                    2 * u2345 * v1 * v6 + 2 * u1345 * v2 * v6 -
                    6 * u345 * v1 * v2 * v6 + 2 * u345 * v12 * v6 +
                    2 * u1245 * v3 * v6 - 6 * u245 * v1 * v3 * v6 -
                    6 * u145 * v2 * v3 * v6 + 24 * u45 * v1 * v2 * v3 * v6 -
                    6 * u45 * v12 * v3 * v6 + 2 * u245 * v13 * v6 -
                    6 * u45 * v2 * v13 * v6 + 2 * u145 * v23 * v6 -
                    6 * u45 * v1 * v23 * v6 + 2 * u45 * v123 * v6 +
                    2 * u1235 * v4 * v6 - 6 * u235 * v1 * v4 * v6 -
                    6 * u135 * v2 * v4 * v6 + 24 * u35 * v1 * v2 * v4 * v6 -
                    6 * u35 * v12 * v4 * v6 - 6 * u125 * v3 * v4 * v6 +
                    24 * u25 * v1 * v3 * v4 * v6 +
                    24 * u15 * v2 * v3 * v4 * v6 -
                    120 * u5 * v1 * v2 * v3 * v4 * v6 +
                    24 * u5 * v12 * v3 * v4 * v6 - 6 * u25 * v13 * v4 * v6 +
                    24 * u5 * v2 * v13 * v4 * v6 - 6 * u15 * v23 * v4 * v6 +
                    24 * u5 * v1 * v23 * v4 * v6 - 6 * u5 * v123 * v4 * v6 +
                    2 * u235 * v14 * v6 - 6 * u35 * v2 * v14 * v6 -
                    6 * u25 * v3 * v14 * v6 + 24 * u5 * v2 * v3 * v14 * v6 -
                    6 * u5 * v23 * v14 * v6 + 2 * u135 * v24 * v6 -
                    6 * u35 * v1 * v24 * v6 - 6 * u15 * v3 * v24 * v6 +
                    24 * u5 * v1 * v3 * v24 * v6 - 6 * u5 * v13 * v24 * v6 +
                    2 * u35 * v124 * v6 - 6 * u5 * v3 * v124 * v6 +
                    2 * u125 * v34 * v6 - 6 * u25 * v1 * v34 * v6 -
                    6 * u15 * v2 * v34 * v6 + 24 * u5 * v1 * v2 * v34 * v6 -
                    6 * u5 * v12 * v34 * v6 + 2 * u25 * v134 * v6 -
                    6 * u5 * v2 * v134 * v6 + 2 * u15 * v234 * v6 -
                    6 * u5 * v1 * v234 * v6 + 2 * u5 * v1234 * v6 +
                    2 * u1234 * v5 * v6 - 6 * u234 * v1 * v5 * v6 -
                    6 * u134 * v2 * v5 * v6 + 24 * u34 * v1 * v2 * v5 * v6 -
                    6 * u34 * v12 * v5 * v6 - 6 * u124 * v3 * v5 * v6 +
                    24 * u24 * v1 * v3 * v5 * v6 +
                    24 * u14 * v2 * v3 * v5 * v6 -
                    120 * u4 * v1 * v2 * v3 * v5 * v6 +
                    24 * u4 * v12 * v3 * v5 * v6 - 6 * u24 * v13 * v5 * v6 +
                    24 * u4 * v2 * v13 * v5 * v6 - 6 * u14 * v23 * v5 * v6 +
                    24 * u4 * v1 * v23 * v5 * v6 - 6 * u4 * v123 * v5 * v6 -
                    6 * u123 * v4 * v5 * v6 + 24 * u23 * v1 * v4 * v5 * v6 +
                    24 * u13 * v2 * v4 * v5 * v6 -
                    120 * u3 * v1 * v2 * v4 * v5 * v6 +
                    24 * u3 * v12 * v4 * v5 * v6 +
                    24 * u12 * v3 * v4 * v5 * v6 -
                    120 * u2 * v1 * v3 * v4 * v5 * v6 -
                    120 * u1 * v2 * v3 * v4 * v5 * v6 +
                    720 * u * v1 * v2 * v3 * v4 * v5 * v6 -
                    120 * u * v12 * v3 * v4 * v5 * v6 +
                    24 * u2 * v13 * v4 * v5 * v6 -
                    120 * u * v2 * v13 * v4 * v5 * v6 +
                    24 * u1 * v23 * v4 * v5 * v6 -
                    120 * u * v1 * v23 * v4 * v5 * v6 +
                    24 * u * v123 * v4 * v5 * v6 - 6 * u23 * v14 * v5 * v6 +
                    24 * u3 * v2 * v14 * v5 * v6 +
                    24 * u2 * v3 * v14 * v5 * v6 -
                    120 * u * v2 * v3 * v14 * v5 * v6 +
                    24 * u * v23 * v14 * v5 * v6 - 6 * u13 * v24 * v5 * v6 +
                    24 * u3 * v1 * v24 * v5 * v6 +
                    24 * u1 * v3 * v24 * v5 * v6 -
                    120 * u * v1 * v3 * v24 * v5 * v6 +
                    24 * u * v13 * v24 * v5 * v6 - 6 * u3 * v124 * v5 * v6 +
                    24 * u * v3 * v124 * v5 * v6 - 6 * u12 * v34 * v5 * v6 +
                    24 * u2 * v1 * v34 * v5 * v6 +
                    24 * u1 * v2 * v34 * v5 * v6 -
                    120 * u * v1 * v2 * v34 * v5 * v6 +
                    24 * u * v12 * v34 * v5 * v6 - 6 * u2 * v134 * v5 * v6 +
                    24 * u * v2 * v134 * v5 * v6 - 6 * u1 * v234 * v5 * v6 +
                    24 * u * v1 * v234 * v5 * v6 - 6 * u * v1234 * v5 * v6 +
                    2 * u234 * v15 * v6 - 6 * u34 * v2 * v15 * v6 -
                    6 * u24 * v3 * v15 * v6 + 24 * u4 * v2 * v3 * v15 * v6 -
                    6 * u4 * v23 * v15 * v6 - 6 * u23 * v4 * v15 * v6 +
                    24 * u3 * v2 * v4 * v15 * v6 +
                    24 * u2 * v3 * v4 * v15 * v6 -
                    120 * u * v2 * v3 * v4 * v15 * v6 +
                    24 * u * v23 * v4 * v15 * v6 - 6 * u3 * v24 * v15 * v6 +
                    24 * u * v3 * v24 * v15 * v6 - 6 * u2 * v34 * v15 * v6 +
                    24 * u * v2 * v34 * v15 * v6 - 6 * u * v234 * v15 * v6 +
                    2 * u134 * v25 * v6 - 6 * u34 * v1 * v25 * v6 -
                    6 * u14 * v3 * v25 * v6 + 24 * u4 * v1 * v3 * v25 * v6 -
                    6 * u4 * v13 * v25 * v6 - 6 * u13 * v4 * v25 * v6 +
                    24 * u3 * v1 * v4 * v25 * v6 +
                    24 * u1 * v3 * v4 * v25 * v6 -
                    120 * u * v1 * v3 * v4 * v25 * v6 +
                    24 * u * v13 * v4 * v25 * v6 - 6 * u3 * v14 * v25 * v6 +
                    24 * u * v3 * v14 * v25 * v6 - 6 * u1 * v34 * v25 * v6 +
                    24 * u * v1 * v34 * v25 * v6 - 6 * u * v134 * v25 * v6 +
                    2 * u34 * v125 * v6 - 6 * u4 * v3 * v125 * v6 -
                    6 * u3 * v4 * v125 * v6 + 24 * u * v3 * v4 * v125 * v6 -
                    6 * u * v34 * v125 * v6 + 2 * u124 * v35 * v6 -
                    6 * u24 * v1 * v35 * v6 - 6 * u14 * v2 * v35 * v6 +
                    24 * u4 * v1 * v2 * v35 * v6 - 6 * u4 * v12 * v35 * v6 -
                    6 * u12 * v4 * v35 * v6 + 24 * u2 * v1 * v4 * v35 * v6 +
                    24 * u1 * v2 * v4 * v35 * v6 -
                    120 * u * v1 * v2 * v4 * v35 * v6 +
                    24 * u * v12 * v4 * v35 * v6 - 6 * u2 * v14 * v35 * v6 +
                    24 * u * v2 * v14 * v35 * v6 - 6 * u1 * v24 * v35 * v6 +
                    24 * u * v1 * v24 * v35 * v6 - 6 * u * v124 * v35 * v6 +
                    2 * u24 * v135 * v6 - 6 * u4 * v2 * v135 * v6 -
                    6 * u2 * v4 * v135 * v6 + 24 * u * v2 * v4 * v135 * v6 -
                    6 * u * v24 * v135 * v6 + 2 * u14 * v235 * v6 -
                    6 * u4 * v1 * v235 * v6 - 6 * u1 * v4 * v235 * v6 +
                    24 * u * v1 * v4 * v235 * v6 - 6 * u * v14 * v235 * v6 +
                    2 * u4 * v1235 * v6 - 6 * u * v4 * v1235 * v6 +
                    2 * u123 * v45 * v6 - 6 * u23 * v1 * v45 * v6 -
                    6 * u13 * v2 * v45 * v6 + 24 * u3 * v1 * v2 * v45 * v6 -
                    6 * u3 * v12 * v45 * v6 - 6 * u12 * v3 * v45 * v6 +
                    24 * u2 * v1 * v3 * v45 * v6 +
                    24 * u1 * v2 * v3 * v45 * v6 -
                    120 * u * v1 * v2 * v3 * v45 * v6 +
                    24 * u * v12 * v3 * v45 * v6 - 6 * u2 * v13 * v45 * v6 +
                    24 * u * v2 * v13 * v45 * v6 - 6 * u1 * v23 * v45 * v6 +
                    24 * u * v1 * v23 * v45 * v6 - 6 * u * v123 * v45 * v6 +
                    2 * u23 * v145 * v6 - 6 * u3 * v2 * v145 * v6 -
                    6 * u2 * v3 * v145 * v6 + 24 * u * v2 * v3 * v145 * v6 -
                    6 * u * v23 * v145 * v6 + 2 * u13 * v245 * v6 -
                    6 * u3 * v1 * v245 * v6 - 6 * u1 * v3 * v245 * v6 +
                    24 * u * v1 * v3 * v245 * v6 - 6 * u * v13 * v245 * v6 +
                    2 * u3 * v1245 * v6 - 6 * u * v3 * v1245 * v6 +
                    2 * u12 * v345 * v6 - 6 * u2 * v1 * v345 * v6 -
                    6 * u1 * v2 * v345 * v6 + 24 * u * v1 * v2 * v345 * v6 -
                    6 * u * v12 * v345 * v6 + 2 * u2 * v1345 * v6 -
                    6 * u * v2 * v1345 * v6 + 2 * u1 * v2345 * v6 -
                    6 * u * v1 * v2345 * v6 + 2 * u * v12345 * v6 -
                    u2345 * v16 + 2 * u345 * v2 * v16 + 2 * u245 * v3 * v16 -
                    6 * u45 * v2 * v3 * v16 + 2 * u45 * v23 * v16 +
                    2 * u235 * v4 * v16 - 6 * u35 * v2 * v4 * v16 -
                    6 * u25 * v3 * v4 * v16 + 24 * u5 * v2 * v3 * v4 * v16 -
                    6 * u5 * v23 * v4 * v16 + 2 * u35 * v24 * v16 -
                    6 * u5 * v3 * v24 * v16 + 2 * u25 * v34 * v16 -
                    6 * u5 * v2 * v34 * v16 + 2 * u5 * v234 * v16 +
                    2 * u234 * v5 * v16 - 6 * u34 * v2 * v5 * v16 -
                    6 * u24 * v3 * v5 * v16 + 24 * u4 * v2 * v3 * v5 * v16 -
                    6 * u4 * v23 * v5 * v16 - 6 * u23 * v4 * v5 * v16 +
                    24 * u3 * v2 * v4 * v5 * v16 +
                    24 * u2 * v3 * v4 * v5 * v16 -
                    120 * u * v2 * v3 * v4 * v5 * v16 +
                    24 * u * v23 * v4 * v5 * v16 - 6 * u3 * v24 * v5 * v16 +
                    24 * u * v3 * v24 * v5 * v16 - 6 * u2 * v34 * v5 * v16 +
                    24 * u * v2 * v34 * v5 * v16 - 6 * u * v234 * v5 * v16 +
                    2 * u34 * v25 * v16 - 6 * u4 * v3 * v25 * v16 -
                    6 * u3 * v4 * v25 * v16 + 24 * u * v3 * v4 * v25 * v16 -
                    6 * u * v34 * v25 * v16 + 2 * u24 * v35 * v16 -
                    6 * u4 * v2 * v35 * v16 - 6 * u2 * v4 * v35 * v16 +
                    24 * u * v2 * v4 * v35 * v16 - 6 * u * v24 * v35 * v16 +
                    2 * u4 * v235 * v16 - 6 * u * v4 * v235 * v16 +
                    2 * u23 * v45 * v16 - 6 * u3 * v2 * v45 * v16 -
                    6 * u2 * v3 * v45 * v16 + 24 * u * v2 * v3 * v45 * v16 -
                    6 * u * v23 * v45 * v16 + 2 * u3 * v245 * v16 -
                    6 * u * v3 * v245 * v16 + 2 * u2 * v345 * v16 -
                    6 * u * v2 * v345 * v16 + 2 * u * v2345 * v16 -
                    u1345 * v26 + 2 * u345 * v1 * v26 + 2 * u145 * v3 * v26 -
                    6 * u45 * v1 * v3 * v26 + 2 * u45 * v13 * v26 +
                    2 * u135 * v4 * v26 - 6 * u35 * v1 * v4 * v26 -
                    6 * u15 * v3 * v4 * v26 + 24 * u5 * v1 * v3 * v4 * v26 -
                    6 * u5 * v13 * v4 * v26 + 2 * u35 * v14 * v26 -
                    6 * u5 * v3 * v14 * v26 + 2 * u15 * v34 * v26 -
                    6 * u5 * v1 * v34 * v26 + 2 * u5 * v134 * v26 +
                    2 * u134 * v5 * v26 - 6 * u34 * v1 * v5 * v26 -
                    6 * u14 * v3 * v5 * v26 + 24 * u4 * v1 * v3 * v5 * v26 -
                    6 * u4 * v13 * v5 * v26 - 6 * u13 * v4 * v5 * v26 +
                    24 * u3 * v1 * v4 * v5 * v26 +
                    24 * u1 * v3 * v4 * v5 * v26 -
                    120 * u * v1 * v3 * v4 * v5 * v26 +
                    24 * u * v13 * v4 * v5 * v26 - 6 * u3 * v14 * v5 * v26 +
                    24 * u * v3 * v14 * v5 * v26 - 6 * u1 * v34 * v5 * v26 +
                    24 * u * v1 * v34 * v5 * v26 - 6 * u * v134 * v5 * v26 +
                    2 * u34 * v15 * v26 - 6 * u4 * v3 * v15 * v26 -
                    6 * u3 * v4 * v15 * v26 + 24 * u * v3 * v4 * v15 * v26 -
                    6 * u * v34 * v15 * v26 + 2 * u14 * v35 * v26 -
                    6 * u4 * v1 * v35 * v26 - 6 * u1 * v4 * v35 * v26 +
                    24 * u * v1 * v4 * v35 * v26 - 6 * u * v14 * v35 * v26 +
                    2 * u4 * v135 * v26 - 6 * u * v4 * v135 * v26 +
                    2 * u13 * v45 * v26 - 6 * u3 * v1 * v45 * v26 -
                    6 * u1 * v3 * v45 * v26 + 24 * u * v1 * v3 * v45 * v26 -
                    6 * u * v13 * v45 * v26 + 2 * u3 * v145 * v26 -
                    6 * u * v3 * v145 * v26 + 2 * u1 * v345 * v26 -
                    6 * u * v1 * v345 * v26 + 2 * u * v1345 * v26 -
                    u345 * v126 + 2 * u45 * v3 * v126 + 2 * u35 * v4 * v126 -
                    6 * u5 * v3 * v4 * v126 + 2 * u5 * v34 * v126 +
                    2 * u34 * v5 * v126 - 6 * u4 * v3 * v5 * v126 -
                    6 * u3 * v4 * v5 * v126 + 24 * u * v3 * v4 * v5 * v126 -
                    6 * u * v34 * v5 * v126 + 2 * u4 * v35 * v126 -
                    6 * u * v4 * v35 * v126 + 2 * u3 * v45 * v126 -
                    6 * u * v3 * v45 * v126 + 2 * u * v345 * v126 -
                    u1245 * v36 + 2 * u245 * v1 * v36 + 2 * u145 * v2 * v36 -
                    6 * u45 * v1 * v2 * v36 + 2 * u45 * v12 * v36 +
                    2 * u125 * v4 * v36 - 6 * u25 * v1 * v4 * v36 -
                    6 * u15 * v2 * v4 * v36 + 24 * u5 * v1 * v2 * v4 * v36 -
                    6 * u5 * v12 * v4 * v36 + 2 * u25 * v14 * v36 -
                    6 * u5 * v2 * v14 * v36 + 2 * u15 * v24 * v36 -
                    6 * u5 * v1 * v24 * v36 + 2 * u5 * v124 * v36 +
                    2 * u124 * v5 * v36 - 6 * u24 * v1 * v5 * v36 -
                    6 * u14 * v2 * v5 * v36 + 24 * u4 * v1 * v2 * v5 * v36 -
                    6 * u4 * v12 * v5 * v36 - 6 * u12 * v4 * v5 * v36 +
                    24 * u2 * v1 * v4 * v5 * v36 +
                    24 * u1 * v2 * v4 * v5 * v36 -
                    120 * u * v1 * v2 * v4 * v5 * v36 +
                    24 * u * v12 * v4 * v5 * v36 - 6 * u2 * v14 * v5 * v36 +
                    24 * u * v2 * v14 * v5 * v36 - 6 * u1 * v24 * v5 * v36 +
                    24 * u * v1 * v24 * v5 * v36 - 6 * u * v124 * v5 * v36 +
                    2 * u24 * v15 * v36 - 6 * u4 * v2 * v15 * v36 -
                    6 * u2 * v4 * v15 * v36 + 24 * u * v2 * v4 * v15 * v36 -
                    6 * u * v24 * v15 * v36 + 2 * u14 * v25 * v36 -
                    6 * u4 * v1 * v25 * v36 - 6 * u1 * v4 * v25 * v36 +
                    24 * u * v1 * v4 * v25 * v36 - 6 * u * v14 * v25 * v36 +
                    2 * u4 * v125 * v36 - 6 * u * v4 * v125 * v36 +
                    2 * u12 * v45 * v36 - 6 * u2 * v1 * v45 * v36 -
                    6 * u1 * v2 * v45 * v36 + 24 * u * v1 * v2 * v45 * v36 -
                    6 * u * v12 * v45 * v36 + 2 * u2 * v145 * v36 -
                    6 * u * v2 * v145 * v36 + 2 * u1 * v245 * v36 -
                    6 * u * v1 * v245 * v36 + 2 * u * v1245 * v36 -
                    u245 * v136 + 2 * u45 * v2 * v136 + 2 * u25 * v4 * v136 -
                    6 * u5 * v2 * v4 * v136 + 2 * u5 * v24 * v136 +
                    2 * u24 * v5 * v136 - 6 * u4 * v2 * v5 * v136 -
                    6 * u2 * v4 * v5 * v136 + 24 * u * v2 * v4 * v5 * v136 -
                    6 * u * v24 * v5 * v136 + 2 * u4 * v25 * v136 -
                    6 * u * v4 * v25 * v136 + 2 * u2 * v45 * v136 -
                    6 * u * v2 * v45 * v136 + 2 * u * v245 * v136 -
                    u145 * v236 + 2 * u45 * v1 * v236 + 2 * u15 * v4 * v236 -
                    6 * u5 * v1 * v4 * v236 + 2 * u5 * v14 * v236 +
                    2 * u14 * v5 * v236 - 6 * u4 * v1 * v5 * v236 -
                    6 * u1 * v4 * v5 * v236 + 24 * u * v1 * v4 * v5 * v236 -
                    6 * u * v14 * v5 * v236 + 2 * u4 * v15 * v236 -
                    6 * u * v4 * v15 * v236 + 2 * u1 * v45 * v236 -
                    6 * u * v1 * v45 * v236 + 2 * u * v145 * v236 -
                    u45 * v1236 + 2 * u5 * v4 * v1236 + 2 * u4 * v5 * v1236 -
                    6 * u * v4 * v5 * v1236 + 2 * u * v45 * v1236 -
                    u1235 * v46 + 2 * u235 * v1 * v46 + 2 * u135 * v2 * v46 -
                    6 * u35 * v1 * v2 * v46 + 2 * u35 * v12 * v46 +
                    2 * u125 * v3 * v46 - 6 * u25 * v1 * v3 * v46 -
                    6 * u15 * v2 * v3 * v46 + 24 * u5 * v1 * v2 * v3 * v46 -
                    6 * u5 * v12 * v3 * v46 + 2 * u25 * v13 * v46 -
                    6 * u5 * v2 * v13 * v46 + 2 * u15 * v23 * v46 -
                    6 * u5 * v1 * v23 * v46 + 2 * u5 * v123 * v46 +
                    2 * u123 * v5 * v46 - 6 * u23 * v1 * v5 * v46 -
                    6 * u13 * v2 * v5 * v46 + 24 * u3 * v1 * v2 * v5 * v46 -
                    6 * u3 * v12 * v5 * v46 - 6 * u12 * v3 * v5 * v46 +
                    24 * u2 * v1 * v3 * v5 * v46 +
                    24 * u1 * v2 * v3 * v5 * v46 -
                    120 * u * v1 * v2 * v3 * v5 * v46 +
                    24 * u * v12 * v3 * v5 * v46 - 6 * u2 * v13 * v5 * v46 +
                    24 * u * v2 * v13 * v5 * v46 - 6 * u1 * v23 * v5 * v46 +
                    24 * u * v1 * v23 * v5 * v46 - 6 * u * v123 * v5 * v46 +
                    2 * u23 * v15 * v46 - 6 * u3 * v2 * v15 * v46 -
                    6 * u2 * v3 * v15 * v46 + 24 * u * v2 * v3 * v15 * v46 -
                    6 * u * v23 * v15 * v46 + 2 * u13 * v25 * v46 -
                    6 * u3 * v1 * v25 * v46 - 6 * u1 * v3 * v25 * v46 +
                    24 * u * v1 * v3 * v25 * v46 - 6 * u * v13 * v25 * v46 +
                    2 * u3 * v125 * v46 - 6 * u * v3 * v125 * v46 +
                    2 * u12 * v35 * v46 - 6 * u2 * v1 * v35 * v46 -
                    6 * u1 * v2 * v35 * v46 + 24 * u * v1 * v2 * v35 * v46 -
                    6 * u * v12 * v35 * v46 + 2 * u2 * v135 * v46 -
                    6 * u * v2 * v135 * v46 + 2 * u1 * v235 * v46 -
                    6 * u * v1 * v235 * v46 + 2 * u * v1235 * v46 -
                    u235 * v146 + 2 * u35 * v2 * v146 + 2 * u25 * v3 * v146 -
                    6 * u5 * v2 * v3 * v146 + 2 * u5 * v23 * v146 +
                    2 * u23 * v5 * v146 - 6 * u3 * v2 * v5 * v146 -
                    6 * u2 * v3 * v5 * v146 + 24 * u * v2 * v3 * v5 * v146 -
                    6 * u * v23 * v5 * v146 + 2 * u3 * v25 * v146 -
                    6 * u * v3 * v25 * v146 + 2 * u2 * v35 * v146 -
                    6 * u * v2 * v35 * v146 + 2 * u * v235 * v146 -
                    u135 * v246 + 2 * u35 * v1 * v246 + 2 * u15 * v3 * v246 -
                    6 * u5 * v1 * v3 * v246 + 2 * u5 * v13 * v246 +
                    2 * u13 * v5 * v246 - 6 * u3 * v1 * v5 * v246 -
                    6 * u1 * v3 * v5 * v246 + 24 * u * v1 * v3 * v5 * v246 -
                    6 * u * v13 * v5 * v246 + 2 * u3 * v15 * v246 -
                    6 * u * v3 * v15 * v246 + 2 * u1 * v35 * v246 -
                    6 * u * v1 * v35 * v246 + 2 * u * v135 * v246 -
                    u35 * v1246 + 2 * u5 * v3 * v1246 + 2 * u3 * v5 * v1246 -
                    6 * u * v3 * v5 * v1246 + 2 * u * v35 * v1246 -
                    u125 * v346 + 2 * u25 * v1 * v346 + 2 * u15 * v2 * v346 -
                    6 * u5 * v1 * v2 * v346 + 2 * u5 * v12 * v346 +
                    2 * u12 * v5 * v346 - 6 * u2 * v1 * v5 * v346 -
                    6 * u1 * v2 * v5 * v346 + 24 * u * v1 * v2 * v5 * v346 -
                    6 * u * v12 * v5 * v346 + 2 * u2 * v15 * v346 -
                    6 * u * v2 * v15 * v346 + 2 * u1 * v25 * v346 -
                    6 * u * v1 * v25 * v346 + 2 * u * v125 * v346 -
                    u25 * v1346 + 2 * u5 * v2 * v1346 + 2 * u2 * v5 * v1346 -
                    6 * u * v2 * v5 * v1346 + 2 * u * v25 * v1346 -
                    u15 * v2346 + 2 * u5 * v1 * v2346 + 2 * u1 * v5 * v2346 -
                    6 * u * v1 * v5 * v2346 + 2 * u * v15 * v2346 -
                    u5 * v12346 + 2 * u * v5 * v12346 - u1234 * v56 +
                    2 * u234 * v1 * v56 + 2 * u134 * v2 * v56 -
                    6 * u34 * v1 * v2 * v56 + 2 * u34 * v12 * v56 +
                    2 * u124 * v3 * v56 - 6 * u24 * v1 * v3 * v56 -
                    6 * u14 * v2 * v3 * v56 + 24 * u4 * v1 * v2 * v3 * v56 -
                    6 * u4 * v12 * v3 * v56 + 2 * u24 * v13 * v56 -
                    6 * u4 * v2 * v13 * v56 + 2 * u14 * v23 * v56 -
                    6 * u4 * v1 * v23 * v56 + 2 * u4 * v123 * v56 +
                    2 * u123 * v4 * v56 - 6 * u23 * v1 * v4 * v56 -
                    6 * u13 * v2 * v4 * v56 + 24 * u3 * v1 * v2 * v4 * v56 -
                    6 * u3 * v12 * v4 * v56 - 6 * u12 * v3 * v4 * v56 +
                    24 * u2 * v1 * v3 * v4 * v56 +
                    24 * u1 * v2 * v3 * v4 * v56 -
                    120 * u * v1 * v2 * v3 * v4 * v56 +
                    24 * u * v12 * v3 * v4 * v56 - 6 * u2 * v13 * v4 * v56 +
                    24 * u * v2 * v13 * v4 * v56 - 6 * u1 * v23 * v4 * v56 +
                    24 * u * v1 * v23 * v4 * v56 - 6 * u * v123 * v4 * v56 +
                    2 * u23 * v14 * v56 - 6 * u3 * v2 * v14 * v56 -
                    6 * u2 * v3 * v14 * v56 + 24 * u * v2 * v3 * v14 * v56 -
                    6 * u * v23 * v14 * v56 + 2 * u13 * v24 * v56 -
                    6 * u3 * v1 * v24 * v56 - 6 * u1 * v3 * v24 * v56 +
                    24 * u * v1 * v3 * v24 * v56 - 6 * u * v13 * v24 * v56 +
                    2 * u3 * v124 * v56 - 6 * u * v3 * v124 * v56 +
                    2 * u12 * v34 * v56 - 6 * u2 * v1 * v34 * v56 -
                    6 * u1 * v2 * v34 * v56 + 24 * u * v1 * v2 * v34 * v56 -
                    6 * u * v12 * v34 * v56 + 2 * u2 * v134 * v56 -
                    6 * u * v2 * v134 * v56 + 2 * u1 * v234 * v56 -
                    6 * u * v1 * v234 * v56 + 2 * u * v1234 * v56 -
                    u234 * v156 + 2 * u34 * v2 * v156 + 2 * u24 * v3 * v156 -
                    6 * u4 * v2 * v3 * v156 + 2 * u4 * v23 * v156 +
                    2 * u23 * v4 * v156 - 6 * u3 * v2 * v4 * v156 -
                    6 * u2 * v3 * v4 * v156 + 24 * u * v2 * v3 * v4 * v156 -
                    6 * u * v23 * v4 * v156 + 2 * u3 * v24 * v156 -
                    6 * u * v3 * v24 * v156 + 2 * u2 * v34 * v156 -
                    6 * u * v2 * v34 * v156 + 2 * u * v234 * v156 -
                    u134 * v256 + 2 * u34 * v1 * v256 + 2 * u14 * v3 * v256 -
                    6 * u4 * v1 * v3 * v256 + 2 * u4 * v13 * v256 +
                    2 * u13 * v4 * v256 - 6 * u3 * v1 * v4 * v256 -
                    6 * u1 * v3 * v4 * v256 + 24 * u * v1 * v3 * v4 * v256 -
                    6 * u * v13 * v4 * v256 + 2 * u3 * v14 * v256 -
                    6 * u * v3 * v14 * v256 + 2 * u1 * v34 * v256 -
                    6 * u * v1 * v34 * v256 + 2 * u * v134 * v256 -
                    u34 * v1256 + 2 * u4 * v3 * v1256 + 2 * u3 * v4 * v1256 -
                    6 * u * v3 * v4 * v1256 + 2 * u * v34 * v1256 -
                    u124 * v356 + 2 * u24 * v1 * v356 + 2 * u14 * v2 * v356 -
                    6 * u4 * v1 * v2 * v356 + 2 * u4 * v12 * v356 +
                    2 * u12 * v4 * v356 - 6 * u2 * v1 * v4 * v356 -
                    6 * u1 * v2 * v4 * v356 + 24 * u * v1 * v2 * v4 * v356 -
                    6 * u * v12 * v4 * v356 + 2 * u2 * v14 * v356 -
                    6 * u * v2 * v14 * v356 + 2 * u1 * v24 * v356 -
                    6 * u * v1 * v24 * v356 + 2 * u * v124 * v356 -
                    u24 * v1356 + 2 * u4 * v2 * v1356 + 2 * u2 * v4 * v1356 -
                    6 * u * v2 * v4 * v1356 + 2 * u * v24 * v1356 -
                    u14 * v2356 + 2 * u4 * v1 * v2356 + 2 * u1 * v4 * v2356 -
                    6 * u * v1 * v4 * v2356 + 2 * u * v14 * v2356 -
                    u4 * v12356 + 2 * u * v4 * v12356 - u123 * v456 +
                    2 * u23 * v1 * v456 + 2 * u13 * v2 * v456 -
                    6 * u3 * v1 * v2 * v456 + 2 * u3 * v12 * v456 +
                    2 * u12 * v3 * v456 - 6 * u2 * v1 * v3 * v456 -
                    6 * u1 * v2 * v3 * v456 + 24 * u * v1 * v2 * v3 * v456 -
                    6 * u * v12 * v3 * v456 + 2 * u2 * v13 * v456 -
                    6 * u * v2 * v13 * v456 + 2 * u1 * v23 * v456 -
                    6 * u * v1 * v23 * v456 + 2 * u * v123 * v456 -
                    u23 * v1456 + 2 * u3 * v2 * v1456 + 2 * u2 * v3 * v1456 -
                    6 * u * v2 * v3 * v1456 + 2 * u * v23 * v1456 -
                    u13 * v2456 + 2 * u3 * v1 * v2456 + 2 * u1 * v3 * v2456 -
                    6 * u * v1 * v3 * v2456 + 2 * u * v13 * v2456 -
                    u3 * v12456 + 2 * u * v3 * v12456 - u12 * v3456 +
                    2 * u2 * v1 * v3456 + 2 * u1 * v2 * v3456 -
                    6 * u * v1 * v2 * v3456 + 2 * u * v12 * v3456 -
                    u2 * v13456 + 2 * u * v2 * v13456 - u1 * v23456 +
                    2 * u * v1 * v23456 - u * v123456,
            .dual7 = u7 - u * v7,
            .dual17 = u17 - u7 * v1 - u1 * v7 + 2 * u * v1 * v7 - u * v17,
            .dual27 = u27 - u7 * v2 - u2 * v7 + 2 * u * v2 * v7 - u * v27,
            .dual127 = u127 - u27 * v1 - u17 * v2 + 2 * u7 * v1 * v2 -
                       u7 * v12 - u12 * v7 + 2 * u2 * v1 * v7 +
                       2 * u1 * v2 * v7 - 6 * u * v1 * v2 * v7 +
                       2 * u * v12 * v7 - u2 * v17 + 2 * u * v2 * v17 -
                       u1 * v27 + 2 * u * v1 * v27 - u * v127,
            .dual37 = u37 - u7 * v3 - u3 * v7 + 2 * u * v3 * v7 - u * v37,
            .dual137 = u137 - u37 * v1 - u17 * v3 + 2 * u7 * v1 * v3 -
                       u7 * v13 - u13 * v7 + 2 * u3 * v1 * v7 +
                       2 * u1 * v3 * v7 - 6 * u * v1 * v3 * v7 +
                       2 * u * v13 * v7 - u3 * v17 + 2 * u * v3 * v17 -
                       u1 * v37 + 2 * u * v1 * v37 - u * v137,
            .dual237 = u237 - u37 * v2 - u27 * v3 + 2 * u7 * v2 * v3 -
                       u7 * v23 - u23 * v7 + 2 * u3 * v2 * v7 +
                       2 * u2 * v3 * v7 - 6 * u * v2 * v3 * v7 +
                       2 * u * v23 * v7 - u3 * v27 + 2 * u * v3 * v27 -
                       u2 * v37 + 2 * u * v2 * v37 - u * v237,
            .dual1237 = u1237 - u237 * v1 - u137 * v2 + 2 * u37 * v1 * v2 -
                        u37 * v12 - u127 * v3 + 2 * u27 * v1 * v3 +
                        2 * u17 * v2 * v3 - 6 * u7 * v1 * v2 * v3 +
                        2 * u7 * v12 * v3 - u27 * v13 + 2 * u7 * v2 * v13 -
                        u17 * v23 + 2 * u7 * v1 * v23 - u7 * v123 - u123 * v7 +
                        2 * u23 * v1 * v7 + 2 * u13 * v2 * v7 -
                        6 * u3 * v1 * v2 * v7 + 2 * u3 * v12 * v7 +
                        2 * u12 * v3 * v7 - 6 * u2 * v1 * v3 * v7 -
                        6 * u1 * v2 * v3 * v7 + 24 * u * v1 * v2 * v3 * v7 -
                        6 * u * v12 * v3 * v7 + 2 * u2 * v13 * v7 -
                        6 * u * v2 * v13 * v7 + 2 * u1 * v23 * v7 -
                        6 * u * v1 * v23 * v7 + 2 * u * v123 * v7 - u23 * v17 +
                        2 * u3 * v2 * v17 + 2 * u2 * v3 * v17 -
                        6 * u * v2 * v3 * v17 + 2 * u * v23 * v17 - u13 * v27 +
                        2 * u3 * v1 * v27 + 2 * u1 * v3 * v27 -
                        6 * u * v1 * v3 * v27 + 2 * u * v13 * v27 - u3 * v127 +
                        2 * u * v3 * v127 - u12 * v37 + 2 * u2 * v1 * v37 +
                        2 * u1 * v2 * v37 - 6 * u * v1 * v2 * v37 +
                        2 * u * v12 * v37 - u2 * v137 + 2 * u * v2 * v137 -
                        u1 * v237 + 2 * u * v1 * v237 - u * v1237,
            .dual47 = u47 - u7 * v4 - u4 * v7 + 2 * u * v4 * v7 - u * v47,
            .dual147 = u147 - u47 * v1 - u17 * v4 + 2 * u7 * v1 * v4 -
                       u7 * v14 - u14 * v7 + 2 * u4 * v1 * v7 +
                       2 * u1 * v4 * v7 - 6 * u * v1 * v4 * v7 +
                       2 * u * v14 * v7 - u4 * v17 + 2 * u * v4 * v17 -
                       u1 * v47 + 2 * u * v1 * v47 - u * v147,
            .dual247 = u247 - u47 * v2 - u27 * v4 + 2 * u7 * v2 * v4 -
                       u7 * v24 - u24 * v7 + 2 * u4 * v2 * v7 +
                       2 * u2 * v4 * v7 - 6 * u * v2 * v4 * v7 +
                       2 * u * v24 * v7 - u4 * v27 + 2 * u * v4 * v27 -
                       u2 * v47 + 2 * u * v2 * v47 - u * v247,
            .dual1247 = u1247 - u247 * v1 - u147 * v2 + 2 * u47 * v1 * v2 -
                        u47 * v12 - u127 * v4 + 2 * u27 * v1 * v4 +
                        2 * u17 * v2 * v4 - 6 * u7 * v1 * v2 * v4 +
                        2 * u7 * v12 * v4 - u27 * v14 + 2 * u7 * v2 * v14 -
                        u17 * v24 + 2 * u7 * v1 * v24 - u7 * v124 - u124 * v7 +
                        2 * u24 * v1 * v7 + 2 * u14 * v2 * v7 -
                        6 * u4 * v1 * v2 * v7 + 2 * u4 * v12 * v7 +
                        2 * u12 * v4 * v7 - 6 * u2 * v1 * v4 * v7 -
                        6 * u1 * v2 * v4 * v7 + 24 * u * v1 * v2 * v4 * v7 -
                        6 * u * v12 * v4 * v7 + 2 * u2 * v14 * v7 -
                        6 * u * v2 * v14 * v7 + 2 * u1 * v24 * v7 -
                        6 * u * v1 * v24 * v7 + 2 * u * v124 * v7 - u24 * v17 +
                        2 * u4 * v2 * v17 + 2 * u2 * v4 * v17 -
                        6 * u * v2 * v4 * v17 + 2 * u * v24 * v17 - u14 * v27 +
                        2 * u4 * v1 * v27 + 2 * u1 * v4 * v27 -
                        6 * u * v1 * v4 * v27 + 2 * u * v14 * v27 - u4 * v127 +
                        2 * u * v4 * v127 - u12 * v47 + 2 * u2 * v1 * v47 +
                        2 * u1 * v2 * v47 - 6 * u * v1 * v2 * v47 +
                        2 * u * v12 * v47 - u2 * v147 + 2 * u * v2 * v147 -
                        u1 * v247 + 2 * u * v1 * v247 - u * v1247,
            .dual347 = u347 - u47 * v3 - u37 * v4 + 2 * u7 * v3 * v4 -
                       u7 * v34 - u34 * v7 + 2 * u4 * v3 * v7 +
                       2 * u3 * v4 * v7 - 6 * u * v3 * v4 * v7 +
                       2 * u * v34 * v7 - u4 * v37 + 2 * u * v4 * v37 -
                       u3 * v47 + 2 * u * v3 * v47 - u * v347,
            .dual1347 = u1347 - u347 * v1 - u147 * v3 + 2 * u47 * v1 * v3 -
                        u47 * v13 - u137 * v4 + 2 * u37 * v1 * v4 +
                        2 * u17 * v3 * v4 - 6 * u7 * v1 * v3 * v4 +
                        2 * u7 * v13 * v4 - u37 * v14 + 2 * u7 * v3 * v14 -
                        u17 * v34 + 2 * u7 * v1 * v34 - u7 * v134 - u134 * v7 +
                        2 * u34 * v1 * v7 + 2 * u14 * v3 * v7 -
                        6 * u4 * v1 * v3 * v7 + 2 * u4 * v13 * v7 +
                        2 * u13 * v4 * v7 - 6 * u3 * v1 * v4 * v7 -
                        6 * u1 * v3 * v4 * v7 + 24 * u * v1 * v3 * v4 * v7 -
                        6 * u * v13 * v4 * v7 + 2 * u3 * v14 * v7 -
                        6 * u * v3 * v14 * v7 + 2 * u1 * v34 * v7 -
                        6 * u * v1 * v34 * v7 + 2 * u * v134 * v7 - u34 * v17 +
                        2 * u4 * v3 * v17 + 2 * u3 * v4 * v17 -
                        6 * u * v3 * v4 * v17 + 2 * u * v34 * v17 - u14 * v37 +
                        2 * u4 * v1 * v37 + 2 * u1 * v4 * v37 -
                        6 * u * v1 * v4 * v37 + 2 * u * v14 * v37 - u4 * v137 +
                        2 * u * v4 * v137 - u13 * v47 + 2 * u3 * v1 * v47 +
                        2 * u1 * v3 * v47 - 6 * u * v1 * v3 * v47 +
                        2 * u * v13 * v47 - u3 * v147 + 2 * u * v3 * v147 -
                        u1 * v347 + 2 * u * v1 * v347 - u * v1347,
            .dual2347 = u2347 - u347 * v2 - u247 * v3 + 2 * u47 * v2 * v3 -
                        u47 * v23 - u237 * v4 + 2 * u37 * v2 * v4 +
                        2 * u27 * v3 * v4 - 6 * u7 * v2 * v3 * v4 +
                        2 * u7 * v23 * v4 - u37 * v24 + 2 * u7 * v3 * v24 -
                        u27 * v34 + 2 * u7 * v2 * v34 - u7 * v234 - u234 * v7 +
                        2 * u34 * v2 * v7 + 2 * u24 * v3 * v7 -
                        6 * u4 * v2 * v3 * v7 + 2 * u4 * v23 * v7 +
                        2 * u23 * v4 * v7 - 6 * u3 * v2 * v4 * v7 -
                        6 * u2 * v3 * v4 * v7 + 24 * u * v2 * v3 * v4 * v7 -
                        6 * u * v23 * v4 * v7 + 2 * u3 * v24 * v7 -
                        6 * u * v3 * v24 * v7 + 2 * u2 * v34 * v7 -
                        6 * u * v2 * v34 * v7 + 2 * u * v234 * v7 - u34 * v27 +
                        2 * u4 * v3 * v27 + 2 * u3 * v4 * v27 -
                        6 * u * v3 * v4 * v27 + 2 * u * v34 * v27 - u24 * v37 +
                        2 * u4 * v2 * v37 + 2 * u2 * v4 * v37 -
                        6 * u * v2 * v4 * v37 + 2 * u * v24 * v37 - u4 * v237 +
                        2 * u * v4 * v237 - u23 * v47 + 2 * u3 * v2 * v47 +
                        2 * u2 * v3 * v47 - 6 * u * v2 * v3 * v47 +
                        2 * u * v23 * v47 - u3 * v247 + 2 * u * v3 * v247 -
                        u2 * v347 + 2 * u * v2 * v347 - u * v2347,
            .dual12347 =
                    u12347 - u2347 * v1 - u1347 * v2 + 2 * u347 * v1 * v2 -
                    u347 * v12 - u1247 * v3 + 2 * u247 * v1 * v3 +
                    2 * u147 * v2 * v3 - 6 * u47 * v1 * v2 * v3 +
                    2 * u47 * v12 * v3 - u247 * v13 + 2 * u47 * v2 * v13 -
                    u147 * v23 + 2 * u47 * v1 * v23 - u47 * v123 - u1237 * v4 +
                    2 * u237 * v1 * v4 + 2 * u137 * v2 * v4 -
                    6 * u37 * v1 * v2 * v4 + 2 * u37 * v12 * v4 +
                    2 * u127 * v3 * v4 - 6 * u27 * v1 * v3 * v4 -
                    6 * u17 * v2 * v3 * v4 + 24 * u7 * v1 * v2 * v3 * v4 -
                    6 * u7 * v12 * v3 * v4 + 2 * u27 * v13 * v4 -
                    6 * u7 * v2 * v13 * v4 + 2 * u17 * v23 * v4 -
                    6 * u7 * v1 * v23 * v4 + 2 * u7 * v123 * v4 - u237 * v14 +
                    2 * u37 * v2 * v14 + 2 * u27 * v3 * v14 -
                    6 * u7 * v2 * v3 * v14 + 2 * u7 * v23 * v14 - u137 * v24 +
                    2 * u37 * v1 * v24 + 2 * u17 * v3 * v24 -
                    6 * u7 * v1 * v3 * v24 + 2 * u7 * v13 * v24 - u37 * v124 +
                    2 * u7 * v3 * v124 - u127 * v34 + 2 * u27 * v1 * v34 +
                    2 * u17 * v2 * v34 - 6 * u7 * v1 * v2 * v34 +
                    2 * u7 * v12 * v34 - u27 * v134 + 2 * u7 * v2 * v134 -
                    u17 * v234 + 2 * u7 * v1 * v234 - u7 * v1234 - u1234 * v7 +
                    2 * u234 * v1 * v7 + 2 * u134 * v2 * v7 -
                    6 * u34 * v1 * v2 * v7 + 2 * u34 * v12 * v7 +
                    2 * u124 * v3 * v7 - 6 * u24 * v1 * v3 * v7 -
                    6 * u14 * v2 * v3 * v7 + 24 * u4 * v1 * v2 * v3 * v7 -
                    6 * u4 * v12 * v3 * v7 + 2 * u24 * v13 * v7 -
                    6 * u4 * v2 * v13 * v7 + 2 * u14 * v23 * v7 -
                    6 * u4 * v1 * v23 * v7 + 2 * u4 * v123 * v7 +
                    2 * u123 * v4 * v7 - 6 * u23 * v1 * v4 * v7 -
                    6 * u13 * v2 * v4 * v7 + 24 * u3 * v1 * v2 * v4 * v7 -
                    6 * u3 * v12 * v4 * v7 - 6 * u12 * v3 * v4 * v7 +
                    24 * u2 * v1 * v3 * v4 * v7 + 24 * u1 * v2 * v3 * v4 * v7 -
                    120 * u * v1 * v2 * v3 * v4 * v7 +
                    24 * u * v12 * v3 * v4 * v7 - 6 * u2 * v13 * v4 * v7 +
                    24 * u * v2 * v13 * v4 * v7 - 6 * u1 * v23 * v4 * v7 +
                    24 * u * v1 * v23 * v4 * v7 - 6 * u * v123 * v4 * v7 +
                    2 * u23 * v14 * v7 - 6 * u3 * v2 * v14 * v7 -
                    6 * u2 * v3 * v14 * v7 + 24 * u * v2 * v3 * v14 * v7 -
                    6 * u * v23 * v14 * v7 + 2 * u13 * v24 * v7 -
                    6 * u3 * v1 * v24 * v7 - 6 * u1 * v3 * v24 * v7 +
                    24 * u * v1 * v3 * v24 * v7 - 6 * u * v13 * v24 * v7 +
                    2 * u3 * v124 * v7 - 6 * u * v3 * v124 * v7 +
                    2 * u12 * v34 * v7 - 6 * u2 * v1 * v34 * v7 -
                    6 * u1 * v2 * v34 * v7 + 24 * u * v1 * v2 * v34 * v7 -
                    6 * u * v12 * v34 * v7 + 2 * u2 * v134 * v7 -
                    6 * u * v2 * v134 * v7 + 2 * u1 * v234 * v7 -
                    6 * u * v1 * v234 * v7 + 2 * u * v1234 * v7 - u234 * v17 +
                    2 * u34 * v2 * v17 + 2 * u24 * v3 * v17 -
                    6 * u4 * v2 * v3 * v17 + 2 * u4 * v23 * v17 +
                    2 * u23 * v4 * v17 - 6 * u3 * v2 * v4 * v17 -
                    6 * u2 * v3 * v4 * v17 + 24 * u * v2 * v3 * v4 * v17 -
                    6 * u * v23 * v4 * v17 + 2 * u3 * v24 * v17 -
                    6 * u * v3 * v24 * v17 + 2 * u2 * v34 * v17 -
                    6 * u * v2 * v34 * v17 + 2 * u * v234 * v17 - u134 * v27 +
                    2 * u34 * v1 * v27 + 2 * u14 * v3 * v27 -
                    6 * u4 * v1 * v3 * v27 + 2 * u4 * v13 * v27 +
                    2 * u13 * v4 * v27 - 6 * u3 * v1 * v4 * v27 -
                    6 * u1 * v3 * v4 * v27 + 24 * u * v1 * v3 * v4 * v27 -
                    6 * u * v13 * v4 * v27 + 2 * u3 * v14 * v27 -
                    6 * u * v3 * v14 * v27 + 2 * u1 * v34 * v27 -
                    6 * u * v1 * v34 * v27 + 2 * u * v134 * v27 - u34 * v127 +
                    2 * u4 * v3 * v127 + 2 * u3 * v4 * v127 -
                    6 * u * v3 * v4 * v127 + 2 * u * v34 * v127 - u124 * v37 +
                    2 * u24 * v1 * v37 + 2 * u14 * v2 * v37 -
                    6 * u4 * v1 * v2 * v37 + 2 * u4 * v12 * v37 +
                    2 * u12 * v4 * v37 - 6 * u2 * v1 * v4 * v37 -
                    6 * u1 * v2 * v4 * v37 + 24 * u * v1 * v2 * v4 * v37 -
                    6 * u * v12 * v4 * v37 + 2 * u2 * v14 * v37 -
                    6 * u * v2 * v14 * v37 + 2 * u1 * v24 * v37 -
                    6 * u * v1 * v24 * v37 + 2 * u * v124 * v37 - u24 * v137 +
                    2 * u4 * v2 * v137 + 2 * u2 * v4 * v137 -
                    6 * u * v2 * v4 * v137 + 2 * u * v24 * v137 - u14 * v237 +
                    2 * u4 * v1 * v237 + 2 * u1 * v4 * v237 -
                    6 * u * v1 * v4 * v237 + 2 * u * v14 * v237 - u4 * v1237 +
                    2 * u * v4 * v1237 - u123 * v47 + 2 * u23 * v1 * v47 +
                    2 * u13 * v2 * v47 - 6 * u3 * v1 * v2 * v47 +
                    2 * u3 * v12 * v47 + 2 * u12 * v3 * v47 -
                    6 * u2 * v1 * v3 * v47 - 6 * u1 * v2 * v3 * v47 +
                    24 * u * v1 * v2 * v3 * v47 - 6 * u * v12 * v3 * v47 +
                    2 * u2 * v13 * v47 - 6 * u * v2 * v13 * v47 +
                    2 * u1 * v23 * v47 - 6 * u * v1 * v23 * v47 +
                    2 * u * v123 * v47 - u23 * v147 + 2 * u3 * v2 * v147 +
                    2 * u2 * v3 * v147 - 6 * u * v2 * v3 * v147 +
                    2 * u * v23 * v147 - u13 * v247 + 2 * u3 * v1 * v247 +
                    2 * u1 * v3 * v247 - 6 * u * v1 * v3 * v247 +
                    2 * u * v13 * v247 - u3 * v1247 + 2 * u * v3 * v1247 -
                    u12 * v347 + 2 * u2 * v1 * v347 + 2 * u1 * v2 * v347 -
                    6 * u * v1 * v2 * v347 + 2 * u * v12 * v347 - u2 * v1347 +
                    2 * u * v2 * v1347 - u1 * v2347 + 2 * u * v1 * v2347 -
                    u * v12347,
            .dual57 = u57 - u7 * v5 - u5 * v7 + 2 * u * v5 * v7 - u * v57,
            .dual157 = u157 - u57 * v1 - u17 * v5 + 2 * u7 * v1 * v5 -
                       u7 * v15 - u15 * v7 + 2 * u5 * v1 * v7 +
                       2 * u1 * v5 * v7 - 6 * u * v1 * v5 * v7 +
                       2 * u * v15 * v7 - u5 * v17 + 2 * u * v5 * v17 -
                       u1 * v57 + 2 * u * v1 * v57 - u * v157,
            .dual257 = u257 - u57 * v2 - u27 * v5 + 2 * u7 * v2 * v5 -
                       u7 * v25 - u25 * v7 + 2 * u5 * v2 * v7 +
                       2 * u2 * v5 * v7 - 6 * u * v2 * v5 * v7 +
                       2 * u * v25 * v7 - u5 * v27 + 2 * u * v5 * v27 -
                       u2 * v57 + 2 * u * v2 * v57 - u * v257,
            .dual1257 = u1257 - u257 * v1 - u157 * v2 + 2 * u57 * v1 * v2 -
                        u57 * v12 - u127 * v5 + 2 * u27 * v1 * v5 +
                        2 * u17 * v2 * v5 - 6 * u7 * v1 * v2 * v5 +
                        2 * u7 * v12 * v5 - u27 * v15 + 2 * u7 * v2 * v15 -
                        u17 * v25 + 2 * u7 * v1 * v25 - u7 * v125 - u125 * v7 +
                        2 * u25 * v1 * v7 + 2 * u15 * v2 * v7 -
                        6 * u5 * v1 * v2 * v7 + 2 * u5 * v12 * v7 +
                        2 * u12 * v5 * v7 - 6 * u2 * v1 * v5 * v7 -
                        6 * u1 * v2 * v5 * v7 + 24 * u * v1 * v2 * v5 * v7 -
                        6 * u * v12 * v5 * v7 + 2 * u2 * v15 * v7 -
                        6 * u * v2 * v15 * v7 + 2 * u1 * v25 * v7 -
                        6 * u * v1 * v25 * v7 + 2 * u * v125 * v7 - u25 * v17 +
                        2 * u5 * v2 * v17 + 2 * u2 * v5 * v17 -
                        6 * u * v2 * v5 * v17 + 2 * u * v25 * v17 - u15 * v27 +
                        2 * u5 * v1 * v27 + 2 * u1 * v5 * v27 -
                        6 * u * v1 * v5 * v27 + 2 * u * v15 * v27 - u5 * v127 +
                        2 * u * v5 * v127 - u12 * v57 + 2 * u2 * v1 * v57 +
                        2 * u1 * v2 * v57 - 6 * u * v1 * v2 * v57 +
                        2 * u * v12 * v57 - u2 * v157 + 2 * u * v2 * v157 -
                        u1 * v257 + 2 * u * v1 * v257 - u * v1257,
            .dual357 = u357 - u57 * v3 - u37 * v5 + 2 * u7 * v3 * v5 -
                       u7 * v35 - u35 * v7 + 2 * u5 * v3 * v7 +
                       2 * u3 * v5 * v7 - 6 * u * v3 * v5 * v7 +
                       2 * u * v35 * v7 - u5 * v37 + 2 * u * v5 * v37 -
                       u3 * v57 + 2 * u * v3 * v57 - u * v357,
            .dual1357 = u1357 - u357 * v1 - u157 * v3 + 2 * u57 * v1 * v3 -
                        u57 * v13 - u137 * v5 + 2 * u37 * v1 * v5 +
                        2 * u17 * v3 * v5 - 6 * u7 * v1 * v3 * v5 +
                        2 * u7 * v13 * v5 - u37 * v15 + 2 * u7 * v3 * v15 -
                        u17 * v35 + 2 * u7 * v1 * v35 - u7 * v135 - u135 * v7 +
                        2 * u35 * v1 * v7 + 2 * u15 * v3 * v7 -
                        6 * u5 * v1 * v3 * v7 + 2 * u5 * v13 * v7 +
                        2 * u13 * v5 * v7 - 6 * u3 * v1 * v5 * v7 -
                        6 * u1 * v3 * v5 * v7 + 24 * u * v1 * v3 * v5 * v7 -
                        6 * u * v13 * v5 * v7 + 2 * u3 * v15 * v7 -
                        6 * u * v3 * v15 * v7 + 2 * u1 * v35 * v7 -
                        6 * u * v1 * v35 * v7 + 2 * u * v135 * v7 - u35 * v17 +
                        2 * u5 * v3 * v17 + 2 * u3 * v5 * v17 -
                        6 * u * v3 * v5 * v17 + 2 * u * v35 * v17 - u15 * v37 +
                        2 * u5 * v1 * v37 + 2 * u1 * v5 * v37 -
                        6 * u * v1 * v5 * v37 + 2 * u * v15 * v37 - u5 * v137 +
                        2 * u * v5 * v137 - u13 * v57 + 2 * u3 * v1 * v57 +
                        2 * u1 * v3 * v57 - 6 * u * v1 * v3 * v57 +
                        2 * u * v13 * v57 - u3 * v157 + 2 * u * v3 * v157 -
                        u1 * v357 + 2 * u * v1 * v357 - u * v1357,
            .dual2357 = u2357 - u357 * v2 - u257 * v3 + 2 * u57 * v2 * v3 -
                        u57 * v23 - u237 * v5 + 2 * u37 * v2 * v5 +
                        2 * u27 * v3 * v5 - 6 * u7 * v2 * v3 * v5 +
                        2 * u7 * v23 * v5 - u37 * v25 + 2 * u7 * v3 * v25 -
                        u27 * v35 + 2 * u7 * v2 * v35 - u7 * v235 - u235 * v7 +
                        2 * u35 * v2 * v7 + 2 * u25 * v3 * v7 -
                        6 * u5 * v2 * v3 * v7 + 2 * u5 * v23 * v7 +
                        2 * u23 * v5 * v7 - 6 * u3 * v2 * v5 * v7 -
                        6 * u2 * v3 * v5 * v7 + 24 * u * v2 * v3 * v5 * v7 -
                        6 * u * v23 * v5 * v7 + 2 * u3 * v25 * v7 -
                        6 * u * v3 * v25 * v7 + 2 * u2 * v35 * v7 -
                        6 * u * v2 * v35 * v7 + 2 * u * v235 * v7 - u35 * v27 +
                        2 * u5 * v3 * v27 + 2 * u3 * v5 * v27 -
                        6 * u * v3 * v5 * v27 + 2 * u * v35 * v27 - u25 * v37 +
                        2 * u5 * v2 * v37 + 2 * u2 * v5 * v37 -
                        6 * u * v2 * v5 * v37 + 2 * u * v25 * v37 - u5 * v237 +
                        2 * u * v5 * v237 - u23 * v57 + 2 * u3 * v2 * v57 +
                        2 * u2 * v3 * v57 - 6 * u * v2 * v3 * v57 +
                        2 * u * v23 * v57 - u3 * v257 + 2 * u * v3 * v257 -
                        u2 * v357 + 2 * u * v2 * v357 - u * v2357,
            .dual12357 =
                    u12357 - u2357 * v1 - u1357 * v2 + 2 * u357 * v1 * v2 -
                    u357 * v12 - u1257 * v3 + 2 * u257 * v1 * v3 +
                    2 * u157 * v2 * v3 - 6 * u57 * v1 * v2 * v3 +
                    2 * u57 * v12 * v3 - u257 * v13 + 2 * u57 * v2 * v13 -
                    u157 * v23 + 2 * u57 * v1 * v23 - u57 * v123 - u1237 * v5 +
                    2 * u237 * v1 * v5 + 2 * u137 * v2 * v5 -
                    6 * u37 * v1 * v2 * v5 + 2 * u37 * v12 * v5 +
                    2 * u127 * v3 * v5 - 6 * u27 * v1 * v3 * v5 -
                    6 * u17 * v2 * v3 * v5 + 24 * u7 * v1 * v2 * v3 * v5 -
                    6 * u7 * v12 * v3 * v5 + 2 * u27 * v13 * v5 -
                    6 * u7 * v2 * v13 * v5 + 2 * u17 * v23 * v5 -
                    6 * u7 * v1 * v23 * v5 + 2 * u7 * v123 * v5 - u237 * v15 +
                    2 * u37 * v2 * v15 + 2 * u27 * v3 * v15 -
                    6 * u7 * v2 * v3 * v15 + 2 * u7 * v23 * v15 - u137 * v25 +
                    2 * u37 * v1 * v25 + 2 * u17 * v3 * v25 -
                    6 * u7 * v1 * v3 * v25 + 2 * u7 * v13 * v25 - u37 * v125 +
                    2 * u7 * v3 * v125 - u127 * v35 + 2 * u27 * v1 * v35 +
                    2 * u17 * v2 * v35 - 6 * u7 * v1 * v2 * v35 +
                    2 * u7 * v12 * v35 - u27 * v135 + 2 * u7 * v2 * v135 -
                    u17 * v235 + 2 * u7 * v1 * v235 - u7 * v1235 - u1235 * v7 +
                    2 * u235 * v1 * v7 + 2 * u135 * v2 * v7 -
                    6 * u35 * v1 * v2 * v7 + 2 * u35 * v12 * v7 +
                    2 * u125 * v3 * v7 - 6 * u25 * v1 * v3 * v7 -
                    6 * u15 * v2 * v3 * v7 + 24 * u5 * v1 * v2 * v3 * v7 -
                    6 * u5 * v12 * v3 * v7 + 2 * u25 * v13 * v7 -
                    6 * u5 * v2 * v13 * v7 + 2 * u15 * v23 * v7 -
                    6 * u5 * v1 * v23 * v7 + 2 * u5 * v123 * v7 +
                    2 * u123 * v5 * v7 - 6 * u23 * v1 * v5 * v7 -
                    6 * u13 * v2 * v5 * v7 + 24 * u3 * v1 * v2 * v5 * v7 -
                    6 * u3 * v12 * v5 * v7 - 6 * u12 * v3 * v5 * v7 +
                    24 * u2 * v1 * v3 * v5 * v7 + 24 * u1 * v2 * v3 * v5 * v7 -
                    120 * u * v1 * v2 * v3 * v5 * v7 +
                    24 * u * v12 * v3 * v5 * v7 - 6 * u2 * v13 * v5 * v7 +
                    24 * u * v2 * v13 * v5 * v7 - 6 * u1 * v23 * v5 * v7 +
                    24 * u * v1 * v23 * v5 * v7 - 6 * u * v123 * v5 * v7 +
                    2 * u23 * v15 * v7 - 6 * u3 * v2 * v15 * v7 -
                    6 * u2 * v3 * v15 * v7 + 24 * u * v2 * v3 * v15 * v7 -
                    6 * u * v23 * v15 * v7 + 2 * u13 * v25 * v7 -
                    6 * u3 * v1 * v25 * v7 - 6 * u1 * v3 * v25 * v7 +
                    24 * u * v1 * v3 * v25 * v7 - 6 * u * v13 * v25 * v7 +
                    2 * u3 * v125 * v7 - 6 * u * v3 * v125 * v7 +
                    2 * u12 * v35 * v7 - 6 * u2 * v1 * v35 * v7 -
                    6 * u1 * v2 * v35 * v7 + 24 * u * v1 * v2 * v35 * v7 -
                    6 * u * v12 * v35 * v7 + 2 * u2 * v135 * v7 -
                    6 * u * v2 * v135 * v7 + 2 * u1 * v235 * v7 -
                    6 * u * v1 * v235 * v7 + 2 * u * v1235 * v7 - u235 * v17 +
                    2 * u35 * v2 * v17 + 2 * u25 * v3 * v17 -
                    6 * u5 * v2 * v3 * v17 + 2 * u5 * v23 * v17 +
                    2 * u23 * v5 * v17 - 6 * u3 * v2 * v5 * v17 -
                    6 * u2 * v3 * v5 * v17 + 24 * u * v2 * v3 * v5 * v17 -
                    6 * u * v23 * v5 * v17 + 2 * u3 * v25 * v17 -
                    6 * u * v3 * v25 * v17 + 2 * u2 * v35 * v17 -
                    6 * u * v2 * v35 * v17 + 2 * u * v235 * v17 - u135 * v27 +
                    2 * u35 * v1 * v27 + 2 * u15 * v3 * v27 -
                    6 * u5 * v1 * v3 * v27 + 2 * u5 * v13 * v27 +
                    2 * u13 * v5 * v27 - 6 * u3 * v1 * v5 * v27 -
                    6 * u1 * v3 * v5 * v27 + 24 * u * v1 * v3 * v5 * v27 -
                    6 * u * v13 * v5 * v27 + 2 * u3 * v15 * v27 -
                    6 * u * v3 * v15 * v27 + 2 * u1 * v35 * v27 -
                    6 * u * v1 * v35 * v27 + 2 * u * v135 * v27 - u35 * v127 +
                    2 * u5 * v3 * v127 + 2 * u3 * v5 * v127 -
                    6 * u * v3 * v5 * v127 + 2 * u * v35 * v127 - u125 * v37 +
                    2 * u25 * v1 * v37 + 2 * u15 * v2 * v37 -
                    6 * u5 * v1 * v2 * v37 + 2 * u5 * v12 * v37 +
                    2 * u12 * v5 * v37 - 6 * u2 * v1 * v5 * v37 -
                    6 * u1 * v2 * v5 * v37 + 24 * u * v1 * v2 * v5 * v37 -
                    6 * u * v12 * v5 * v37 + 2 * u2 * v15 * v37 -
                    6 * u * v2 * v15 * v37 + 2 * u1 * v25 * v37 -
                    6 * u * v1 * v25 * v37 + 2 * u * v125 * v37 - u25 * v137 +
                    2 * u5 * v2 * v137 + 2 * u2 * v5 * v137 -
                    6 * u * v2 * v5 * v137 + 2 * u * v25 * v137 - u15 * v237 +
                    2 * u5 * v1 * v237 + 2 * u1 * v5 * v237 -
                    6 * u * v1 * v5 * v237 + 2 * u * v15 * v237 - u5 * v1237 +
                    2 * u * v5 * v1237 - u123 * v57 + 2 * u23 * v1 * v57 +
                    2 * u13 * v2 * v57 - 6 * u3 * v1 * v2 * v57 +
                    2 * u3 * v12 * v57 + 2 * u12 * v3 * v57 -
                    6 * u2 * v1 * v3 * v57 - 6 * u1 * v2 * v3 * v57 +
                    24 * u * v1 * v2 * v3 * v57 - 6 * u * v12 * v3 * v57 +
                    2 * u2 * v13 * v57 - 6 * u * v2 * v13 * v57 +
                    2 * u1 * v23 * v57 - 6 * u * v1 * v23 * v57 +
                    2 * u * v123 * v57 - u23 * v157 + 2 * u3 * v2 * v157 +
                    2 * u2 * v3 * v157 - 6 * u * v2 * v3 * v157 +
                    2 * u * v23 * v157 - u13 * v257 + 2 * u3 * v1 * v257 +
                    2 * u1 * v3 * v257 - 6 * u * v1 * v3 * v257 +
                    2 * u * v13 * v257 - u3 * v1257 + 2 * u * v3 * v1257 -
                    u12 * v357 + 2 * u2 * v1 * v357 + 2 * u1 * v2 * v357 -
                    6 * u * v1 * v2 * v357 + 2 * u * v12 * v357 - u2 * v1357 +
                    2 * u * v2 * v1357 - u1 * v2357 + 2 * u * v1 * v2357 -
                    u * v12357,
            .dual457 = u457 - u57 * v4 - u47 * v5 + 2 * u7 * v4 * v5 -
                       u7 * v45 - u45 * v7 + 2 * u5 * v4 * v7 +
                       2 * u4 * v5 * v7 - 6 * u * v4 * v5 * v7 +
                       2 * u * v45 * v7 - u5 * v47 + 2 * u * v5 * v47 -
                       u4 * v57 + 2 * u * v4 * v57 - u * v457,
            .dual1457 = u1457 - u457 * v1 - u157 * v4 + 2 * u57 * v1 * v4 -
                        u57 * v14 - u147 * v5 + 2 * u47 * v1 * v5 +
                        2 * u17 * v4 * v5 - 6 * u7 * v1 * v4 * v5 +
                        2 * u7 * v14 * v5 - u47 * v15 + 2 * u7 * v4 * v15 -
                        u17 * v45 + 2 * u7 * v1 * v45 - u7 * v145 - u145 * v7 +
                        2 * u45 * v1 * v7 + 2 * u15 * v4 * v7 -
                        6 * u5 * v1 * v4 * v7 + 2 * u5 * v14 * v7 +
                        2 * u14 * v5 * v7 - 6 * u4 * v1 * v5 * v7 -
                        6 * u1 * v4 * v5 * v7 + 24 * u * v1 * v4 * v5 * v7 -
                        6 * u * v14 * v5 * v7 + 2 * u4 * v15 * v7 -
                        6 * u * v4 * v15 * v7 + 2 * u1 * v45 * v7 -
                        6 * u * v1 * v45 * v7 + 2 * u * v145 * v7 - u45 * v17 +
                        2 * u5 * v4 * v17 + 2 * u4 * v5 * v17 -
                        6 * u * v4 * v5 * v17 + 2 * u * v45 * v17 - u15 * v47 +
                        2 * u5 * v1 * v47 + 2 * u1 * v5 * v47 -
                        6 * u * v1 * v5 * v47 + 2 * u * v15 * v47 - u5 * v147 +
                        2 * u * v5 * v147 - u14 * v57 + 2 * u4 * v1 * v57 +
                        2 * u1 * v4 * v57 - 6 * u * v1 * v4 * v57 +
                        2 * u * v14 * v57 - u4 * v157 + 2 * u * v4 * v157 -
                        u1 * v457 + 2 * u * v1 * v457 - u * v1457,
            .dual2457 = u2457 - u457 * v2 - u257 * v4 + 2 * u57 * v2 * v4 -
                        u57 * v24 - u247 * v5 + 2 * u47 * v2 * v5 +
                        2 * u27 * v4 * v5 - 6 * u7 * v2 * v4 * v5 +
                        2 * u7 * v24 * v5 - u47 * v25 + 2 * u7 * v4 * v25 -
                        u27 * v45 + 2 * u7 * v2 * v45 - u7 * v245 - u245 * v7 +
                        2 * u45 * v2 * v7 + 2 * u25 * v4 * v7 -
                        6 * u5 * v2 * v4 * v7 + 2 * u5 * v24 * v7 +
                        2 * u24 * v5 * v7 - 6 * u4 * v2 * v5 * v7 -
                        6 * u2 * v4 * v5 * v7 + 24 * u * v2 * v4 * v5 * v7 -
                        6 * u * v24 * v5 * v7 + 2 * u4 * v25 * v7 -
                        6 * u * v4 * v25 * v7 + 2 * u2 * v45 * v7 -
                        6 * u * v2 * v45 * v7 + 2 * u * v245 * v7 - u45 * v27 +
                        2 * u5 * v4 * v27 + 2 * u4 * v5 * v27 -
                        6 * u * v4 * v5 * v27 + 2 * u * v45 * v27 - u25 * v47 +
                        2 * u5 * v2 * v47 + 2 * u2 * v5 * v47 -
                        6 * u * v2 * v5 * v47 + 2 * u * v25 * v47 - u5 * v247 +
                        2 * u * v5 * v247 - u24 * v57 + 2 * u4 * v2 * v57 +
                        2 * u2 * v4 * v57 - 6 * u * v2 * v4 * v57 +
                        2 * u * v24 * v57 - u4 * v257 + 2 * u * v4 * v257 -
                        u2 * v457 + 2 * u * v2 * v457 - u * v2457,
            .dual12457 =
                    u12457 - u2457 * v1 - u1457 * v2 + 2 * u457 * v1 * v2 -
                    u457 * v12 - u1257 * v4 + 2 * u257 * v1 * v4 +
                    2 * u157 * v2 * v4 - 6 * u57 * v1 * v2 * v4 +
                    2 * u57 * v12 * v4 - u257 * v14 + 2 * u57 * v2 * v14 -
                    u157 * v24 + 2 * u57 * v1 * v24 - u57 * v124 - u1247 * v5 +
                    2 * u247 * v1 * v5 + 2 * u147 * v2 * v5 -
                    6 * u47 * v1 * v2 * v5 + 2 * u47 * v12 * v5 +
                    2 * u127 * v4 * v5 - 6 * u27 * v1 * v4 * v5 -
                    6 * u17 * v2 * v4 * v5 + 24 * u7 * v1 * v2 * v4 * v5 -
                    6 * u7 * v12 * v4 * v5 + 2 * u27 * v14 * v5 -
                    6 * u7 * v2 * v14 * v5 + 2 * u17 * v24 * v5 -
                    6 * u7 * v1 * v24 * v5 + 2 * u7 * v124 * v5 - u247 * v15 +
                    2 * u47 * v2 * v15 + 2 * u27 * v4 * v15 -
                    6 * u7 * v2 * v4 * v15 + 2 * u7 * v24 * v15 - u147 * v25 +
                    2 * u47 * v1 * v25 + 2 * u17 * v4 * v25 -
                    6 * u7 * v1 * v4 * v25 + 2 * u7 * v14 * v25 - u47 * v125 +
                    2 * u7 * v4 * v125 - u127 * v45 + 2 * u27 * v1 * v45 +
                    2 * u17 * v2 * v45 - 6 * u7 * v1 * v2 * v45 +
                    2 * u7 * v12 * v45 - u27 * v145 + 2 * u7 * v2 * v145 -
                    u17 * v245 + 2 * u7 * v1 * v245 - u7 * v1245 - u1245 * v7 +
                    2 * u245 * v1 * v7 + 2 * u145 * v2 * v7 -
                    6 * u45 * v1 * v2 * v7 + 2 * u45 * v12 * v7 +
                    2 * u125 * v4 * v7 - 6 * u25 * v1 * v4 * v7 -
                    6 * u15 * v2 * v4 * v7 + 24 * u5 * v1 * v2 * v4 * v7 -
                    6 * u5 * v12 * v4 * v7 + 2 * u25 * v14 * v7 -
                    6 * u5 * v2 * v14 * v7 + 2 * u15 * v24 * v7 -
                    6 * u5 * v1 * v24 * v7 + 2 * u5 * v124 * v7 +
                    2 * u124 * v5 * v7 - 6 * u24 * v1 * v5 * v7 -
                    6 * u14 * v2 * v5 * v7 + 24 * u4 * v1 * v2 * v5 * v7 -
                    6 * u4 * v12 * v5 * v7 - 6 * u12 * v4 * v5 * v7 +
                    24 * u2 * v1 * v4 * v5 * v7 + 24 * u1 * v2 * v4 * v5 * v7 -
                    120 * u * v1 * v2 * v4 * v5 * v7 +
                    24 * u * v12 * v4 * v5 * v7 - 6 * u2 * v14 * v5 * v7 +
                    24 * u * v2 * v14 * v5 * v7 - 6 * u1 * v24 * v5 * v7 +
                    24 * u * v1 * v24 * v5 * v7 - 6 * u * v124 * v5 * v7 +
                    2 * u24 * v15 * v7 - 6 * u4 * v2 * v15 * v7 -
                    6 * u2 * v4 * v15 * v7 + 24 * u * v2 * v4 * v15 * v7 -
                    6 * u * v24 * v15 * v7 + 2 * u14 * v25 * v7 -
                    6 * u4 * v1 * v25 * v7 - 6 * u1 * v4 * v25 * v7 +
                    24 * u * v1 * v4 * v25 * v7 - 6 * u * v14 * v25 * v7 +
                    2 * u4 * v125 * v7 - 6 * u * v4 * v125 * v7 +
                    2 * u12 * v45 * v7 - 6 * u2 * v1 * v45 * v7 -
                    6 * u1 * v2 * v45 * v7 + 24 * u * v1 * v2 * v45 * v7 -
                    6 * u * v12 * v45 * v7 + 2 * u2 * v145 * v7 -
                    6 * u * v2 * v145 * v7 + 2 * u1 * v245 * v7 -
                    6 * u * v1 * v245 * v7 + 2 * u * v1245 * v7 - u245 * v17 +
                    2 * u45 * v2 * v17 + 2 * u25 * v4 * v17 -
                    6 * u5 * v2 * v4 * v17 + 2 * u5 * v24 * v17 +
                    2 * u24 * v5 * v17 - 6 * u4 * v2 * v5 * v17 -
                    6 * u2 * v4 * v5 * v17 + 24 * u * v2 * v4 * v5 * v17 -
                    6 * u * v24 * v5 * v17 + 2 * u4 * v25 * v17 -
                    6 * u * v4 * v25 * v17 + 2 * u2 * v45 * v17 -
                    6 * u * v2 * v45 * v17 + 2 * u * v245 * v17 - u145 * v27 +
                    2 * u45 * v1 * v27 + 2 * u15 * v4 * v27 -
                    6 * u5 * v1 * v4 * v27 + 2 * u5 * v14 * v27 +
                    2 * u14 * v5 * v27 - 6 * u4 * v1 * v5 * v27 -
                    6 * u1 * v4 * v5 * v27 + 24 * u * v1 * v4 * v5 * v27 -
                    6 * u * v14 * v5 * v27 + 2 * u4 * v15 * v27 -
                    6 * u * v4 * v15 * v27 + 2 * u1 * v45 * v27 -
                    6 * u * v1 * v45 * v27 + 2 * u * v145 * v27 - u45 * v127 +
                    2 * u5 * v4 * v127 + 2 * u4 * v5 * v127 -
                    6 * u * v4 * v5 * v127 + 2 * u * v45 * v127 - u125 * v47 +
                    2 * u25 * v1 * v47 + 2 * u15 * v2 * v47 -
                    6 * u5 * v1 * v2 * v47 + 2 * u5 * v12 * v47 +
                    2 * u12 * v5 * v47 - 6 * u2 * v1 * v5 * v47 -
                    6 * u1 * v2 * v5 * v47 + 24 * u * v1 * v2 * v5 * v47 -
                    6 * u * v12 * v5 * v47 + 2 * u2 * v15 * v47 -
                    6 * u * v2 * v15 * v47 + 2 * u1 * v25 * v47 -
                    6 * u * v1 * v25 * v47 + 2 * u * v125 * v47 - u25 * v147 +
                    2 * u5 * v2 * v147 + 2 * u2 * v5 * v147 -
                    6 * u * v2 * v5 * v147 + 2 * u * v25 * v147 - u15 * v247 +
                    2 * u5 * v1 * v247 + 2 * u1 * v5 * v247 -
                    6 * u * v1 * v5 * v247 + 2 * u * v15 * v247 - u5 * v1247 +
                    2 * u * v5 * v1247 - u124 * v57 + 2 * u24 * v1 * v57 +
                    2 * u14 * v2 * v57 - 6 * u4 * v1 * v2 * v57 +
                    2 * u4 * v12 * v57 + 2 * u12 * v4 * v57 -
                    6 * u2 * v1 * v4 * v57 - 6 * u1 * v2 * v4 * v57 +
                    24 * u * v1 * v2 * v4 * v57 - 6 * u * v12 * v4 * v57 +
                    2 * u2 * v14 * v57 - 6 * u * v2 * v14 * v57 +
                    2 * u1 * v24 * v57 - 6 * u * v1 * v24 * v57 +
                    2 * u * v124 * v57 - u24 * v157 + 2 * u4 * v2 * v157 +
                    2 * u2 * v4 * v157 - 6 * u * v2 * v4 * v157 +
                    2 * u * v24 * v157 - u14 * v257 + 2 * u4 * v1 * v257 +
                    2 * u1 * v4 * v257 - 6 * u * v1 * v4 * v257 +
                    2 * u * v14 * v257 - u4 * v1257 + 2 * u * v4 * v1257 -
                    u12 * v457 + 2 * u2 * v1 * v457 + 2 * u1 * v2 * v457 -
                    6 * u * v1 * v2 * v457 + 2 * u * v12 * v457 - u2 * v1457 +
                    2 * u * v2 * v1457 - u1 * v2457 + 2 * u * v1 * v2457 -
                    u * v12457,
            .dual3457 = u3457 - u457 * v3 - u357 * v4 + 2 * u57 * v3 * v4 -
                        u57 * v34 - u347 * v5 + 2 * u47 * v3 * v5 +
                        2 * u37 * v4 * v5 - 6 * u7 * v3 * v4 * v5 +
                        2 * u7 * v34 * v5 - u47 * v35 + 2 * u7 * v4 * v35 -
                        u37 * v45 + 2 * u7 * v3 * v45 - u7 * v345 - u345 * v7 +
                        2 * u45 * v3 * v7 + 2 * u35 * v4 * v7 -
                        6 * u5 * v3 * v4 * v7 + 2 * u5 * v34 * v7 +
                        2 * u34 * v5 * v7 - 6 * u4 * v3 * v5 * v7 -
                        6 * u3 * v4 * v5 * v7 + 24 * u * v3 * v4 * v5 * v7 -
                        6 * u * v34 * v5 * v7 + 2 * u4 * v35 * v7 -
                        6 * u * v4 * v35 * v7 + 2 * u3 * v45 * v7 -
                        6 * u * v3 * v45 * v7 + 2 * u * v345 * v7 - u45 * v37 +
                        2 * u5 * v4 * v37 + 2 * u4 * v5 * v37 -
                        6 * u * v4 * v5 * v37 + 2 * u * v45 * v37 - u35 * v47 +
                        2 * u5 * v3 * v47 + 2 * u3 * v5 * v47 -
                        6 * u * v3 * v5 * v47 + 2 * u * v35 * v47 - u5 * v347 +
                        2 * u * v5 * v347 - u34 * v57 + 2 * u4 * v3 * v57 +
                        2 * u3 * v4 * v57 - 6 * u * v3 * v4 * v57 +
                        2 * u * v34 * v57 - u4 * v357 + 2 * u * v4 * v357 -
                        u3 * v457 + 2 * u * v3 * v457 - u * v3457,
            .dual13457 =
                    u13457 - u3457 * v1 - u1457 * v3 + 2 * u457 * v1 * v3 -
                    u457 * v13 - u1357 * v4 + 2 * u357 * v1 * v4 +
                    2 * u157 * v3 * v4 - 6 * u57 * v1 * v3 * v4 +
                    2 * u57 * v13 * v4 - u357 * v14 + 2 * u57 * v3 * v14 -
                    u157 * v34 + 2 * u57 * v1 * v34 - u57 * v134 - u1347 * v5 +
                    2 * u347 * v1 * v5 + 2 * u147 * v3 * v5 -
                    6 * u47 * v1 * v3 * v5 + 2 * u47 * v13 * v5 +
                    2 * u137 * v4 * v5 - 6 * u37 * v1 * v4 * v5 -
                    6 * u17 * v3 * v4 * v5 + 24 * u7 * v1 * v3 * v4 * v5 -
                    6 * u7 * v13 * v4 * v5 + 2 * u37 * v14 * v5 -
                    6 * u7 * v3 * v14 * v5 + 2 * u17 * v34 * v5 -
                    6 * u7 * v1 * v34 * v5 + 2 * u7 * v134 * v5 - u347 * v15 +
                    2 * u47 * v3 * v15 + 2 * u37 * v4 * v15 -
                    6 * u7 * v3 * v4 * v15 + 2 * u7 * v34 * v15 - u147 * v35 +
                    2 * u47 * v1 * v35 + 2 * u17 * v4 * v35 -
                    6 * u7 * v1 * v4 * v35 + 2 * u7 * v14 * v35 - u47 * v135 +
                    2 * u7 * v4 * v135 - u137 * v45 + 2 * u37 * v1 * v45 +
                    2 * u17 * v3 * v45 - 6 * u7 * v1 * v3 * v45 +
                    2 * u7 * v13 * v45 - u37 * v145 + 2 * u7 * v3 * v145 -
                    u17 * v345 + 2 * u7 * v1 * v345 - u7 * v1345 - u1345 * v7 +
                    2 * u345 * v1 * v7 + 2 * u145 * v3 * v7 -
                    6 * u45 * v1 * v3 * v7 + 2 * u45 * v13 * v7 +
                    2 * u135 * v4 * v7 - 6 * u35 * v1 * v4 * v7 -
                    6 * u15 * v3 * v4 * v7 + 24 * u5 * v1 * v3 * v4 * v7 -
                    6 * u5 * v13 * v4 * v7 + 2 * u35 * v14 * v7 -
                    6 * u5 * v3 * v14 * v7 + 2 * u15 * v34 * v7 -
                    6 * u5 * v1 * v34 * v7 + 2 * u5 * v134 * v7 +
                    2 * u134 * v5 * v7 - 6 * u34 * v1 * v5 * v7 -
                    6 * u14 * v3 * v5 * v7 + 24 * u4 * v1 * v3 * v5 * v7 -
                    6 * u4 * v13 * v5 * v7 - 6 * u13 * v4 * v5 * v7 +
                    24 * u3 * v1 * v4 * v5 * v7 + 24 * u1 * v3 * v4 * v5 * v7 -
                    120 * u * v1 * v3 * v4 * v5 * v7 +
                    24 * u * v13 * v4 * v5 * v7 - 6 * u3 * v14 * v5 * v7 +
                    24 * u * v3 * v14 * v5 * v7 - 6 * u1 * v34 * v5 * v7 +
                    24 * u * v1 * v34 * v5 * v7 - 6 * u * v134 * v5 * v7 +
                    2 * u34 * v15 * v7 - 6 * u4 * v3 * v15 * v7 -
                    6 * u3 * v4 * v15 * v7 + 24 * u * v3 * v4 * v15 * v7 -
                    6 * u * v34 * v15 * v7 + 2 * u14 * v35 * v7 -
                    6 * u4 * v1 * v35 * v7 - 6 * u1 * v4 * v35 * v7 +
                    24 * u * v1 * v4 * v35 * v7 - 6 * u * v14 * v35 * v7 +
                    2 * u4 * v135 * v7 - 6 * u * v4 * v135 * v7 +
                    2 * u13 * v45 * v7 - 6 * u3 * v1 * v45 * v7 -
                    6 * u1 * v3 * v45 * v7 + 24 * u * v1 * v3 * v45 * v7 -
                    6 * u * v13 * v45 * v7 + 2 * u3 * v145 * v7 -
                    6 * u * v3 * v145 * v7 + 2 * u1 * v345 * v7 -
                    6 * u * v1 * v345 * v7 + 2 * u * v1345 * v7 - u345 * v17 +
                    2 * u45 * v3 * v17 + 2 * u35 * v4 * v17 -
                    6 * u5 * v3 * v4 * v17 + 2 * u5 * v34 * v17 +
                    2 * u34 * v5 * v17 - 6 * u4 * v3 * v5 * v17 -
                    6 * u3 * v4 * v5 * v17 + 24 * u * v3 * v4 * v5 * v17 -
                    6 * u * v34 * v5 * v17 + 2 * u4 * v35 * v17 -
                    6 * u * v4 * v35 * v17 + 2 * u3 * v45 * v17 -
                    6 * u * v3 * v45 * v17 + 2 * u * v345 * v17 - u145 * v37 +
                    2 * u45 * v1 * v37 + 2 * u15 * v4 * v37 -
                    6 * u5 * v1 * v4 * v37 + 2 * u5 * v14 * v37 +
                    2 * u14 * v5 * v37 - 6 * u4 * v1 * v5 * v37 -
                    6 * u1 * v4 * v5 * v37 + 24 * u * v1 * v4 * v5 * v37 -
                    6 * u * v14 * v5 * v37 + 2 * u4 * v15 * v37 -
                    6 * u * v4 * v15 * v37 + 2 * u1 * v45 * v37 -
                    6 * u * v1 * v45 * v37 + 2 * u * v145 * v37 - u45 * v137 +
                    2 * u5 * v4 * v137 + 2 * u4 * v5 * v137 -
                    6 * u * v4 * v5 * v137 + 2 * u * v45 * v137 - u135 * v47 +
                    2 * u35 * v1 * v47 + 2 * u15 * v3 * v47 -
                    6 * u5 * v1 * v3 * v47 + 2 * u5 * v13 * v47 +
                    2 * u13 * v5 * v47 - 6 * u3 * v1 * v5 * v47 -
                    6 * u1 * v3 * v5 * v47 + 24 * u * v1 * v3 * v5 * v47 -
                    6 * u * v13 * v5 * v47 + 2 * u3 * v15 * v47 -
                    6 * u * v3 * v15 * v47 + 2 * u1 * v35 * v47 -
                    6 * u * v1 * v35 * v47 + 2 * u * v135 * v47 - u35 * v147 +
                    2 * u5 * v3 * v147 + 2 * u3 * v5 * v147 -
                    6 * u * v3 * v5 * v147 + 2 * u * v35 * v147 - u15 * v347 +
                    2 * u5 * v1 * v347 + 2 * u1 * v5 * v347 -
                    6 * u * v1 * v5 * v347 + 2 * u * v15 * v347 - u5 * v1347 +
                    2 * u * v5 * v1347 - u134 * v57 + 2 * u34 * v1 * v57 +
                    2 * u14 * v3 * v57 - 6 * u4 * v1 * v3 * v57 +
                    2 * u4 * v13 * v57 + 2 * u13 * v4 * v57 -
                    6 * u3 * v1 * v4 * v57 - 6 * u1 * v3 * v4 * v57 +
                    24 * u * v1 * v3 * v4 * v57 - 6 * u * v13 * v4 * v57 +
                    2 * u3 * v14 * v57 - 6 * u * v3 * v14 * v57 +
                    2 * u1 * v34 * v57 - 6 * u * v1 * v34 * v57 +
                    2 * u * v134 * v57 - u34 * v157 + 2 * u4 * v3 * v157 +
                    2 * u3 * v4 * v157 - 6 * u * v3 * v4 * v157 +
                    2 * u * v34 * v157 - u14 * v357 + 2 * u4 * v1 * v357 +
                    2 * u1 * v4 * v357 - 6 * u * v1 * v4 * v357 +
                    2 * u * v14 * v357 - u4 * v1357 + 2 * u * v4 * v1357 -
                    u13 * v457 + 2 * u3 * v1 * v457 + 2 * u1 * v3 * v457 -
                    6 * u * v1 * v3 * v457 + 2 * u * v13 * v457 - u3 * v1457 +
                    2 * u * v3 * v1457 - u1 * v3457 + 2 * u * v1 * v3457 -
                    u * v13457,
            .dual23457 =
                    u23457 - u3457 * v2 - u2457 * v3 + 2 * u457 * v2 * v3 -
                    u457 * v23 - u2357 * v4 + 2 * u357 * v2 * v4 +
                    2 * u257 * v3 * v4 - 6 * u57 * v2 * v3 * v4 +
                    2 * u57 * v23 * v4 - u357 * v24 + 2 * u57 * v3 * v24 -
                    u257 * v34 + 2 * u57 * v2 * v34 - u57 * v234 - u2347 * v5 +
                    2 * u347 * v2 * v5 + 2 * u247 * v3 * v5 -
                    6 * u47 * v2 * v3 * v5 + 2 * u47 * v23 * v5 +
                    2 * u237 * v4 * v5 - 6 * u37 * v2 * v4 * v5 -
                    6 * u27 * v3 * v4 * v5 + 24 * u7 * v2 * v3 * v4 * v5 -
                    6 * u7 * v23 * v4 * v5 + 2 * u37 * v24 * v5 -
                    6 * u7 * v3 * v24 * v5 + 2 * u27 * v34 * v5 -
                    6 * u7 * v2 * v34 * v5 + 2 * u7 * v234 * v5 - u347 * v25 +
                    2 * u47 * v3 * v25 + 2 * u37 * v4 * v25 -
                    6 * u7 * v3 * v4 * v25 + 2 * u7 * v34 * v25 - u247 * v35 +
                    2 * u47 * v2 * v35 + 2 * u27 * v4 * v35 -
                    6 * u7 * v2 * v4 * v35 + 2 * u7 * v24 * v35 - u47 * v235 +
                    2 * u7 * v4 * v235 - u237 * v45 + 2 * u37 * v2 * v45 +
                    2 * u27 * v3 * v45 - 6 * u7 * v2 * v3 * v45 +
                    2 * u7 * v23 * v45 - u37 * v245 + 2 * u7 * v3 * v245 -
                    u27 * v345 + 2 * u7 * v2 * v345 - u7 * v2345 - u2345 * v7 +
                    2 * u345 * v2 * v7 + 2 * u245 * v3 * v7 -
                    6 * u45 * v2 * v3 * v7 + 2 * u45 * v23 * v7 +
                    2 * u235 * v4 * v7 - 6 * u35 * v2 * v4 * v7 -
                    6 * u25 * v3 * v4 * v7 + 24 * u5 * v2 * v3 * v4 * v7 -
                    6 * u5 * v23 * v4 * v7 + 2 * u35 * v24 * v7 -
                    6 * u5 * v3 * v24 * v7 + 2 * u25 * v34 * v7 -
                    6 * u5 * v2 * v34 * v7 + 2 * u5 * v234 * v7 +
                    2 * u234 * v5 * v7 - 6 * u34 * v2 * v5 * v7 -
                    6 * u24 * v3 * v5 * v7 + 24 * u4 * v2 * v3 * v5 * v7 -
                    6 * u4 * v23 * v5 * v7 - 6 * u23 * v4 * v5 * v7 +
                    24 * u3 * v2 * v4 * v5 * v7 + 24 * u2 * v3 * v4 * v5 * v7 -
                    120 * u * v2 * v3 * v4 * v5 * v7 +
                    24 * u * v23 * v4 * v5 * v7 - 6 * u3 * v24 * v5 * v7 +
                    24 * u * v3 * v24 * v5 * v7 - 6 * u2 * v34 * v5 * v7 +
                    24 * u * v2 * v34 * v5 * v7 - 6 * u * v234 * v5 * v7 +
                    2 * u34 * v25 * v7 - 6 * u4 * v3 * v25 * v7 -
                    6 * u3 * v4 * v25 * v7 + 24 * u * v3 * v4 * v25 * v7 -
                    6 * u * v34 * v25 * v7 + 2 * u24 * v35 * v7 -
                    6 * u4 * v2 * v35 * v7 - 6 * u2 * v4 * v35 * v7 +
                    24 * u * v2 * v4 * v35 * v7 - 6 * u * v24 * v35 * v7 +
                    2 * u4 * v235 * v7 - 6 * u * v4 * v235 * v7 +
                    2 * u23 * v45 * v7 - 6 * u3 * v2 * v45 * v7 -
                    6 * u2 * v3 * v45 * v7 + 24 * u * v2 * v3 * v45 * v7 -
                    6 * u * v23 * v45 * v7 + 2 * u3 * v245 * v7 -
                    6 * u * v3 * v245 * v7 + 2 * u2 * v345 * v7 -
                    6 * u * v2 * v345 * v7 + 2 * u * v2345 * v7 - u345 * v27 +
                    2 * u45 * v3 * v27 + 2 * u35 * v4 * v27 -
                    6 * u5 * v3 * v4 * v27 + 2 * u5 * v34 * v27 +
                    2 * u34 * v5 * v27 - 6 * u4 * v3 * v5 * v27 -
                    6 * u3 * v4 * v5 * v27 + 24 * u * v3 * v4 * v5 * v27 -
                    6 * u * v34 * v5 * v27 + 2 * u4 * v35 * v27 -
                    6 * u * v4 * v35 * v27 + 2 * u3 * v45 * v27 -
                    6 * u * v3 * v45 * v27 + 2 * u * v345 * v27 - u245 * v37 +
                    2 * u45 * v2 * v37 + 2 * u25 * v4 * v37 -
                    6 * u5 * v2 * v4 * v37 + 2 * u5 * v24 * v37 +
                    2 * u24 * v5 * v37 - 6 * u4 * v2 * v5 * v37 -
                    6 * u2 * v4 * v5 * v37 + 24 * u * v2 * v4 * v5 * v37 -
                    6 * u * v24 * v5 * v37 + 2 * u4 * v25 * v37 -
                    6 * u * v4 * v25 * v37 + 2 * u2 * v45 * v37 -
                    6 * u * v2 * v45 * v37 + 2 * u * v245 * v37 - u45 * v237 +
                    2 * u5 * v4 * v237 + 2 * u4 * v5 * v237 -
                    6 * u * v4 * v5 * v237 + 2 * u * v45 * v237 - u235 * v47 +
                    2 * u35 * v2 * v47 + 2 * u25 * v3 * v47 -
                    6 * u5 * v2 * v3 * v47 + 2 * u5 * v23 * v47 +
                    2 * u23 * v5 * v47 - 6 * u3 * v2 * v5 * v47 -
                    6 * u2 * v3 * v5 * v47 + 24 * u * v2 * v3 * v5 * v47 -
                    6 * u * v23 * v5 * v47 + 2 * u3 * v25 * v47 -
                    6 * u * v3 * v25 * v47 + 2 * u2 * v35 * v47 -
                    6 * u * v2 * v35 * v47 + 2 * u * v235 * v47 - u35 * v247 +
                    2 * u5 * v3 * v247 + 2 * u3 * v5 * v247 -
                    6 * u * v3 * v5 * v247 + 2 * u * v35 * v247 - u25 * v347 +
                    2 * u5 * v2 * v347 + 2 * u2 * v5 * v347 -
                    6 * u * v2 * v5 * v347 + 2 * u * v25 * v347 - u5 * v2347 +
                    2 * u * v5 * v2347 - u234 * v57 + 2 * u34 * v2 * v57 +
                    2 * u24 * v3 * v57 - 6 * u4 * v2 * v3 * v57 +
                    2 * u4 * v23 * v57 + 2 * u23 * v4 * v57 -
                    6 * u3 * v2 * v4 * v57 - 6 * u2 * v3 * v4 * v57 +
                    24 * u * v2 * v3 * v4 * v57 - 6 * u * v23 * v4 * v57 +
                    2 * u3 * v24 * v57 - 6 * u * v3 * v24 * v57 +
                    2 * u2 * v34 * v57 - 6 * u * v2 * v34 * v57 +
                    2 * u * v234 * v57 - u34 * v257 + 2 * u4 * v3 * v257 +
                    2 * u3 * v4 * v257 - 6 * u * v3 * v4 * v257 +
                    2 * u * v34 * v257 - u24 * v357 + 2 * u4 * v2 * v357 +
                    2 * u2 * v4 * v357 - 6 * u * v2 * v4 * v357 +
                    2 * u * v24 * v357 - u4 * v2357 + 2 * u * v4 * v2357 -
                    u23 * v457 + 2 * u3 * v2 * v457 + 2 * u2 * v3 * v457 -
                    6 * u * v2 * v3 * v457 + 2 * u * v23 * v457 - u3 * v2457 +
                    2 * u * v3 * v2457 - u2 * v3457 + 2 * u * v2 * v3457 -
                    u * v23457,
            .dual123457 =
                    u123457 - u23457 * v1 - u13457 * v2 + 2 * u3457 * v1 * v2 -
                    u3457 * v12 - u12457 * v3 + 2 * u2457 * v1 * v3 +
                    2 * u1457 * v2 * v3 - 6 * u457 * v1 * v2 * v3 +
                    2 * u457 * v12 * v3 - u2457 * v13 + 2 * u457 * v2 * v13 -
                    u1457 * v23 + 2 * u457 * v1 * v23 - u457 * v123 -
                    u12357 * v4 + 2 * u2357 * v1 * v4 + 2 * u1357 * v2 * v4 -
                    6 * u357 * v1 * v2 * v4 + 2 * u357 * v12 * v4 +
                    2 * u1257 * v3 * v4 - 6 * u257 * v1 * v3 * v4 -
                    6 * u157 * v2 * v3 * v4 + 24 * u57 * v1 * v2 * v3 * v4 -
                    6 * u57 * v12 * v3 * v4 + 2 * u257 * v13 * v4 -
                    6 * u57 * v2 * v13 * v4 + 2 * u157 * v23 * v4 -
                    6 * u57 * v1 * v23 * v4 + 2 * u57 * v123 * v4 -
                    u2357 * v14 + 2 * u357 * v2 * v14 + 2 * u257 * v3 * v14 -
                    6 * u57 * v2 * v3 * v14 + 2 * u57 * v23 * v14 -
                    u1357 * v24 + 2 * u357 * v1 * v24 + 2 * u157 * v3 * v24 -
                    6 * u57 * v1 * v3 * v24 + 2 * u57 * v13 * v24 -
                    u357 * v124 + 2 * u57 * v3 * v124 - u1257 * v34 +
                    2 * u257 * v1 * v34 + 2 * u157 * v2 * v34 -
                    6 * u57 * v1 * v2 * v34 + 2 * u57 * v12 * v34 -
                    u257 * v134 + 2 * u57 * v2 * v134 - u157 * v234 +
                    2 * u57 * v1 * v234 - u57 * v1234 - u12347 * v5 +
                    2 * u2347 * v1 * v5 + 2 * u1347 * v2 * v5 -
                    6 * u347 * v1 * v2 * v5 + 2 * u347 * v12 * v5 +
                    2 * u1247 * v3 * v5 - 6 * u247 * v1 * v3 * v5 -
                    6 * u147 * v2 * v3 * v5 + 24 * u47 * v1 * v2 * v3 * v5 -
                    6 * u47 * v12 * v3 * v5 + 2 * u247 * v13 * v5 -
                    6 * u47 * v2 * v13 * v5 + 2 * u147 * v23 * v5 -
                    6 * u47 * v1 * v23 * v5 + 2 * u47 * v123 * v5 +
                    2 * u1237 * v4 * v5 - 6 * u237 * v1 * v4 * v5 -
                    6 * u137 * v2 * v4 * v5 + 24 * u37 * v1 * v2 * v4 * v5 -
                    6 * u37 * v12 * v4 * v5 - 6 * u127 * v3 * v4 * v5 +
                    24 * u27 * v1 * v3 * v4 * v5 +
                    24 * u17 * v2 * v3 * v4 * v5 -
                    120 * u7 * v1 * v2 * v3 * v4 * v5 +
                    24 * u7 * v12 * v3 * v4 * v5 - 6 * u27 * v13 * v4 * v5 +
                    24 * u7 * v2 * v13 * v4 * v5 - 6 * u17 * v23 * v4 * v5 +
                    24 * u7 * v1 * v23 * v4 * v5 - 6 * u7 * v123 * v4 * v5 +
                    2 * u237 * v14 * v5 - 6 * u37 * v2 * v14 * v5 -
                    6 * u27 * v3 * v14 * v5 + 24 * u7 * v2 * v3 * v14 * v5 -
                    6 * u7 * v23 * v14 * v5 + 2 * u137 * v24 * v5 -
                    6 * u37 * v1 * v24 * v5 - 6 * u17 * v3 * v24 * v5 +
                    24 * u7 * v1 * v3 * v24 * v5 - 6 * u7 * v13 * v24 * v5 +
                    2 * u37 * v124 * v5 - 6 * u7 * v3 * v124 * v5 +
                    2 * u127 * v34 * v5 - 6 * u27 * v1 * v34 * v5 -
                    6 * u17 * v2 * v34 * v5 + 24 * u7 * v1 * v2 * v34 * v5 -
                    6 * u7 * v12 * v34 * v5 + 2 * u27 * v134 * v5 -
                    6 * u7 * v2 * v134 * v5 + 2 * u17 * v234 * v5 -
                    6 * u7 * v1 * v234 * v5 + 2 * u7 * v1234 * v5 -
                    u2347 * v15 + 2 * u347 * v2 * v15 + 2 * u247 * v3 * v15 -
                    6 * u47 * v2 * v3 * v15 + 2 * u47 * v23 * v15 +
                    2 * u237 * v4 * v15 - 6 * u37 * v2 * v4 * v15 -
                    6 * u27 * v3 * v4 * v15 + 24 * u7 * v2 * v3 * v4 * v15 -
                    6 * u7 * v23 * v4 * v15 + 2 * u37 * v24 * v15 -
                    6 * u7 * v3 * v24 * v15 + 2 * u27 * v34 * v15 -
                    6 * u7 * v2 * v34 * v15 + 2 * u7 * v234 * v15 -
                    u1347 * v25 + 2 * u347 * v1 * v25 + 2 * u147 * v3 * v25 -
                    6 * u47 * v1 * v3 * v25 + 2 * u47 * v13 * v25 +
                    2 * u137 * v4 * v25 - 6 * u37 * v1 * v4 * v25 -
                    6 * u17 * v3 * v4 * v25 + 24 * u7 * v1 * v3 * v4 * v25 -
                    6 * u7 * v13 * v4 * v25 + 2 * u37 * v14 * v25 -
                    6 * u7 * v3 * v14 * v25 + 2 * u17 * v34 * v25 -
                    6 * u7 * v1 * v34 * v25 + 2 * u7 * v134 * v25 -
                    u347 * v125 + 2 * u47 * v3 * v125 + 2 * u37 * v4 * v125 -
                    6 * u7 * v3 * v4 * v125 + 2 * u7 * v34 * v125 -
                    u1247 * v35 + 2 * u247 * v1 * v35 + 2 * u147 * v2 * v35 -
                    6 * u47 * v1 * v2 * v35 + 2 * u47 * v12 * v35 +
                    2 * u127 * v4 * v35 - 6 * u27 * v1 * v4 * v35 -
                    6 * u17 * v2 * v4 * v35 + 24 * u7 * v1 * v2 * v4 * v35 -
                    6 * u7 * v12 * v4 * v35 + 2 * u27 * v14 * v35 -
                    6 * u7 * v2 * v14 * v35 + 2 * u17 * v24 * v35 -
                    6 * u7 * v1 * v24 * v35 + 2 * u7 * v124 * v35 -
                    u247 * v135 + 2 * u47 * v2 * v135 + 2 * u27 * v4 * v135 -
                    6 * u7 * v2 * v4 * v135 + 2 * u7 * v24 * v135 -
                    u147 * v235 + 2 * u47 * v1 * v235 + 2 * u17 * v4 * v235 -
                    6 * u7 * v1 * v4 * v235 + 2 * u7 * v14 * v235 -
                    u47 * v1235 + 2 * u7 * v4 * v1235 - u1237 * v45 +
                    2 * u237 * v1 * v45 + 2 * u137 * v2 * v45 -
                    6 * u37 * v1 * v2 * v45 + 2 * u37 * v12 * v45 +
                    2 * u127 * v3 * v45 - 6 * u27 * v1 * v3 * v45 -
                    6 * u17 * v2 * v3 * v45 + 24 * u7 * v1 * v2 * v3 * v45 -
                    6 * u7 * v12 * v3 * v45 + 2 * u27 * v13 * v45 -
                    6 * u7 * v2 * v13 * v45 + 2 * u17 * v23 * v45 -
                    6 * u7 * v1 * v23 * v45 + 2 * u7 * v123 * v45 -
                    u237 * v145 + 2 * u37 * v2 * v145 + 2 * u27 * v3 * v145 -
                    6 * u7 * v2 * v3 * v145 + 2 * u7 * v23 * v145 -
                    u137 * v245 + 2 * u37 * v1 * v245 + 2 * u17 * v3 * v245 -
                    6 * u7 * v1 * v3 * v245 + 2 * u7 * v13 * v245 -
                    u37 * v1245 + 2 * u7 * v3 * v1245 - u127 * v345 +
                    2 * u27 * v1 * v345 + 2 * u17 * v2 * v345 -
                    6 * u7 * v1 * v2 * v345 + 2 * u7 * v12 * v345 -
                    u27 * v1345 + 2 * u7 * v2 * v1345 - u17 * v2345 +
                    2 * u7 * v1 * v2345 - u7 * v12345 - u12345 * v7 +
                    2 * u2345 * v1 * v7 + 2 * u1345 * v2 * v7 -
                    6 * u345 * v1 * v2 * v7 + 2 * u345 * v12 * v7 +
                    2 * u1245 * v3 * v7 - 6 * u245 * v1 * v3 * v7 -
                    6 * u145 * v2 * v3 * v7 + 24 * u45 * v1 * v2 * v3 * v7 -
                    6 * u45 * v12 * v3 * v7 + 2 * u245 * v13 * v7 -
                    6 * u45 * v2 * v13 * v7 + 2 * u145 * v23 * v7 -
                    6 * u45 * v1 * v23 * v7 + 2 * u45 * v123 * v7 +
                    2 * u1235 * v4 * v7 - 6 * u235 * v1 * v4 * v7 -
                    6 * u135 * v2 * v4 * v7 + 24 * u35 * v1 * v2 * v4 * v7 -
                    6 * u35 * v12 * v4 * v7 - 6 * u125 * v3 * v4 * v7 +
                    24 * u25 * v1 * v3 * v4 * v7 +
                    24 * u15 * v2 * v3 * v4 * v7 -
                    120 * u5 * v1 * v2 * v3 * v4 * v7 +
                    24 * u5 * v12 * v3 * v4 * v7 - 6 * u25 * v13 * v4 * v7 +
                    24 * u5 * v2 * v13 * v4 * v7 - 6 * u15 * v23 * v4 * v7 +
                    24 * u5 * v1 * v23 * v4 * v7 - 6 * u5 * v123 * v4 * v7 +
                    2 * u235 * v14 * v7 - 6 * u35 * v2 * v14 * v7 -
                    6 * u25 * v3 * v14 * v7 + 24 * u5 * v2 * v3 * v14 * v7 -
                    6 * u5 * v23 * v14 * v7 + 2 * u135 * v24 * v7 -
                    6 * u35 * v1 * v24 * v7 - 6 * u15 * v3 * v24 * v7 +
                    24 * u5 * v1 * v3 * v24 * v7 - 6 * u5 * v13 * v24 * v7 +
                    2 * u35 * v124 * v7 - 6 * u5 * v3 * v124 * v7 +
                    2 * u125 * v34 * v7 - 6 * u25 * v1 * v34 * v7 -
                    6 * u15 * v2 * v34 * v7 + 24 * u5 * v1 * v2 * v34 * v7 -
                    6 * u5 * v12 * v34 * v7 + 2 * u25 * v134 * v7 -
                    6 * u5 * v2 * v134 * v7 + 2 * u15 * v234 * v7 -
                    6 * u5 * v1 * v234 * v7 + 2 * u5 * v1234 * v7 +
                    2 * u1234 * v5 * v7 - 6 * u234 * v1 * v5 * v7 -
                    6 * u134 * v2 * v5 * v7 + 24 * u34 * v1 * v2 * v5 * v7 -
                    6 * u34 * v12 * v5 * v7 - 6 * u124 * v3 * v5 * v7 +
                    24 * u24 * v1 * v3 * v5 * v7 +
                    24 * u14 * v2 * v3 * v5 * v7 -
                    120 * u4 * v1 * v2 * v3 * v5 * v7 +
                    24 * u4 * v12 * v3 * v5 * v7 - 6 * u24 * v13 * v5 * v7 +
                    24 * u4 * v2 * v13 * v5 * v7 - 6 * u14 * v23 * v5 * v7 +
                    24 * u4 * v1 * v23 * v5 * v7 - 6 * u4 * v123 * v5 * v7 -
                    6 * u123 * v4 * v5 * v7 + 24 * u23 * v1 * v4 * v5 * v7 +
                    24 * u13 * v2 * v4 * v5 * v7 -
                    120 * u3 * v1 * v2 * v4 * v5 * v7 +
                    24 * u3 * v12 * v4 * v5 * v7 +
                    24 * u12 * v3 * v4 * v5 * v7 -
                    120 * u2 * v1 * v3 * v4 * v5 * v7 -
                    120 * u1 * v2 * v3 * v4 * v5 * v7 +
                    720 * u * v1 * v2 * v3 * v4 * v5 * v7 -
                    120 * u * v12 * v3 * v4 * v5 * v7 +
                    24 * u2 * v13 * v4 * v5 * v7 -
                    120 * u * v2 * v13 * v4 * v5 * v7 +
                    24 * u1 * v23 * v4 * v5 * v7 -
                    120 * u * v1 * v23 * v4 * v5 * v7 +
                    24 * u * v123 * v4 * v5 * v7 - 6 * u23 * v14 * v5 * v7 +
                    24 * u3 * v2 * v14 * v5 * v7 +
                    24 * u2 * v3 * v14 * v5 * v7 -
                    120 * u * v2 * v3 * v14 * v5 * v7 +
                    24 * u * v23 * v14 * v5 * v7 - 6 * u13 * v24 * v5 * v7 +
                    24 * u3 * v1 * v24 * v5 * v7 +
                    24 * u1 * v3 * v24 * v5 * v7 -
                    120 * u * v1 * v3 * v24 * v5 * v7 +
                    24 * u * v13 * v24 * v5 * v7 - 6 * u3 * v124 * v5 * v7 +
                    24 * u * v3 * v124 * v5 * v7 - 6 * u12 * v34 * v5 * v7 +
                    24 * u2 * v1 * v34 * v5 * v7 +
                    24 * u1 * v2 * v34 * v5 * v7 -
                    120 * u * v1 * v2 * v34 * v5 * v7 +
                    24 * u * v12 * v34 * v5 * v7 - 6 * u2 * v134 * v5 * v7 +
                    24 * u * v2 * v134 * v5 * v7 - 6 * u1 * v234 * v5 * v7 +
                    24 * u * v1 * v234 * v5 * v7 - 6 * u * v1234 * v5 * v7 +
                    2 * u234 * v15 * v7 - 6 * u34 * v2 * v15 * v7 -
                    6 * u24 * v3 * v15 * v7 + 24 * u4 * v2 * v3 * v15 * v7 -
                    6 * u4 * v23 * v15 * v7 - 6 * u23 * v4 * v15 * v7 +
                    24 * u3 * v2 * v4 * v15 * v7 +
                    24 * u2 * v3 * v4 * v15 * v7 -
                    120 * u * v2 * v3 * v4 * v15 * v7 +
                    24 * u * v23 * v4 * v15 * v7 - 6 * u3 * v24 * v15 * v7 +
                    24 * u * v3 * v24 * v15 * v7 - 6 * u2 * v34 * v15 * v7 +
                    24 * u * v2 * v34 * v15 * v7 - 6 * u * v234 * v15 * v7 +
                    2 * u134 * v25 * v7 - 6 * u34 * v1 * v25 * v7 -
                    6 * u14 * v3 * v25 * v7 + 24 * u4 * v1 * v3 * v25 * v7 -
                    6 * u4 * v13 * v25 * v7 - 6 * u13 * v4 * v25 * v7 +
                    24 * u3 * v1 * v4 * v25 * v7 +
                    24 * u1 * v3 * v4 * v25 * v7 -
                    120 * u * v1 * v3 * v4 * v25 * v7 +
                    24 * u * v13 * v4 * v25 * v7 - 6 * u3 * v14 * v25 * v7 +
                    24 * u * v3 * v14 * v25 * v7 - 6 * u1 * v34 * v25 * v7 +
                    24 * u * v1 * v34 * v25 * v7 - 6 * u * v134 * v25 * v7 +
                    2 * u34 * v125 * v7 - 6 * u4 * v3 * v125 * v7 -
                    6 * u3 * v4 * v125 * v7 + 24 * u * v3 * v4 * v125 * v7 -
                    6 * u * v34 * v125 * v7 + 2 * u124 * v35 * v7 -
                    6 * u24 * v1 * v35 * v7 - 6 * u14 * v2 * v35 * v7 +
                    24 * u4 * v1 * v2 * v35 * v7 - 6 * u4 * v12 * v35 * v7 -
                    6 * u12 * v4 * v35 * v7 + 24 * u2 * v1 * v4 * v35 * v7 +
                    24 * u1 * v2 * v4 * v35 * v7 -
                    120 * u * v1 * v2 * v4 * v35 * v7 +
                    24 * u * v12 * v4 * v35 * v7 - 6 * u2 * v14 * v35 * v7 +
                    24 * u * v2 * v14 * v35 * v7 - 6 * u1 * v24 * v35 * v7 +
                    24 * u * v1 * v24 * v35 * v7 - 6 * u * v124 * v35 * v7 +
                    2 * u24 * v135 * v7 - 6 * u4 * v2 * v135 * v7 -
                    6 * u2 * v4 * v135 * v7 + 24 * u * v2 * v4 * v135 * v7 -
                    6 * u * v24 * v135 * v7 + 2 * u14 * v235 * v7 -
                    6 * u4 * v1 * v235 * v7 - 6 * u1 * v4 * v235 * v7 +
                    24 * u * v1 * v4 * v235 * v7 - 6 * u * v14 * v235 * v7 +
                    2 * u4 * v1235 * v7 - 6 * u * v4 * v1235 * v7 +
                    2 * u123 * v45 * v7 - 6 * u23 * v1 * v45 * v7 -
                    6 * u13 * v2 * v45 * v7 + 24 * u3 * v1 * v2 * v45 * v7 -
                    6 * u3 * v12 * v45 * v7 - 6 * u12 * v3 * v45 * v7 +
                    24 * u2 * v1 * v3 * v45 * v7 +
                    24 * u1 * v2 * v3 * v45 * v7 -
                    120 * u * v1 * v2 * v3 * v45 * v7 +
                    24 * u * v12 * v3 * v45 * v7 - 6 * u2 * v13 * v45 * v7 +
                    24 * u * v2 * v13 * v45 * v7 - 6 * u1 * v23 * v45 * v7 +
                    24 * u * v1 * v23 * v45 * v7 - 6 * u * v123 * v45 * v7 +
                    2 * u23 * v145 * v7 - 6 * u3 * v2 * v145 * v7 -
                    6 * u2 * v3 * v145 * v7 + 24 * u * v2 * v3 * v145 * v7 -
                    6 * u * v23 * v145 * v7 + 2 * u13 * v245 * v7 -
                    6 * u3 * v1 * v245 * v7 - 6 * u1 * v3 * v245 * v7 +
                    24 * u * v1 * v3 * v245 * v7 - 6 * u * v13 * v245 * v7 +
                    2 * u3 * v1245 * v7 - 6 * u * v3 * v1245 * v7 +
                    2 * u12 * v345 * v7 - 6 * u2 * v1 * v345 * v7 -
                    6 * u1 * v2 * v345 * v7 + 24 * u * v1 * v2 * v345 * v7 -
                    6 * u * v12 * v345 * v7 + 2 * u2 * v1345 * v7 -
                    6 * u * v2 * v1345 * v7 + 2 * u1 * v2345 * v7 -
                    6 * u * v1 * v2345 * v7 + 2 * u * v12345 * v7 -
                    u2345 * v17 + 2 * u345 * v2 * v17 + 2 * u245 * v3 * v17 -
                    6 * u45 * v2 * v3 * v17 + 2 * u45 * v23 * v17 +
                    2 * u235 * v4 * v17 - 6 * u35 * v2 * v4 * v17 -
                    6 * u25 * v3 * v4 * v17 + 24 * u5 * v2 * v3 * v4 * v17 -
                    6 * u5 * v23 * v4 * v17 + 2 * u35 * v24 * v17 -
                    6 * u5 * v3 * v24 * v17 + 2 * u25 * v34 * v17 -
                    6 * u5 * v2 * v34 * v17 + 2 * u5 * v234 * v17 +
                    2 * u234 * v5 * v17 - 6 * u34 * v2 * v5 * v17 -
                    6 * u24 * v3 * v5 * v17 + 24 * u4 * v2 * v3 * v5 * v17 -
                    6 * u4 * v23 * v5 * v17 - 6 * u23 * v4 * v5 * v17 +
                    24 * u3 * v2 * v4 * v5 * v17 +
                    24 * u2 * v3 * v4 * v5 * v17 -
                    120 * u * v2 * v3 * v4 * v5 * v17 +
                    24 * u * v23 * v4 * v5 * v17 - 6 * u3 * v24 * v5 * v17 +
                    24 * u * v3 * v24 * v5 * v17 - 6 * u2 * v34 * v5 * v17 +
                    24 * u * v2 * v34 * v5 * v17 - 6 * u * v234 * v5 * v17 +
                    2 * u34 * v25 * v17 - 6 * u4 * v3 * v25 * v17 -
                    6 * u3 * v4 * v25 * v17 + 24 * u * v3 * v4 * v25 * v17 -
                    6 * u * v34 * v25 * v17 + 2 * u24 * v35 * v17 -
                    6 * u4 * v2 * v35 * v17 - 6 * u2 * v4 * v35 * v17 +
                    24 * u * v2 * v4 * v35 * v17 - 6 * u * v24 * v35 * v17 +
                    2 * u4 * v235 * v17 - 6 * u * v4 * v235 * v17 +
                    2 * u23 * v45 * v17 - 6 * u3 * v2 * v45 * v17 -
                    6 * u2 * v3 * v45 * v17 + 24 * u * v2 * v3 * v45 * v17 -
                    6 * u * v23 * v45 * v17 + 2 * u3 * v245 * v17 -
                    6 * u * v3 * v245 * v17 + 2 * u2 * v345 * v17 -
                    6 * u * v2 * v345 * v17 + 2 * u * v2345 * v17 -
                    u1345 * v27 + 2 * u345 * v1 * v27 + 2 * u145 * v3 * v27 -
                    6 * u45 * v1 * v3 * v27 + 2 * u45 * v13 * v27 +
                    2 * u135 * v4 * v27 - 6 * u35 * v1 * v4 * v27 -
                    6 * u15 * v3 * v4 * v27 + 24 * u5 * v1 * v3 * v4 * v27 -
                    6 * u5 * v13 * v4 * v27 + 2 * u35 * v14 * v27 -
                    6 * u5 * v3 * v14 * v27 + 2 * u15 * v34 * v27 -
                    6 * u5 * v1 * v34 * v27 + 2 * u5 * v134 * v27 +
                    2 * u134 * v5 * v27 - 6 * u34 * v1 * v5 * v27 -
                    6 * u14 * v3 * v5 * v27 + 24 * u4 * v1 * v3 * v5 * v27 -
                    6 * u4 * v13 * v5 * v27 - 6 * u13 * v4 * v5 * v27 +
                    24 * u3 * v1 * v4 * v5 * v27 +
                    24 * u1 * v3 * v4 * v5 * v27 -
                    120 * u * v1 * v3 * v4 * v5 * v27 +
                    24 * u * v13 * v4 * v5 * v27 - 6 * u3 * v14 * v5 * v27 +
                    24 * u * v3 * v14 * v5 * v27 - 6 * u1 * v34 * v5 * v27 +
                    24 * u * v1 * v34 * v5 * v27 - 6 * u * v134 * v5 * v27 +
                    2 * u34 * v15 * v27 - 6 * u4 * v3 * v15 * v27 -
                    6 * u3 * v4 * v15 * v27 + 24 * u * v3 * v4 * v15 * v27 -
                    6 * u * v34 * v15 * v27 + 2 * u14 * v35 * v27 -
                    6 * u4 * v1 * v35 * v27 - 6 * u1 * v4 * v35 * v27 +
                    24 * u * v1 * v4 * v35 * v27 - 6 * u * v14 * v35 * v27 +
                    2 * u4 * v135 * v27 - 6 * u * v4 * v135 * v27 +
                    2 * u13 * v45 * v27 - 6 * u3 * v1 * v45 * v27 -
                    6 * u1 * v3 * v45 * v27 + 24 * u * v1 * v3 * v45 * v27 -
                    6 * u * v13 * v45 * v27 + 2 * u3 * v145 * v27 -
                    6 * u * v3 * v145 * v27 + 2 * u1 * v345 * v27 -
                    6 * u * v1 * v345 * v27 + 2 * u * v1345 * v27 -
                    u345 * v127 + 2 * u45 * v3 * v127 + 2 * u35 * v4 * v127 -
                    6 * u5 * v3 * v4 * v127 + 2 * u5 * v34 * v127 +
                    2 * u34 * v5 * v127 - 6 * u4 * v3 * v5 * v127 -
                    6 * u3 * v4 * v5 * v127 + 24 * u * v3 * v4 * v5 * v127 -
                    6 * u * v34 * v5 * v127 + 2 * u4 * v35 * v127 -
                    6 * u * v4 * v35 * v127 + 2 * u3 * v45 * v127 -
                    6 * u * v3 * v45 * v127 + 2 * u * v345 * v127 -
                    u1245 * v37 + 2 * u245 * v1 * v37 + 2 * u145 * v2 * v37 -
                    6 * u45 * v1 * v2 * v37 + 2 * u45 * v12 * v37 +
                    2 * u125 * v4 * v37 - 6 * u25 * v1 * v4 * v37 -
                    6 * u15 * v2 * v4 * v37 + 24 * u5 * v1 * v2 * v4 * v37 -
                    6 * u5 * v12 * v4 * v37 + 2 * u25 * v14 * v37 -
                    6 * u5 * v2 * v14 * v37 + 2 * u15 * v24 * v37 -
                    6 * u5 * v1 * v24 * v37 + 2 * u5 * v124 * v37 +
                    2 * u124 * v5 * v37 - 6 * u24 * v1 * v5 * v37 -
                    6 * u14 * v2 * v5 * v37 + 24 * u4 * v1 * v2 * v5 * v37 -
                    6 * u4 * v12 * v5 * v37 - 6 * u12 * v4 * v5 * v37 +
                    24 * u2 * v1 * v4 * v5 * v37 +
                    24 * u1 * v2 * v4 * v5 * v37 -
                    120 * u * v1 * v2 * v4 * v5 * v37 +
                    24 * u * v12 * v4 * v5 * v37 - 6 * u2 * v14 * v5 * v37 +
                    24 * u * v2 * v14 * v5 * v37 - 6 * u1 * v24 * v5 * v37 +
                    24 * u * v1 * v24 * v5 * v37 - 6 * u * v124 * v5 * v37 +
                    2 * u24 * v15 * v37 - 6 * u4 * v2 * v15 * v37 -
                    6 * u2 * v4 * v15 * v37 + 24 * u * v2 * v4 * v15 * v37 -
                    6 * u * v24 * v15 * v37 + 2 * u14 * v25 * v37 -
                    6 * u4 * v1 * v25 * v37 - 6 * u1 * v4 * v25 * v37 +
                    24 * u * v1 * v4 * v25 * v37 - 6 * u * v14 * v25 * v37 +
                    2 * u4 * v125 * v37 - 6 * u * v4 * v125 * v37 +
                    2 * u12 * v45 * v37 - 6 * u2 * v1 * v45 * v37 -
                    6 * u1 * v2 * v45 * v37 + 24 * u * v1 * v2 * v45 * v37 -
                    6 * u * v12 * v45 * v37 + 2 * u2 * v145 * v37 -
                    6 * u * v2 * v145 * v37 + 2 * u1 * v245 * v37 -
                    6 * u * v1 * v245 * v37 + 2 * u * v1245 * v37 -
                    u245 * v137 + 2 * u45 * v2 * v137 + 2 * u25 * v4 * v137 -
                    6 * u5 * v2 * v4 * v137 + 2 * u5 * v24 * v137 +
                    2 * u24 * v5 * v137 - 6 * u4 * v2 * v5 * v137 -
                    6 * u2 * v4 * v5 * v137 + 24 * u * v2 * v4 * v5 * v137 -
                    6 * u * v24 * v5 * v137 + 2 * u4 * v25 * v137 -
                    6 * u * v4 * v25 * v137 + 2 * u2 * v45 * v137 -
                    6 * u * v2 * v45 * v137 + 2 * u * v245 * v137 -
                    u145 * v237 + 2 * u45 * v1 * v237 + 2 * u15 * v4 * v237 -
                    6 * u5 * v1 * v4 * v237 + 2 * u5 * v14 * v237 +
                    2 * u14 * v5 * v237 - 6 * u4 * v1 * v5 * v237 -
                    6 * u1 * v4 * v5 * v237 + 24 * u * v1 * v4 * v5 * v237 -
                    6 * u * v14 * v5 * v237 + 2 * u4 * v15 * v237 -
                    6 * u * v4 * v15 * v237 + 2 * u1 * v45 * v237 -
                    6 * u * v1 * v45 * v237 + 2 * u * v145 * v237 -
                    u45 * v1237 + 2 * u5 * v4 * v1237 + 2 * u4 * v5 * v1237 -
                    6 * u * v4 * v5 * v1237 + 2 * u * v45 * v1237 -
                    u1235 * v47 + 2 * u235 * v1 * v47 + 2 * u135 * v2 * v47 -
                    6 * u35 * v1 * v2 * v47 + 2 * u35 * v12 * v47 +
                    2 * u125 * v3 * v47 - 6 * u25 * v1 * v3 * v47 -
                    6 * u15 * v2 * v3 * v47 + 24 * u5 * v1 * v2 * v3 * v47 -
                    6 * u5 * v12 * v3 * v47 + 2 * u25 * v13 * v47 -
                    6 * u5 * v2 * v13 * v47 + 2 * u15 * v23 * v47 -
                    6 * u5 * v1 * v23 * v47 + 2 * u5 * v123 * v47 +
                    2 * u123 * v5 * v47 - 6 * u23 * v1 * v5 * v47 -
                    6 * u13 * v2 * v5 * v47 + 24 * u3 * v1 * v2 * v5 * v47 -
                    6 * u3 * v12 * v5 * v47 - 6 * u12 * v3 * v5 * v47 +
                    24 * u2 * v1 * v3 * v5 * v47 +
                    24 * u1 * v2 * v3 * v5 * v47 -
                    120 * u * v1 * v2 * v3 * v5 * v47 +
                    24 * u * v12 * v3 * v5 * v47 - 6 * u2 * v13 * v5 * v47 +
                    24 * u * v2 * v13 * v5 * v47 - 6 * u1 * v23 * v5 * v47 +
                    24 * u * v1 * v23 * v5 * v47 - 6 * u * v123 * v5 * v47 +
                    2 * u23 * v15 * v47 - 6 * u3 * v2 * v15 * v47 -
                    6 * u2 * v3 * v15 * v47 + 24 * u * v2 * v3 * v15 * v47 -
                    6 * u * v23 * v15 * v47 + 2 * u13 * v25 * v47 -
                    6 * u3 * v1 * v25 * v47 - 6 * u1 * v3 * v25 * v47 +
                    24 * u * v1 * v3 * v25 * v47 - 6 * u * v13 * v25 * v47 +
                    2 * u3 * v125 * v47 - 6 * u * v3 * v125 * v47 +
                    2 * u12 * v35 * v47 - 6 * u2 * v1 * v35 * v47 -
                    6 * u1 * v2 * v35 * v47 + 24 * u * v1 * v2 * v35 * v47 -
                    6 * u * v12 * v35 * v47 + 2 * u2 * v135 * v47 -
                    6 * u * v2 * v135 * v47 + 2 * u1 * v235 * v47 -
                    6 * u * v1 * v235 * v47 + 2 * u * v1235 * v47 -
                    u235 * v147 + 2 * u35 * v2 * v147 + 2 * u25 * v3 * v147 -
                    6 * u5 * v2 * v3 * v147 + 2 * u5 * v23 * v147 +
                    2 * u23 * v5 * v147 - 6 * u3 * v2 * v5 * v147 -
                    6 * u2 * v3 * v5 * v147 + 24 * u * v2 * v3 * v5 * v147 -
                    6 * u * v23 * v5 * v147 + 2 * u3 * v25 * v147 -
                    6 * u * v3 * v25 * v147 + 2 * u2 * v35 * v147 -
                    6 * u * v2 * v35 * v147 + 2 * u * v235 * v147 -
                    u135 * v247 + 2 * u35 * v1 * v247 + 2 * u15 * v3 * v247 -
                    6 * u5 * v1 * v3 * v247 + 2 * u5 * v13 * v247 +
                    2 * u13 * v5 * v247 - 6 * u3 * v1 * v5 * v247 -
                    6 * u1 * v3 * v5 * v247 + 24 * u * v1 * v3 * v5 * v247 -
                    6 * u * v13 * v5 * v247 + 2 * u3 * v15 * v247 -
                    6 * u * v3 * v15 * v247 + 2 * u1 * v35 * v247 -
                    6 * u * v1 * v35 * v247 + 2 * u * v135 * v247 -
                    u35 * v1247 + 2 * u5 * v3 * v1247 + 2 * u3 * v5 * v1247 -
                    6 * u * v3 * v5 * v1247 + 2 * u * v35 * v1247 -
                    u125 * v347 + 2 * u25 * v1 * v347 + 2 * u15 * v2 * v347 -
                    6 * u5 * v1 * v2 * v347 + 2 * u5 * v12 * v347 +
                    2 * u12 * v5 * v347 - 6 * u2 * v1 * v5 * v347 -
                    6 * u1 * v2 * v5 * v347 + 24 * u * v1 * v2 * v5 * v347 -
                    6 * u * v12 * v5 * v347 + 2 * u2 * v15 * v347 -
                    6 * u * v2 * v15 * v347 + 2 * u1 * v25 * v347 -
                    6 * u * v1 * v25 * v347 + 2 * u * v125 * v347 -
                    u25 * v1347 + 2 * u5 * v2 * v1347 + 2 * u2 * v5 * v1347 -
                    6 * u * v2 * v5 * v1347 + 2 * u * v25 * v1347 -
                    u15 * v2347 + 2 * u5 * v1 * v2347 + 2 * u1 * v5 * v2347 -
                    6 * u * v1 * v5 * v2347 + 2 * u * v15 * v2347 -
                    u5 * v12347 + 2 * u * v5 * v12347 - u1234 * v57 +
                    2 * u234 * v1 * v57 + 2 * u134 * v2 * v57 -
                    6 * u34 * v1 * v2 * v57 + 2 * u34 * v12 * v57 +
                    2 * u124 * v3 * v57 - 6 * u24 * v1 * v3 * v57 -
                    6 * u14 * v2 * v3 * v57 + 24 * u4 * v1 * v2 * v3 * v57 -
                    6 * u4 * v12 * v3 * v57 + 2 * u24 * v13 * v57 -
                    6 * u4 * v2 * v13 * v57 + 2 * u14 * v23 * v57 -
                    6 * u4 * v1 * v23 * v57 + 2 * u4 * v123 * v57 +
                    2 * u123 * v4 * v57 - 6 * u23 * v1 * v4 * v57 -
                    6 * u13 * v2 * v4 * v57 + 24 * u3 * v1 * v2 * v4 * v57 -
                    6 * u3 * v12 * v4 * v57 - 6 * u12 * v3 * v4 * v57 +
                    24 * u2 * v1 * v3 * v4 * v57 +
                    24 * u1 * v2 * v3 * v4 * v57 -
                    120 * u * v1 * v2 * v3 * v4 * v57 +
                    24 * u * v12 * v3 * v4 * v57 - 6 * u2 * v13 * v4 * v57 +
                    24 * u * v2 * v13 * v4 * v57 - 6 * u1 * v23 * v4 * v57 +
                    24 * u * v1 * v23 * v4 * v57 - 6 * u * v123 * v4 * v57 +
                    2 * u23 * v14 * v57 - 6 * u3 * v2 * v14 * v57 -
                    6 * u2 * v3 * v14 * v57 + 24 * u * v2 * v3 * v14 * v57 -
                    6 * u * v23 * v14 * v57 + 2 * u13 * v24 * v57 -
                    6 * u3 * v1 * v24 * v57 - 6 * u1 * v3 * v24 * v57 +
                    24 * u * v1 * v3 * v24 * v57 - 6 * u * v13 * v24 * v57 +
                    2 * u3 * v124 * v57 - 6 * u * v3 * v124 * v57 +
                    2 * u12 * v34 * v57 - 6 * u2 * v1 * v34 * v57 -
                    6 * u1 * v2 * v34 * v57 + 24 * u * v1 * v2 * v34 * v57 -
                    6 * u * v12 * v34 * v57 + 2 * u2 * v134 * v57 -
                    6 * u * v2 * v134 * v57 + 2 * u1 * v234 * v57 -
                    6 * u * v1 * v234 * v57 + 2 * u * v1234 * v57 -
                    u234 * v157 + 2 * u34 * v2 * v157 + 2 * u24 * v3 * v157 -
                    6 * u4 * v2 * v3 * v157 + 2 * u4 * v23 * v157 +
                    2 * u23 * v4 * v157 - 6 * u3 * v2 * v4 * v157 -
                    6 * u2 * v3 * v4 * v157 + 24 * u * v2 * v3 * v4 * v157 -
                    6 * u * v23 * v4 * v157 + 2 * u3 * v24 * v157 -
                    6 * u * v3 * v24 * v157 + 2 * u2 * v34 * v157 -
                    6 * u * v2 * v34 * v157 + 2 * u * v234 * v157 -
                    u134 * v257 + 2 * u34 * v1 * v257 + 2 * u14 * v3 * v257 -
                    6 * u4 * v1 * v3 * v257 + 2 * u4 * v13 * v257 +
                    2 * u13 * v4 * v257 - 6 * u3 * v1 * v4 * v257 -
                    6 * u1 * v3 * v4 * v257 + 24 * u * v1 * v3 * v4 * v257 -
                    6 * u * v13 * v4 * v257 + 2 * u3 * v14 * v257 -
                    6 * u * v3 * v14 * v257 + 2 * u1 * v34 * v257 -
                    6 * u * v1 * v34 * v257 + 2 * u * v134 * v257 -
                    u34 * v1257 + 2 * u4 * v3 * v1257 + 2 * u3 * v4 * v1257 -
                    6 * u * v3 * v4 * v1257 + 2 * u * v34 * v1257 -
                    u124 * v357 + 2 * u24 * v1 * v357 + 2 * u14 * v2 * v357 -
                    6 * u4 * v1 * v2 * v357 + 2 * u4 * v12 * v357 +
                    2 * u12 * v4 * v357 - 6 * u2 * v1 * v4 * v357 -
                    6 * u1 * v2 * v4 * v357 + 24 * u * v1 * v2 * v4 * v357 -
                    6 * u * v12 * v4 * v357 + 2 * u2 * v14 * v357 -
                    6 * u * v2 * v14 * v357 + 2 * u1 * v24 * v357 -
                    6 * u * v1 * v24 * v357 + 2 * u * v124 * v357 -
                    u24 * v1357 + 2 * u4 * v2 * v1357 + 2 * u2 * v4 * v1357 -
                    6 * u * v2 * v4 * v1357 + 2 * u * v24 * v1357 -
                    u14 * v2357 + 2 * u4 * v1 * v2357 + 2 * u1 * v4 * v2357 -
                    6 * u * v1 * v4 * v2357 + 2 * u * v14 * v2357 -
                    u4 * v12357 + 2 * u * v4 * v12357 - u123 * v457 +
                    2 * u23 * v1 * v457 + 2 * u13 * v2 * v457 -
                    6 * u3 * v1 * v2 * v457 + 2 * u3 * v12 * v457 +
                    2 * u12 * v3 * v457 - 6 * u2 * v1 * v3 * v457 -
                    6 * u1 * v2 * v3 * v457 + 24 * u * v1 * v2 * v3 * v457 -
                    6 * u * v12 * v3 * v457 + 2 * u2 * v13 * v457 -
                    6 * u * v2 * v13 * v457 + 2 * u1 * v23 * v457 -
                    6 * u * v1 * v23 * v457 + 2 * u * v123 * v457 -
                    u23 * v1457 + 2 * u3 * v2 * v1457 + 2 * u2 * v3 * v1457 -
                    6 * u * v2 * v3 * v1457 + 2 * u * v23 * v1457 -
                    u13 * v2457 + 2 * u3 * v1 * v2457 + 2 * u1 * v3 * v2457 -
                    6 * u * v1 * v3 * v2457 + 2 * u * v13 * v2457 -
                    u3 * v12457 + 2 * u * v3 * v12457 - u12 * v3457 +
                    2 * u2 * v1 * v3457 + 2 * u1 * v2 * v3457 -
                    6 * u * v1 * v2 * v3457 + 2 * u * v12 * v3457 -
                    u2 * v13457 + 2 * u * v2 * v13457 - u1 * v23457 +
                    2 * u * v1 * v23457 - u * v123457,
            .dual67 = u67 - u7 * v6 - u6 * v7 + 2 * u * v6 * v7 - u * v67,
            .dual167 = u167 - u67 * v1 - u17 * v6 + 2 * u7 * v1 * v6 -
                       u7 * v16 - u16 * v7 + 2 * u6 * v1 * v7 +
                       2 * u1 * v6 * v7 - 6 * u * v1 * v6 * v7 +
                       2 * u * v16 * v7 - u6 * v17 + 2 * u * v6 * v17 -
                       u1 * v67 + 2 * u * v1 * v67 - u * v167,
            .dual267 = u267 - u67 * v2 - u27 * v6 + 2 * u7 * v2 * v6 -
                       u7 * v26 - u26 * v7 + 2 * u6 * v2 * v7 +
                       2 * u2 * v6 * v7 - 6 * u * v2 * v6 * v7 +
                       2 * u * v26 * v7 - u6 * v27 + 2 * u * v6 * v27 -
                       u2 * v67 + 2 * u * v2 * v67 - u * v267,
            .dual1267 = u1267 - u267 * v1 - u167 * v2 + 2 * u67 * v1 * v2 -
                        u67 * v12 - u127 * v6 + 2 * u27 * v1 * v6 +
                        2 * u17 * v2 * v6 - 6 * u7 * v1 * v2 * v6 +
                        2 * u7 * v12 * v6 - u27 * v16 + 2 * u7 * v2 * v16 -
                        u17 * v26 + 2 * u7 * v1 * v26 - u7 * v126 - u126 * v7 +
                        2 * u26 * v1 * v7 + 2 * u16 * v2 * v7 -
                        6 * u6 * v1 * v2 * v7 + 2 * u6 * v12 * v7 +
                        2 * u12 * v6 * v7 - 6 * u2 * v1 * v6 * v7 -
                        6 * u1 * v2 * v6 * v7 + 24 * u * v1 * v2 * v6 * v7 -
                        6 * u * v12 * v6 * v7 + 2 * u2 * v16 * v7 -
                        6 * u * v2 * v16 * v7 + 2 * u1 * v26 * v7 -
                        6 * u * v1 * v26 * v7 + 2 * u * v126 * v7 - u26 * v17 +
                        2 * u6 * v2 * v17 + 2 * u2 * v6 * v17 -
                        6 * u * v2 * v6 * v17 + 2 * u * v26 * v17 - u16 * v27 +
                        2 * u6 * v1 * v27 + 2 * u1 * v6 * v27 -
                        6 * u * v1 * v6 * v27 + 2 * u * v16 * v27 - u6 * v127 +
                        2 * u * v6 * v127 - u12 * v67 + 2 * u2 * v1 * v67 +
                        2 * u1 * v2 * v67 - 6 * u * v1 * v2 * v67 +
                        2 * u * v12 * v67 - u2 * v167 + 2 * u * v2 * v167 -
                        u1 * v267 + 2 * u * v1 * v267 - u * v1267,
            .dual367 = u367 - u67 * v3 - u37 * v6 + 2 * u7 * v3 * v6 -
                       u7 * v36 - u36 * v7 + 2 * u6 * v3 * v7 +
                       2 * u3 * v6 * v7 - 6 * u * v3 * v6 * v7 +
                       2 * u * v36 * v7 - u6 * v37 + 2 * u * v6 * v37 -
                       u3 * v67 + 2 * u * v3 * v67 - u * v367,
            .dual1367 = u1367 - u367 * v1 - u167 * v3 + 2 * u67 * v1 * v3 -
                        u67 * v13 - u137 * v6 + 2 * u37 * v1 * v6 +
                        2 * u17 * v3 * v6 - 6 * u7 * v1 * v3 * v6 +
                        2 * u7 * v13 * v6 - u37 * v16 + 2 * u7 * v3 * v16 -
                        u17 * v36 + 2 * u7 * v1 * v36 - u7 * v136 - u136 * v7 +
                        2 * u36 * v1 * v7 + 2 * u16 * v3 * v7 -
                        6 * u6 * v1 * v3 * v7 + 2 * u6 * v13 * v7 +
                        2 * u13 * v6 * v7 - 6 * u3 * v1 * v6 * v7 -
                        6 * u1 * v3 * v6 * v7 + 24 * u * v1 * v3 * v6 * v7 -
                        6 * u * v13 * v6 * v7 + 2 * u3 * v16 * v7 -
                        6 * u * v3 * v16 * v7 + 2 * u1 * v36 * v7 -
                        6 * u * v1 * v36 * v7 + 2 * u * v136 * v7 - u36 * v17 +
                        2 * u6 * v3 * v17 + 2 * u3 * v6 * v17 -
                        6 * u * v3 * v6 * v17 + 2 * u * v36 * v17 - u16 * v37 +
                        2 * u6 * v1 * v37 + 2 * u1 * v6 * v37 -
                        6 * u * v1 * v6 * v37 + 2 * u * v16 * v37 - u6 * v137 +
                        2 * u * v6 * v137 - u13 * v67 + 2 * u3 * v1 * v67 +
                        2 * u1 * v3 * v67 - 6 * u * v1 * v3 * v67 +
                        2 * u * v13 * v67 - u3 * v167 + 2 * u * v3 * v167 -
                        u1 * v367 + 2 * u * v1 * v367 - u * v1367,
            .dual2367 = u2367 - u367 * v2 - u267 * v3 + 2 * u67 * v2 * v3 -
                        u67 * v23 - u237 * v6 + 2 * u37 * v2 * v6 +
                        2 * u27 * v3 * v6 - 6 * u7 * v2 * v3 * v6 +
                        2 * u7 * v23 * v6 - u37 * v26 + 2 * u7 * v3 * v26 -
                        u27 * v36 + 2 * u7 * v2 * v36 - u7 * v236 - u236 * v7 +
                        2 * u36 * v2 * v7 + 2 * u26 * v3 * v7 -
                        6 * u6 * v2 * v3 * v7 + 2 * u6 * v23 * v7 +
                        2 * u23 * v6 * v7 - 6 * u3 * v2 * v6 * v7 -
                        6 * u2 * v3 * v6 * v7 + 24 * u * v2 * v3 * v6 * v7 -
                        6 * u * v23 * v6 * v7 + 2 * u3 * v26 * v7 -
                        6 * u * v3 * v26 * v7 + 2 * u2 * v36 * v7 -
                        6 * u * v2 * v36 * v7 + 2 * u * v236 * v7 - u36 * v27 +
                        2 * u6 * v3 * v27 + 2 * u3 * v6 * v27 -
                        6 * u * v3 * v6 * v27 + 2 * u * v36 * v27 - u26 * v37 +
                        2 * u6 * v2 * v37 + 2 * u2 * v6 * v37 -
                        6 * u * v2 * v6 * v37 + 2 * u * v26 * v37 - u6 * v237 +
                        2 * u * v6 * v237 - u23 * v67 + 2 * u3 * v2 * v67 +
                        2 * u2 * v3 * v67 - 6 * u * v2 * v3 * v67 +
                        2 * u * v23 * v67 - u3 * v267 + 2 * u * v3 * v267 -
                        u2 * v367 + 2 * u * v2 * v367 - u * v2367,
            .dual12367 =
                    u12367 - u2367 * v1 - u1367 * v2 + 2 * u367 * v1 * v2 -
                    u367 * v12 - u1267 * v3 + 2 * u267 * v1 * v3 +
                    2 * u167 * v2 * v3 - 6 * u67 * v1 * v2 * v3 +
                    2 * u67 * v12 * v3 - u267 * v13 + 2 * u67 * v2 * v13 -
                    u167 * v23 + 2 * u67 * v1 * v23 - u67 * v123 - u1237 * v6 +
                    2 * u237 * v1 * v6 + 2 * u137 * v2 * v6 -
                    6 * u37 * v1 * v2 * v6 + 2 * u37 * v12 * v6 +
                    2 * u127 * v3 * v6 - 6 * u27 * v1 * v3 * v6 -
                    6 * u17 * v2 * v3 * v6 + 24 * u7 * v1 * v2 * v3 * v6 -
                    6 * u7 * v12 * v3 * v6 + 2 * u27 * v13 * v6 -
                    6 * u7 * v2 * v13 * v6 + 2 * u17 * v23 * v6 -
                    6 * u7 * v1 * v23 * v6 + 2 * u7 * v123 * v6 - u237 * v16 +
                    2 * u37 * v2 * v16 + 2 * u27 * v3 * v16 -
                    6 * u7 * v2 * v3 * v16 + 2 * u7 * v23 * v16 - u137 * v26 +
                    2 * u37 * v1 * v26 + 2 * u17 * v3 * v26 -
                    6 * u7 * v1 * v3 * v26 + 2 * u7 * v13 * v26 - u37 * v126 +
                    2 * u7 * v3 * v126 - u127 * v36 + 2 * u27 * v1 * v36 +
                    2 * u17 * v2 * v36 - 6 * u7 * v1 * v2 * v36 +
                    2 * u7 * v12 * v36 - u27 * v136 + 2 * u7 * v2 * v136 -
                    u17 * v236 + 2 * u7 * v1 * v236 - u7 * v1236 - u1236 * v7 +
                    2 * u236 * v1 * v7 + 2 * u136 * v2 * v7 -
                    6 * u36 * v1 * v2 * v7 + 2 * u36 * v12 * v7 +
                    2 * u126 * v3 * v7 - 6 * u26 * v1 * v3 * v7 -
                    6 * u16 * v2 * v3 * v7 + 24 * u6 * v1 * v2 * v3 * v7 -
                    6 * u6 * v12 * v3 * v7 + 2 * u26 * v13 * v7 -
                    6 * u6 * v2 * v13 * v7 + 2 * u16 * v23 * v7 -
                    6 * u6 * v1 * v23 * v7 + 2 * u6 * v123 * v7 +
                    2 * u123 * v6 * v7 - 6 * u23 * v1 * v6 * v7 -
                    6 * u13 * v2 * v6 * v7 + 24 * u3 * v1 * v2 * v6 * v7 -
                    6 * u3 * v12 * v6 * v7 - 6 * u12 * v3 * v6 * v7 +
                    24 * u2 * v1 * v3 * v6 * v7 + 24 * u1 * v2 * v3 * v6 * v7 -
                    120 * u * v1 * v2 * v3 * v6 * v7 +
                    24 * u * v12 * v3 * v6 * v7 - 6 * u2 * v13 * v6 * v7 +
                    24 * u * v2 * v13 * v6 * v7 - 6 * u1 * v23 * v6 * v7 +
                    24 * u * v1 * v23 * v6 * v7 - 6 * u * v123 * v6 * v7 +
                    2 * u23 * v16 * v7 - 6 * u3 * v2 * v16 * v7 -
                    6 * u2 * v3 * v16 * v7 + 24 * u * v2 * v3 * v16 * v7 -
                    6 * u * v23 * v16 * v7 + 2 * u13 * v26 * v7 -
                    6 * u3 * v1 * v26 * v7 - 6 * u1 * v3 * v26 * v7 +
                    24 * u * v1 * v3 * v26 * v7 - 6 * u * v13 * v26 * v7 +
                    2 * u3 * v126 * v7 - 6 * u * v3 * v126 * v7 +
                    2 * u12 * v36 * v7 - 6 * u2 * v1 * v36 * v7 -
                    6 * u1 * v2 * v36 * v7 + 24 * u * v1 * v2 * v36 * v7 -
                    6 * u * v12 * v36 * v7 + 2 * u2 * v136 * v7 -
                    6 * u * v2 * v136 * v7 + 2 * u1 * v236 * v7 -
                    6 * u * v1 * v236 * v7 + 2 * u * v1236 * v7 - u236 * v17 +
                    2 * u36 * v2 * v17 + 2 * u26 * v3 * v17 -
                    6 * u6 * v2 * v3 * v17 + 2 * u6 * v23 * v17 +
                    2 * u23 * v6 * v17 - 6 * u3 * v2 * v6 * v17 -
                    6 * u2 * v3 * v6 * v17 + 24 * u * v2 * v3 * v6 * v17 -
                    6 * u * v23 * v6 * v17 + 2 * u3 * v26 * v17 -
                    6 * u * v3 * v26 * v17 + 2 * u2 * v36 * v17 -
                    6 * u * v2 * v36 * v17 + 2 * u * v236 * v17 - u136 * v27 +
                    2 * u36 * v1 * v27 + 2 * u16 * v3 * v27 -
                    6 * u6 * v1 * v3 * v27 + 2 * u6 * v13 * v27 +
                    2 * u13 * v6 * v27 - 6 * u3 * v1 * v6 * v27 -
                    6 * u1 * v3 * v6 * v27 + 24 * u * v1 * v3 * v6 * v27 -
                    6 * u * v13 * v6 * v27 + 2 * u3 * v16 * v27 -
                    6 * u * v3 * v16 * v27 + 2 * u1 * v36 * v27 -
                    6 * u * v1 * v36 * v27 + 2 * u * v136 * v27 - u36 * v127 +
                    2 * u6 * v3 * v127 + 2 * u3 * v6 * v127 -
                    6 * u * v3 * v6 * v127 + 2 * u * v36 * v127 - u126 * v37 +
                    2 * u26 * v1 * v37 + 2 * u16 * v2 * v37 -
                    6 * u6 * v1 * v2 * v37 + 2 * u6 * v12 * v37 +
                    2 * u12 * v6 * v37 - 6 * u2 * v1 * v6 * v37 -
                    6 * u1 * v2 * v6 * v37 + 24 * u * v1 * v2 * v6 * v37 -
                    6 * u * v12 * v6 * v37 + 2 * u2 * v16 * v37 -
                    6 * u * v2 * v16 * v37 + 2 * u1 * v26 * v37 -
                    6 * u * v1 * v26 * v37 + 2 * u * v126 * v37 - u26 * v137 +
                    2 * u6 * v2 * v137 + 2 * u2 * v6 * v137 -
                    6 * u * v2 * v6 * v137 + 2 * u * v26 * v137 - u16 * v237 +
                    2 * u6 * v1 * v237 + 2 * u1 * v6 * v237 -
                    6 * u * v1 * v6 * v237 + 2 * u * v16 * v237 - u6 * v1237 +
                    2 * u * v6 * v1237 - u123 * v67 + 2 * u23 * v1 * v67 +
                    2 * u13 * v2 * v67 - 6 * u3 * v1 * v2 * v67 +
                    2 * u3 * v12 * v67 + 2 * u12 * v3 * v67 -
                    6 * u2 * v1 * v3 * v67 - 6 * u1 * v2 * v3 * v67 +
                    24 * u * v1 * v2 * v3 * v67 - 6 * u * v12 * v3 * v67 +
                    2 * u2 * v13 * v67 - 6 * u * v2 * v13 * v67 +
                    2 * u1 * v23 * v67 - 6 * u * v1 * v23 * v67 +
                    2 * u * v123 * v67 - u23 * v167 + 2 * u3 * v2 * v167 +
                    2 * u2 * v3 * v167 - 6 * u * v2 * v3 * v167 +
                    2 * u * v23 * v167 - u13 * v267 + 2 * u3 * v1 * v267 +
                    2 * u1 * v3 * v267 - 6 * u * v1 * v3 * v267 +
                    2 * u * v13 * v267 - u3 * v1267 + 2 * u * v3 * v1267 -
                    u12 * v367 + 2 * u2 * v1 * v367 + 2 * u1 * v2 * v367 -
                    6 * u * v1 * v2 * v367 + 2 * u * v12 * v367 - u2 * v1367 +
                    2 * u * v2 * v1367 - u1 * v2367 + 2 * u * v1 * v2367 -
                    u * v12367,
            .dual467 = u467 - u67 * v4 - u47 * v6 + 2 * u7 * v4 * v6 -
                       u7 * v46 - u46 * v7 + 2 * u6 * v4 * v7 +
                       2 * u4 * v6 * v7 - 6 * u * v4 * v6 * v7 +
                       2 * u * v46 * v7 - u6 * v47 + 2 * u * v6 * v47 -
                       u4 * v67 + 2 * u * v4 * v67 - u * v467,
            .dual1467 = u1467 - u467 * v1 - u167 * v4 + 2 * u67 * v1 * v4 -
                        u67 * v14 - u147 * v6 + 2 * u47 * v1 * v6 +
                        2 * u17 * v4 * v6 - 6 * u7 * v1 * v4 * v6 +
                        2 * u7 * v14 * v6 - u47 * v16 + 2 * u7 * v4 * v16 -
                        u17 * v46 + 2 * u7 * v1 * v46 - u7 * v146 - u146 * v7 +
                        2 * u46 * v1 * v7 + 2 * u16 * v4 * v7 -
                        6 * u6 * v1 * v4 * v7 + 2 * u6 * v14 * v7 +
                        2 * u14 * v6 * v7 - 6 * u4 * v1 * v6 * v7 -
                        6 * u1 * v4 * v6 * v7 + 24 * u * v1 * v4 * v6 * v7 -
                        6 * u * v14 * v6 * v7 + 2 * u4 * v16 * v7 -
                        6 * u * v4 * v16 * v7 + 2 * u1 * v46 * v7 -
                        6 * u * v1 * v46 * v7 + 2 * u * v146 * v7 - u46 * v17 +
                        2 * u6 * v4 * v17 + 2 * u4 * v6 * v17 -
                        6 * u * v4 * v6 * v17 + 2 * u * v46 * v17 - u16 * v47 +
                        2 * u6 * v1 * v47 + 2 * u1 * v6 * v47 -
                        6 * u * v1 * v6 * v47 + 2 * u * v16 * v47 - u6 * v147 +
                        2 * u * v6 * v147 - u14 * v67 + 2 * u4 * v1 * v67 +
                        2 * u1 * v4 * v67 - 6 * u * v1 * v4 * v67 +
                        2 * u * v14 * v67 - u4 * v167 + 2 * u * v4 * v167 -
                        u1 * v467 + 2 * u * v1 * v467 - u * v1467,
            .dual2467 = u2467 - u467 * v2 - u267 * v4 + 2 * u67 * v2 * v4 -
                        u67 * v24 - u247 * v6 + 2 * u47 * v2 * v6 +
                        2 * u27 * v4 * v6 - 6 * u7 * v2 * v4 * v6 +
                        2 * u7 * v24 * v6 - u47 * v26 + 2 * u7 * v4 * v26 -
                        u27 * v46 + 2 * u7 * v2 * v46 - u7 * v246 - u246 * v7 +
                        2 * u46 * v2 * v7 + 2 * u26 * v4 * v7 -
                        6 * u6 * v2 * v4 * v7 + 2 * u6 * v24 * v7 +
                        2 * u24 * v6 * v7 - 6 * u4 * v2 * v6 * v7 -
                        6 * u2 * v4 * v6 * v7 + 24 * u * v2 * v4 * v6 * v7 -
                        6 * u * v24 * v6 * v7 + 2 * u4 * v26 * v7 -
                        6 * u * v4 * v26 * v7 + 2 * u2 * v46 * v7 -
                        6 * u * v2 * v46 * v7 + 2 * u * v246 * v7 - u46 * v27 +
                        2 * u6 * v4 * v27 + 2 * u4 * v6 * v27 -
                        6 * u * v4 * v6 * v27 + 2 * u * v46 * v27 - u26 * v47 +
                        2 * u6 * v2 * v47 + 2 * u2 * v6 * v47 -
                        6 * u * v2 * v6 * v47 + 2 * u * v26 * v47 - u6 * v247 +
                        2 * u * v6 * v247 - u24 * v67 + 2 * u4 * v2 * v67 +
                        2 * u2 * v4 * v67 - 6 * u * v2 * v4 * v67 +
                        2 * u * v24 * v67 - u4 * v267 + 2 * u * v4 * v267 -
                        u2 * v467 + 2 * u * v2 * v467 - u * v2467,
            .dual12467 =
                    u12467 - u2467 * v1 - u1467 * v2 + 2 * u467 * v1 * v2 -
                    u467 * v12 - u1267 * v4 + 2 * u267 * v1 * v4 +
                    2 * u167 * v2 * v4 - 6 * u67 * v1 * v2 * v4 +
                    2 * u67 * v12 * v4 - u267 * v14 + 2 * u67 * v2 * v14 -
                    u167 * v24 + 2 * u67 * v1 * v24 - u67 * v124 - u1247 * v6 +
                    2 * u247 * v1 * v6 + 2 * u147 * v2 * v6 -
                    6 * u47 * v1 * v2 * v6 + 2 * u47 * v12 * v6 +
                    2 * u127 * v4 * v6 - 6 * u27 * v1 * v4 * v6 -
                    6 * u17 * v2 * v4 * v6 + 24 * u7 * v1 * v2 * v4 * v6 -
                    6 * u7 * v12 * v4 * v6 + 2 * u27 * v14 * v6 -
                    6 * u7 * v2 * v14 * v6 + 2 * u17 * v24 * v6 -
                    6 * u7 * v1 * v24 * v6 + 2 * u7 * v124 * v6 - u247 * v16 +
                    2 * u47 * v2 * v16 + 2 * u27 * v4 * v16 -
                    6 * u7 * v2 * v4 * v16 + 2 * u7 * v24 * v16 - u147 * v26 +
                    2 * u47 * v1 * v26 + 2 * u17 * v4 * v26 -
                    6 * u7 * v1 * v4 * v26 + 2 * u7 * v14 * v26 - u47 * v126 +
                    2 * u7 * v4 * v126 - u127 * v46 + 2 * u27 * v1 * v46 +
                    2 * u17 * v2 * v46 - 6 * u7 * v1 * v2 * v46 +
                    2 * u7 * v12 * v46 - u27 * v146 + 2 * u7 * v2 * v146 -
                    u17 * v246 + 2 * u7 * v1 * v246 - u7 * v1246 - u1246 * v7 +
                    2 * u246 * v1 * v7 + 2 * u146 * v2 * v7 -
                    6 * u46 * v1 * v2 * v7 + 2 * u46 * v12 * v7 +
                    2 * u126 * v4 * v7 - 6 * u26 * v1 * v4 * v7 -
                    6 * u16 * v2 * v4 * v7 + 24 * u6 * v1 * v2 * v4 * v7 -
                    6 * u6 * v12 * v4 * v7 + 2 * u26 * v14 * v7 -
                    6 * u6 * v2 * v14 * v7 + 2 * u16 * v24 * v7 -
                    6 * u6 * v1 * v24 * v7 + 2 * u6 * v124 * v7 +
                    2 * u124 * v6 * v7 - 6 * u24 * v1 * v6 * v7 -
                    6 * u14 * v2 * v6 * v7 + 24 * u4 * v1 * v2 * v6 * v7 -
                    6 * u4 * v12 * v6 * v7 - 6 * u12 * v4 * v6 * v7 +
                    24 * u2 * v1 * v4 * v6 * v7 + 24 * u1 * v2 * v4 * v6 * v7 -
                    120 * u * v1 * v2 * v4 * v6 * v7 +
                    24 * u * v12 * v4 * v6 * v7 - 6 * u2 * v14 * v6 * v7 +
                    24 * u * v2 * v14 * v6 * v7 - 6 * u1 * v24 * v6 * v7 +
                    24 * u * v1 * v24 * v6 * v7 - 6 * u * v124 * v6 * v7 +
                    2 * u24 * v16 * v7 - 6 * u4 * v2 * v16 * v7 -
                    6 * u2 * v4 * v16 * v7 + 24 * u * v2 * v4 * v16 * v7 -
                    6 * u * v24 * v16 * v7 + 2 * u14 * v26 * v7 -
                    6 * u4 * v1 * v26 * v7 - 6 * u1 * v4 * v26 * v7 +
                    24 * u * v1 * v4 * v26 * v7 - 6 * u * v14 * v26 * v7 +
                    2 * u4 * v126 * v7 - 6 * u * v4 * v126 * v7 +
                    2 * u12 * v46 * v7 - 6 * u2 * v1 * v46 * v7 -
                    6 * u1 * v2 * v46 * v7 + 24 * u * v1 * v2 * v46 * v7 -
                    6 * u * v12 * v46 * v7 + 2 * u2 * v146 * v7 -
                    6 * u * v2 * v146 * v7 + 2 * u1 * v246 * v7 -
                    6 * u * v1 * v246 * v7 + 2 * u * v1246 * v7 - u246 * v17 +
                    2 * u46 * v2 * v17 + 2 * u26 * v4 * v17 -
                    6 * u6 * v2 * v4 * v17 + 2 * u6 * v24 * v17 +
                    2 * u24 * v6 * v17 - 6 * u4 * v2 * v6 * v17 -
                    6 * u2 * v4 * v6 * v17 + 24 * u * v2 * v4 * v6 * v17 -
                    6 * u * v24 * v6 * v17 + 2 * u4 * v26 * v17 -
                    6 * u * v4 * v26 * v17 + 2 * u2 * v46 * v17 -
                    6 * u * v2 * v46 * v17 + 2 * u * v246 * v17 - u146 * v27 +
                    2 * u46 * v1 * v27 + 2 * u16 * v4 * v27 -
                    6 * u6 * v1 * v4 * v27 + 2 * u6 * v14 * v27 +
                    2 * u14 * v6 * v27 - 6 * u4 * v1 * v6 * v27 -
                    6 * u1 * v4 * v6 * v27 + 24 * u * v1 * v4 * v6 * v27 -
                    6 * u * v14 * v6 * v27 + 2 * u4 * v16 * v27 -
                    6 * u * v4 * v16 * v27 + 2 * u1 * v46 * v27 -
                    6 * u * v1 * v46 * v27 + 2 * u * v146 * v27 - u46 * v127 +
                    2 * u6 * v4 * v127 + 2 * u4 * v6 * v127 -
                    6 * u * v4 * v6 * v127 + 2 * u * v46 * v127 - u126 * v47 +
                    2 * u26 * v1 * v47 + 2 * u16 * v2 * v47 -
                    6 * u6 * v1 * v2 * v47 + 2 * u6 * v12 * v47 +
                    2 * u12 * v6 * v47 - 6 * u2 * v1 * v6 * v47 -
                    6 * u1 * v2 * v6 * v47 + 24 * u * v1 * v2 * v6 * v47 -
                    6 * u * v12 * v6 * v47 + 2 * u2 * v16 * v47 -
                    6 * u * v2 * v16 * v47 + 2 * u1 * v26 * v47 -
                    6 * u * v1 * v26 * v47 + 2 * u * v126 * v47 - u26 * v147 +
                    2 * u6 * v2 * v147 + 2 * u2 * v6 * v147 -
                    6 * u * v2 * v6 * v147 + 2 * u * v26 * v147 - u16 * v247 +
                    2 * u6 * v1 * v247 + 2 * u1 * v6 * v247 -
                    6 * u * v1 * v6 * v247 + 2 * u * v16 * v247 - u6 * v1247 +
                    2 * u * v6 * v1247 - u124 * v67 + 2 * u24 * v1 * v67 +
                    2 * u14 * v2 * v67 - 6 * u4 * v1 * v2 * v67 +
                    2 * u4 * v12 * v67 + 2 * u12 * v4 * v67 -
                    6 * u2 * v1 * v4 * v67 - 6 * u1 * v2 * v4 * v67 +
                    24 * u * v1 * v2 * v4 * v67 - 6 * u * v12 * v4 * v67 +
                    2 * u2 * v14 * v67 - 6 * u * v2 * v14 * v67 +
                    2 * u1 * v24 * v67 - 6 * u * v1 * v24 * v67 +
                    2 * u * v124 * v67 - u24 * v167 + 2 * u4 * v2 * v167 +
                    2 * u2 * v4 * v167 - 6 * u * v2 * v4 * v167 +
                    2 * u * v24 * v167 - u14 * v267 + 2 * u4 * v1 * v267 +
                    2 * u1 * v4 * v267 - 6 * u * v1 * v4 * v267 +
                    2 * u * v14 * v267 - u4 * v1267 + 2 * u * v4 * v1267 -
                    u12 * v467 + 2 * u2 * v1 * v467 + 2 * u1 * v2 * v467 -
                    6 * u * v1 * v2 * v467 + 2 * u * v12 * v467 - u2 * v1467 +
                    2 * u * v2 * v1467 - u1 * v2467 + 2 * u * v1 * v2467 -
                    u * v12467,
            .dual3467 = u3467 - u467 * v3 - u367 * v4 + 2 * u67 * v3 * v4 -
                        u67 * v34 - u347 * v6 + 2 * u47 * v3 * v6 +
                        2 * u37 * v4 * v6 - 6 * u7 * v3 * v4 * v6 +
                        2 * u7 * v34 * v6 - u47 * v36 + 2 * u7 * v4 * v36 -
                        u37 * v46 + 2 * u7 * v3 * v46 - u7 * v346 - u346 * v7 +
                        2 * u46 * v3 * v7 + 2 * u36 * v4 * v7 -
                        6 * u6 * v3 * v4 * v7 + 2 * u6 * v34 * v7 +
                        2 * u34 * v6 * v7 - 6 * u4 * v3 * v6 * v7 -
                        6 * u3 * v4 * v6 * v7 + 24 * u * v3 * v4 * v6 * v7 -
                        6 * u * v34 * v6 * v7 + 2 * u4 * v36 * v7 -
                        6 * u * v4 * v36 * v7 + 2 * u3 * v46 * v7 -
                        6 * u * v3 * v46 * v7 + 2 * u * v346 * v7 - u46 * v37 +
                        2 * u6 * v4 * v37 + 2 * u4 * v6 * v37 -
                        6 * u * v4 * v6 * v37 + 2 * u * v46 * v37 - u36 * v47 +
                        2 * u6 * v3 * v47 + 2 * u3 * v6 * v47 -
                        6 * u * v3 * v6 * v47 + 2 * u * v36 * v47 - u6 * v347 +
                        2 * u * v6 * v347 - u34 * v67 + 2 * u4 * v3 * v67 +
                        2 * u3 * v4 * v67 - 6 * u * v3 * v4 * v67 +
                        2 * u * v34 * v67 - u4 * v367 + 2 * u * v4 * v367 -
                        u3 * v467 + 2 * u * v3 * v467 - u * v3467,
            .dual13467 =
                    u13467 - u3467 * v1 - u1467 * v3 + 2 * u467 * v1 * v3 -
                    u467 * v13 - u1367 * v4 + 2 * u367 * v1 * v4 +
                    2 * u167 * v3 * v4 - 6 * u67 * v1 * v3 * v4 +
                    2 * u67 * v13 * v4 - u367 * v14 + 2 * u67 * v3 * v14 -
                    u167 * v34 + 2 * u67 * v1 * v34 - u67 * v134 - u1347 * v6 +
                    2 * u347 * v1 * v6 + 2 * u147 * v3 * v6 -
                    6 * u47 * v1 * v3 * v6 + 2 * u47 * v13 * v6 +
                    2 * u137 * v4 * v6 - 6 * u37 * v1 * v4 * v6 -
                    6 * u17 * v3 * v4 * v6 + 24 * u7 * v1 * v3 * v4 * v6 -
                    6 * u7 * v13 * v4 * v6 + 2 * u37 * v14 * v6 -
                    6 * u7 * v3 * v14 * v6 + 2 * u17 * v34 * v6 -
                    6 * u7 * v1 * v34 * v6 + 2 * u7 * v134 * v6 - u347 * v16 +
                    2 * u47 * v3 * v16 + 2 * u37 * v4 * v16 -
                    6 * u7 * v3 * v4 * v16 + 2 * u7 * v34 * v16 - u147 * v36 +
                    2 * u47 * v1 * v36 + 2 * u17 * v4 * v36 -
                    6 * u7 * v1 * v4 * v36 + 2 * u7 * v14 * v36 - u47 * v136 +
                    2 * u7 * v4 * v136 - u137 * v46 + 2 * u37 * v1 * v46 +
                    2 * u17 * v3 * v46 - 6 * u7 * v1 * v3 * v46 +
                    2 * u7 * v13 * v46 - u37 * v146 + 2 * u7 * v3 * v146 -
                    u17 * v346 + 2 * u7 * v1 * v346 - u7 * v1346 - u1346 * v7 +
                    2 * u346 * v1 * v7 + 2 * u146 * v3 * v7 -
                    6 * u46 * v1 * v3 * v7 + 2 * u46 * v13 * v7 +
                    2 * u136 * v4 * v7 - 6 * u36 * v1 * v4 * v7 -
                    6 * u16 * v3 * v4 * v7 + 24 * u6 * v1 * v3 * v4 * v7 -
                    6 * u6 * v13 * v4 * v7 + 2 * u36 * v14 * v7 -
                    6 * u6 * v3 * v14 * v7 + 2 * u16 * v34 * v7 -
                    6 * u6 * v1 * v34 * v7 + 2 * u6 * v134 * v7 +
                    2 * u134 * v6 * v7 - 6 * u34 * v1 * v6 * v7 -
                    6 * u14 * v3 * v6 * v7 + 24 * u4 * v1 * v3 * v6 * v7 -
                    6 * u4 * v13 * v6 * v7 - 6 * u13 * v4 * v6 * v7 +
                    24 * u3 * v1 * v4 * v6 * v7 + 24 * u1 * v3 * v4 * v6 * v7 -
                    120 * u * v1 * v3 * v4 * v6 * v7 +
                    24 * u * v13 * v4 * v6 * v7 - 6 * u3 * v14 * v6 * v7 +
                    24 * u * v3 * v14 * v6 * v7 - 6 * u1 * v34 * v6 * v7 +
                    24 * u * v1 * v34 * v6 * v7 - 6 * u * v134 * v6 * v7 +
                    2 * u34 * v16 * v7 - 6 * u4 * v3 * v16 * v7 -
                    6 * u3 * v4 * v16 * v7 + 24 * u * v3 * v4 * v16 * v7 -
                    6 * u * v34 * v16 * v7 + 2 * u14 * v36 * v7 -
                    6 * u4 * v1 * v36 * v7 - 6 * u1 * v4 * v36 * v7 +
                    24 * u * v1 * v4 * v36 * v7 - 6 * u * v14 * v36 * v7 +
                    2 * u4 * v136 * v7 - 6 * u * v4 * v136 * v7 +
                    2 * u13 * v46 * v7 - 6 * u3 * v1 * v46 * v7 -
                    6 * u1 * v3 * v46 * v7 + 24 * u * v1 * v3 * v46 * v7 -
                    6 * u * v13 * v46 * v7 + 2 * u3 * v146 * v7 -
                    6 * u * v3 * v146 * v7 + 2 * u1 * v346 * v7 -
                    6 * u * v1 * v346 * v7 + 2 * u * v1346 * v7 - u346 * v17 +
                    2 * u46 * v3 * v17 + 2 * u36 * v4 * v17 -
                    6 * u6 * v3 * v4 * v17 + 2 * u6 * v34 * v17 +
                    2 * u34 * v6 * v17 - 6 * u4 * v3 * v6 * v17 -
                    6 * u3 * v4 * v6 * v17 + 24 * u * v3 * v4 * v6 * v17 -
                    6 * u * v34 * v6 * v17 + 2 * u4 * v36 * v17 -
                    6 * u * v4 * v36 * v17 + 2 * u3 * v46 * v17 -
                    6 * u * v3 * v46 * v17 + 2 * u * v346 * v17 - u146 * v37 +
                    2 * u46 * v1 * v37 + 2 * u16 * v4 * v37 -
                    6 * u6 * v1 * v4 * v37 + 2 * u6 * v14 * v37 +
                    2 * u14 * v6 * v37 - 6 * u4 * v1 * v6 * v37 -
                    6 * u1 * v4 * v6 * v37 + 24 * u * v1 * v4 * v6 * v37 -
                    6 * u * v14 * v6 * v37 + 2 * u4 * v16 * v37 -
                    6 * u * v4 * v16 * v37 + 2 * u1 * v46 * v37 -
                    6 * u * v1 * v46 * v37 + 2 * u * v146 * v37 - u46 * v137 +
                    2 * u6 * v4 * v137 + 2 * u4 * v6 * v137 -
                    6 * u * v4 * v6 * v137 + 2 * u * v46 * v137 - u136 * v47 +
                    2 * u36 * v1 * v47 + 2 * u16 * v3 * v47 -
                    6 * u6 * v1 * v3 * v47 + 2 * u6 * v13 * v47 +
                    2 * u13 * v6 * v47 - 6 * u3 * v1 * v6 * v47 -
                    6 * u1 * v3 * v6 * v47 + 24 * u * v1 * v3 * v6 * v47 -
                    6 * u * v13 * v6 * v47 + 2 * u3 * v16 * v47 -
                    6 * u * v3 * v16 * v47 + 2 * u1 * v36 * v47 -
                    6 * u * v1 * v36 * v47 + 2 * u * v136 * v47 - u36 * v147 +
                    2 * u6 * v3 * v147 + 2 * u3 * v6 * v147 -
                    6 * u * v3 * v6 * v147 + 2 * u * v36 * v147 - u16 * v347 +
                    2 * u6 * v1 * v347 + 2 * u1 * v6 * v347 -
                    6 * u * v1 * v6 * v347 + 2 * u * v16 * v347 - u6 * v1347 +
                    2 * u * v6 * v1347 - u134 * v67 + 2 * u34 * v1 * v67 +
                    2 * u14 * v3 * v67 - 6 * u4 * v1 * v3 * v67 +
                    2 * u4 * v13 * v67 + 2 * u13 * v4 * v67 -
                    6 * u3 * v1 * v4 * v67 - 6 * u1 * v3 * v4 * v67 +
                    24 * u * v1 * v3 * v4 * v67 - 6 * u * v13 * v4 * v67 +
                    2 * u3 * v14 * v67 - 6 * u * v3 * v14 * v67 +
                    2 * u1 * v34 * v67 - 6 * u * v1 * v34 * v67 +
                    2 * u * v134 * v67 - u34 * v167 + 2 * u4 * v3 * v167 +
                    2 * u3 * v4 * v167 - 6 * u * v3 * v4 * v167 +
                    2 * u * v34 * v167 - u14 * v367 + 2 * u4 * v1 * v367 +
                    2 * u1 * v4 * v367 - 6 * u * v1 * v4 * v367 +
                    2 * u * v14 * v367 - u4 * v1367 + 2 * u * v4 * v1367 -
                    u13 * v467 + 2 * u3 * v1 * v467 + 2 * u1 * v3 * v467 -
                    6 * u * v1 * v3 * v467 + 2 * u * v13 * v467 - u3 * v1467 +
                    2 * u * v3 * v1467 - u1 * v3467 + 2 * u * v1 * v3467 -
                    u * v13467,
            .dual23467 =
                    u23467 - u3467 * v2 - u2467 * v3 + 2 * u467 * v2 * v3 -
                    u467 * v23 - u2367 * v4 + 2 * u367 * v2 * v4 +
                    2 * u267 * v3 * v4 - 6 * u67 * v2 * v3 * v4 +
                    2 * u67 * v23 * v4 - u367 * v24 + 2 * u67 * v3 * v24 -
                    u267 * v34 + 2 * u67 * v2 * v34 - u67 * v234 - u2347 * v6 +
                    2 * u347 * v2 * v6 + 2 * u247 * v3 * v6 -
                    6 * u47 * v2 * v3 * v6 + 2 * u47 * v23 * v6 +
                    2 * u237 * v4 * v6 - 6 * u37 * v2 * v4 * v6 -
                    6 * u27 * v3 * v4 * v6 + 24 * u7 * v2 * v3 * v4 * v6 -
                    6 * u7 * v23 * v4 * v6 + 2 * u37 * v24 * v6 -
                    6 * u7 * v3 * v24 * v6 + 2 * u27 * v34 * v6 -
                    6 * u7 * v2 * v34 * v6 + 2 * u7 * v234 * v6 - u347 * v26 +
                    2 * u47 * v3 * v26 + 2 * u37 * v4 * v26 -
                    6 * u7 * v3 * v4 * v26 + 2 * u7 * v34 * v26 - u247 * v36 +
                    2 * u47 * v2 * v36 + 2 * u27 * v4 * v36 -
                    6 * u7 * v2 * v4 * v36 + 2 * u7 * v24 * v36 - u47 * v236 +
                    2 * u7 * v4 * v236 - u237 * v46 + 2 * u37 * v2 * v46 +
                    2 * u27 * v3 * v46 - 6 * u7 * v2 * v3 * v46 +
                    2 * u7 * v23 * v46 - u37 * v246 + 2 * u7 * v3 * v246 -
                    u27 * v346 + 2 * u7 * v2 * v346 - u7 * v2346 - u2346 * v7 +
                    2 * u346 * v2 * v7 + 2 * u246 * v3 * v7 -
                    6 * u46 * v2 * v3 * v7 + 2 * u46 * v23 * v7 +
                    2 * u236 * v4 * v7 - 6 * u36 * v2 * v4 * v7 -
                    6 * u26 * v3 * v4 * v7 + 24 * u6 * v2 * v3 * v4 * v7 -
                    6 * u6 * v23 * v4 * v7 + 2 * u36 * v24 * v7 -
                    6 * u6 * v3 * v24 * v7 + 2 * u26 * v34 * v7 -
                    6 * u6 * v2 * v34 * v7 + 2 * u6 * v234 * v7 +
                    2 * u234 * v6 * v7 - 6 * u34 * v2 * v6 * v7 -
                    6 * u24 * v3 * v6 * v7 + 24 * u4 * v2 * v3 * v6 * v7 -
                    6 * u4 * v23 * v6 * v7 - 6 * u23 * v4 * v6 * v7 +
                    24 * u3 * v2 * v4 * v6 * v7 + 24 * u2 * v3 * v4 * v6 * v7 -
                    120 * u * v2 * v3 * v4 * v6 * v7 +
                    24 * u * v23 * v4 * v6 * v7 - 6 * u3 * v24 * v6 * v7 +
                    24 * u * v3 * v24 * v6 * v7 - 6 * u2 * v34 * v6 * v7 +
                    24 * u * v2 * v34 * v6 * v7 - 6 * u * v234 * v6 * v7 +
                    2 * u34 * v26 * v7 - 6 * u4 * v3 * v26 * v7 -
                    6 * u3 * v4 * v26 * v7 + 24 * u * v3 * v4 * v26 * v7 -
                    6 * u * v34 * v26 * v7 + 2 * u24 * v36 * v7 -
                    6 * u4 * v2 * v36 * v7 - 6 * u2 * v4 * v36 * v7 +
                    24 * u * v2 * v4 * v36 * v7 - 6 * u * v24 * v36 * v7 +
                    2 * u4 * v236 * v7 - 6 * u * v4 * v236 * v7 +
                    2 * u23 * v46 * v7 - 6 * u3 * v2 * v46 * v7 -
                    6 * u2 * v3 * v46 * v7 + 24 * u * v2 * v3 * v46 * v7 -
                    6 * u * v23 * v46 * v7 + 2 * u3 * v246 * v7 -
                    6 * u * v3 * v246 * v7 + 2 * u2 * v346 * v7 -
                    6 * u * v2 * v346 * v7 + 2 * u * v2346 * v7 - u346 * v27 +
                    2 * u46 * v3 * v27 + 2 * u36 * v4 * v27 -
                    6 * u6 * v3 * v4 * v27 + 2 * u6 * v34 * v27 +
                    2 * u34 * v6 * v27 - 6 * u4 * v3 * v6 * v27 -
                    6 * u3 * v4 * v6 * v27 + 24 * u * v3 * v4 * v6 * v27 -
                    6 * u * v34 * v6 * v27 + 2 * u4 * v36 * v27 -
                    6 * u * v4 * v36 * v27 + 2 * u3 * v46 * v27 -
                    6 * u * v3 * v46 * v27 + 2 * u * v346 * v27 - u246 * v37 +
                    2 * u46 * v2 * v37 + 2 * u26 * v4 * v37 -
                    6 * u6 * v2 * v4 * v37 + 2 * u6 * v24 * v37 +
                    2 * u24 * v6 * v37 - 6 * u4 * v2 * v6 * v37 -
                    6 * u2 * v4 * v6 * v37 + 24 * u * v2 * v4 * v6 * v37 -
                    6 * u * v24 * v6 * v37 + 2 * u4 * v26 * v37 -
                    6 * u * v4 * v26 * v37 + 2 * u2 * v46 * v37 -
                    6 * u * v2 * v46 * v37 + 2 * u * v246 * v37 - u46 * v237 +
                    2 * u6 * v4 * v237 + 2 * u4 * v6 * v237 -
                    6 * u * v4 * v6 * v237 + 2 * u * v46 * v237 - u236 * v47 +
                    2 * u36 * v2 * v47 + 2 * u26 * v3 * v47 -
                    6 * u6 * v2 * v3 * v47 + 2 * u6 * v23 * v47 +
                    2 * u23 * v6 * v47 - 6 * u3 * v2 * v6 * v47 -
                    6 * u2 * v3 * v6 * v47 + 24 * u * v2 * v3 * v6 * v47 -
                    6 * u * v23 * v6 * v47 + 2 * u3 * v26 * v47 -
                    6 * u * v3 * v26 * v47 + 2 * u2 * v36 * v47 -
                    6 * u * v2 * v36 * v47 + 2 * u * v236 * v47 - u36 * v247 +
                    2 * u6 * v3 * v247 + 2 * u3 * v6 * v247 -
                    6 * u * v3 * v6 * v247 + 2 * u * v36 * v247 - u26 * v347 +
                    2 * u6 * v2 * v347 + 2 * u2 * v6 * v347 -
                    6 * u * v2 * v6 * v347 + 2 * u * v26 * v347 - u6 * v2347 +
                    2 * u * v6 * v2347 - u234 * v67 + 2 * u34 * v2 * v67 +
                    2 * u24 * v3 * v67 - 6 * u4 * v2 * v3 * v67 +
                    2 * u4 * v23 * v67 + 2 * u23 * v4 * v67 -
                    6 * u3 * v2 * v4 * v67 - 6 * u2 * v3 * v4 * v67 +
                    24 * u * v2 * v3 * v4 * v67 - 6 * u * v23 * v4 * v67 +
                    2 * u3 * v24 * v67 - 6 * u * v3 * v24 * v67 +
                    2 * u2 * v34 * v67 - 6 * u * v2 * v34 * v67 +
                    2 * u * v234 * v67 - u34 * v267 + 2 * u4 * v3 * v267 +
                    2 * u3 * v4 * v267 - 6 * u * v3 * v4 * v267 +
                    2 * u * v34 * v267 - u24 * v367 + 2 * u4 * v2 * v367 +
                    2 * u2 * v4 * v367 - 6 * u * v2 * v4 * v367 +
                    2 * u * v24 * v367 - u4 * v2367 + 2 * u * v4 * v2367 -
                    u23 * v467 + 2 * u3 * v2 * v467 + 2 * u2 * v3 * v467 -
                    6 * u * v2 * v3 * v467 + 2 * u * v23 * v467 - u3 * v2467 +
                    2 * u * v3 * v2467 - u2 * v3467 + 2 * u * v2 * v3467 -
                    u * v23467,
            .dual123467 =
                    u123467 - u23467 * v1 - u13467 * v2 + 2 * u3467 * v1 * v2 -
                    u3467 * v12 - u12467 * v3 + 2 * u2467 * v1 * v3 +
                    2 * u1467 * v2 * v3 - 6 * u467 * v1 * v2 * v3 +
                    2 * u467 * v12 * v3 - u2467 * v13 + 2 * u467 * v2 * v13 -
                    u1467 * v23 + 2 * u467 * v1 * v23 - u467 * v123 -
                    u12367 * v4 + 2 * u2367 * v1 * v4 + 2 * u1367 * v2 * v4 -
                    6 * u367 * v1 * v2 * v4 + 2 * u367 * v12 * v4 +
                    2 * u1267 * v3 * v4 - 6 * u267 * v1 * v3 * v4 -
                    6 * u167 * v2 * v3 * v4 + 24 * u67 * v1 * v2 * v3 * v4 -
                    6 * u67 * v12 * v3 * v4 + 2 * u267 * v13 * v4 -
                    6 * u67 * v2 * v13 * v4 + 2 * u167 * v23 * v4 -
                    6 * u67 * v1 * v23 * v4 + 2 * u67 * v123 * v4 -
                    u2367 * v14 + 2 * u367 * v2 * v14 + 2 * u267 * v3 * v14 -
                    6 * u67 * v2 * v3 * v14 + 2 * u67 * v23 * v14 -
                    u1367 * v24 + 2 * u367 * v1 * v24 + 2 * u167 * v3 * v24 -
                    6 * u67 * v1 * v3 * v24 + 2 * u67 * v13 * v24 -
                    u367 * v124 + 2 * u67 * v3 * v124 - u1267 * v34 +
                    2 * u267 * v1 * v34 + 2 * u167 * v2 * v34 -
                    6 * u67 * v1 * v2 * v34 + 2 * u67 * v12 * v34 -
                    u267 * v134 + 2 * u67 * v2 * v134 - u167 * v234 +
                    2 * u67 * v1 * v234 - u67 * v1234 - u12347 * v6 +
                    2 * u2347 * v1 * v6 + 2 * u1347 * v2 * v6 -
                    6 * u347 * v1 * v2 * v6 + 2 * u347 * v12 * v6 +
                    2 * u1247 * v3 * v6 - 6 * u247 * v1 * v3 * v6 -
                    6 * u147 * v2 * v3 * v6 + 24 * u47 * v1 * v2 * v3 * v6 -
                    6 * u47 * v12 * v3 * v6 + 2 * u247 * v13 * v6 -
                    6 * u47 * v2 * v13 * v6 + 2 * u147 * v23 * v6 -
                    6 * u47 * v1 * v23 * v6 + 2 * u47 * v123 * v6 +
                    2 * u1237 * v4 * v6 - 6 * u237 * v1 * v4 * v6 -
                    6 * u137 * v2 * v4 * v6 + 24 * u37 * v1 * v2 * v4 * v6 -
                    6 * u37 * v12 * v4 * v6 - 6 * u127 * v3 * v4 * v6 +
                    24 * u27 * v1 * v3 * v4 * v6 +
                    24 * u17 * v2 * v3 * v4 * v6 -
                    120 * u7 * v1 * v2 * v3 * v4 * v6 +
                    24 * u7 * v12 * v3 * v4 * v6 - 6 * u27 * v13 * v4 * v6 +
                    24 * u7 * v2 * v13 * v4 * v6 - 6 * u17 * v23 * v4 * v6 +
                    24 * u7 * v1 * v23 * v4 * v6 - 6 * u7 * v123 * v4 * v6 +
                    2 * u237 * v14 * v6 - 6 * u37 * v2 * v14 * v6 -
                    6 * u27 * v3 * v14 * v6 + 24 * u7 * v2 * v3 * v14 * v6 -
                    6 * u7 * v23 * v14 * v6 + 2 * u137 * v24 * v6 -
                    6 * u37 * v1 * v24 * v6 - 6 * u17 * v3 * v24 * v6 +
                    24 * u7 * v1 * v3 * v24 * v6 - 6 * u7 * v13 * v24 * v6 +
                    2 * u37 * v124 * v6 - 6 * u7 * v3 * v124 * v6 +
                    2 * u127 * v34 * v6 - 6 * u27 * v1 * v34 * v6 -
                    6 * u17 * v2 * v34 * v6 + 24 * u7 * v1 * v2 * v34 * v6 -
                    6 * u7 * v12 * v34 * v6 + 2 * u27 * v134 * v6 -
                    6 * u7 * v2 * v134 * v6 + 2 * u17 * v234 * v6 -
                    6 * u7 * v1 * v234 * v6 + 2 * u7 * v1234 * v6 -
                    u2347 * v16 + 2 * u347 * v2 * v16 + 2 * u247 * v3 * v16 -
                    6 * u47 * v2 * v3 * v16 + 2 * u47 * v23 * v16 +
                    2 * u237 * v4 * v16 - 6 * u37 * v2 * v4 * v16 -
                    6 * u27 * v3 * v4 * v16 + 24 * u7 * v2 * v3 * v4 * v16 -
                    6 * u7 * v23 * v4 * v16 + 2 * u37 * v24 * v16 -
                    6 * u7 * v3 * v24 * v16 + 2 * u27 * v34 * v16 -
                    6 * u7 * v2 * v34 * v16 + 2 * u7 * v234 * v16 -
                    u1347 * v26 + 2 * u347 * v1 * v26 + 2 * u147 * v3 * v26 -
                    6 * u47 * v1 * v3 * v26 + 2 * u47 * v13 * v26 +
                    2 * u137 * v4 * v26 - 6 * u37 * v1 * v4 * v26 -
                    6 * u17 * v3 * v4 * v26 + 24 * u7 * v1 * v3 * v4 * v26 -
                    6 * u7 * v13 * v4 * v26 + 2 * u37 * v14 * v26 -
                    6 * u7 * v3 * v14 * v26 + 2 * u17 * v34 * v26 -
                    6 * u7 * v1 * v34 * v26 + 2 * u7 * v134 * v26 -
                    u347 * v126 + 2 * u47 * v3 * v126 + 2 * u37 * v4 * v126 -
                    6 * u7 * v3 * v4 * v126 + 2 * u7 * v34 * v126 -
                    u1247 * v36 + 2 * u247 * v1 * v36 + 2 * u147 * v2 * v36 -
                    6 * u47 * v1 * v2 * v36 + 2 * u47 * v12 * v36 +
                    2 * u127 * v4 * v36 - 6 * u27 * v1 * v4 * v36 -
                    6 * u17 * v2 * v4 * v36 + 24 * u7 * v1 * v2 * v4 * v36 -
                    6 * u7 * v12 * v4 * v36 + 2 * u27 * v14 * v36 -
                    6 * u7 * v2 * v14 * v36 + 2 * u17 * v24 * v36 -
                    6 * u7 * v1 * v24 * v36 + 2 * u7 * v124 * v36 -
                    u247 * v136 + 2 * u47 * v2 * v136 + 2 * u27 * v4 * v136 -
                    6 * u7 * v2 * v4 * v136 + 2 * u7 * v24 * v136 -
                    u147 * v236 + 2 * u47 * v1 * v236 + 2 * u17 * v4 * v236 -
                    6 * u7 * v1 * v4 * v236 + 2 * u7 * v14 * v236 -
                    u47 * v1236 + 2 * u7 * v4 * v1236 - u1237 * v46 +
                    2 * u237 * v1 * v46 + 2 * u137 * v2 * v46 -
                    6 * u37 * v1 * v2 * v46 + 2 * u37 * v12 * v46 +
                    2 * u127 * v3 * v46 - 6 * u27 * v1 * v3 * v46 -
                    6 * u17 * v2 * v3 * v46 + 24 * u7 * v1 * v2 * v3 * v46 -
                    6 * u7 * v12 * v3 * v46 + 2 * u27 * v13 * v46 -
                    6 * u7 * v2 * v13 * v46 + 2 * u17 * v23 * v46 -
                    6 * u7 * v1 * v23 * v46 + 2 * u7 * v123 * v46 -
                    u237 * v146 + 2 * u37 * v2 * v146 + 2 * u27 * v3 * v146 -
                    6 * u7 * v2 * v3 * v146 + 2 * u7 * v23 * v146 -
                    u137 * v246 + 2 * u37 * v1 * v246 + 2 * u17 * v3 * v246 -
                    6 * u7 * v1 * v3 * v246 + 2 * u7 * v13 * v246 -
                    u37 * v1246 + 2 * u7 * v3 * v1246 - u127 * v346 +
                    2 * u27 * v1 * v346 + 2 * u17 * v2 * v346 -
                    6 * u7 * v1 * v2 * v346 + 2 * u7 * v12 * v346 -
                    u27 * v1346 + 2 * u7 * v2 * v1346 - u17 * v2346 +
                    2 * u7 * v1 * v2346 - u7 * v12346 - u12346 * v7 +
                    2 * u2346 * v1 * v7 + 2 * u1346 * v2 * v7 -
                    6 * u346 * v1 * v2 * v7 + 2 * u346 * v12 * v7 +
                    2 * u1246 * v3 * v7 - 6 * u246 * v1 * v3 * v7 -
                    6 * u146 * v2 * v3 * v7 + 24 * u46 * v1 * v2 * v3 * v7 -
                    6 * u46 * v12 * v3 * v7 + 2 * u246 * v13 * v7 -
                    6 * u46 * v2 * v13 * v7 + 2 * u146 * v23 * v7 -
                    6 * u46 * v1 * v23 * v7 + 2 * u46 * v123 * v7 +
                    2 * u1236 * v4 * v7 - 6 * u236 * v1 * v4 * v7 -
                    6 * u136 * v2 * v4 * v7 + 24 * u36 * v1 * v2 * v4 * v7 -
                    6 * u36 * v12 * v4 * v7 - 6 * u126 * v3 * v4 * v7 +
                    24 * u26 * v1 * v3 * v4 * v7 +
                    24 * u16 * v2 * v3 * v4 * v7 -
                    120 * u6 * v1 * v2 * v3 * v4 * v7 +
                    24 * u6 * v12 * v3 * v4 * v7 - 6 * u26 * v13 * v4 * v7 +
                    24 * u6 * v2 * v13 * v4 * v7 - 6 * u16 * v23 * v4 * v7 +
                    24 * u6 * v1 * v23 * v4 * v7 - 6 * u6 * v123 * v4 * v7 +
                    2 * u236 * v14 * v7 - 6 * u36 * v2 * v14 * v7 -
                    6 * u26 * v3 * v14 * v7 + 24 * u6 * v2 * v3 * v14 * v7 -
                    6 * u6 * v23 * v14 * v7 + 2 * u136 * v24 * v7 -
                    6 * u36 * v1 * v24 * v7 - 6 * u16 * v3 * v24 * v7 +
                    24 * u6 * v1 * v3 * v24 * v7 - 6 * u6 * v13 * v24 * v7 +
                    2 * u36 * v124 * v7 - 6 * u6 * v3 * v124 * v7 +
                    2 * u126 * v34 * v7 - 6 * u26 * v1 * v34 * v7 -
                    6 * u16 * v2 * v34 * v7 + 24 * u6 * v1 * v2 * v34 * v7 -
                    6 * u6 * v12 * v34 * v7 + 2 * u26 * v134 * v7 -
                    6 * u6 * v2 * v134 * v7 + 2 * u16 * v234 * v7 -
                    6 * u6 * v1 * v234 * v7 + 2 * u6 * v1234 * v7 +
                    2 * u1234 * v6 * v7 - 6 * u234 * v1 * v6 * v7 -
                    6 * u134 * v2 * v6 * v7 + 24 * u34 * v1 * v2 * v6 * v7 -
                    6 * u34 * v12 * v6 * v7 - 6 * u124 * v3 * v6 * v7 +
                    24 * u24 * v1 * v3 * v6 * v7 +
                    24 * u14 * v2 * v3 * v6 * v7 -
                    120 * u4 * v1 * v2 * v3 * v6 * v7 +
                    24 * u4 * v12 * v3 * v6 * v7 - 6 * u24 * v13 * v6 * v7 +
                    24 * u4 * v2 * v13 * v6 * v7 - 6 * u14 * v23 * v6 * v7 +
                    24 * u4 * v1 * v23 * v6 * v7 - 6 * u4 * v123 * v6 * v7 -
                    6 * u123 * v4 * v6 * v7 + 24 * u23 * v1 * v4 * v6 * v7 +
                    24 * u13 * v2 * v4 * v6 * v7 -
                    120 * u3 * v1 * v2 * v4 * v6 * v7 +
                    24 * u3 * v12 * v4 * v6 * v7 +
                    24 * u12 * v3 * v4 * v6 * v7 -
                    120 * u2 * v1 * v3 * v4 * v6 * v7 -
                    120 * u1 * v2 * v3 * v4 * v6 * v7 +
                    720 * u * v1 * v2 * v3 * v4 * v6 * v7 -
                    120 * u * v12 * v3 * v4 * v6 * v7 +
                    24 * u2 * v13 * v4 * v6 * v7 -
                    120 * u * v2 * v13 * v4 * v6 * v7 +
                    24 * u1 * v23 * v4 * v6 * v7 -
                    120 * u * v1 * v23 * v4 * v6 * v7 +
                    24 * u * v123 * v4 * v6 * v7 - 6 * u23 * v14 * v6 * v7 +
                    24 * u3 * v2 * v14 * v6 * v7 +
                    24 * u2 * v3 * v14 * v6 * v7 -
                    120 * u * v2 * v3 * v14 * v6 * v7 +
                    24 * u * v23 * v14 * v6 * v7 - 6 * u13 * v24 * v6 * v7 +
                    24 * u3 * v1 * v24 * v6 * v7 +
                    24 * u1 * v3 * v24 * v6 * v7 -
                    120 * u * v1 * v3 * v24 * v6 * v7 +
                    24 * u * v13 * v24 * v6 * v7 - 6 * u3 * v124 * v6 * v7 +
                    24 * u * v3 * v124 * v6 * v7 - 6 * u12 * v34 * v6 * v7 +
                    24 * u2 * v1 * v34 * v6 * v7 +
                    24 * u1 * v2 * v34 * v6 * v7 -
                    120 * u * v1 * v2 * v34 * v6 * v7 +
                    24 * u * v12 * v34 * v6 * v7 - 6 * u2 * v134 * v6 * v7 +
                    24 * u * v2 * v134 * v6 * v7 - 6 * u1 * v234 * v6 * v7 +
                    24 * u * v1 * v234 * v6 * v7 - 6 * u * v1234 * v6 * v7 +
                    2 * u234 * v16 * v7 - 6 * u34 * v2 * v16 * v7 -
                    6 * u24 * v3 * v16 * v7 + 24 * u4 * v2 * v3 * v16 * v7 -
                    6 * u4 * v23 * v16 * v7 - 6 * u23 * v4 * v16 * v7 +
                    24 * u3 * v2 * v4 * v16 * v7 +
                    24 * u2 * v3 * v4 * v16 * v7 -
                    120 * u * v2 * v3 * v4 * v16 * v7 +
                    24 * u * v23 * v4 * v16 * v7 - 6 * u3 * v24 * v16 * v7 +
                    24 * u * v3 * v24 * v16 * v7 - 6 * u2 * v34 * v16 * v7 +
                    24 * u * v2 * v34 * v16 * v7 - 6 * u * v234 * v16 * v7 +
                    2 * u134 * v26 * v7 - 6 * u34 * v1 * v26 * v7 -
                    6 * u14 * v3 * v26 * v7 + 24 * u4 * v1 * v3 * v26 * v7 -
                    6 * u4 * v13 * v26 * v7 - 6 * u13 * v4 * v26 * v7 +
                    24 * u3 * v1 * v4 * v26 * v7 +
                    24 * u1 * v3 * v4 * v26 * v7 -
                    120 * u * v1 * v3 * v4 * v26 * v7 +
                    24 * u * v13 * v4 * v26 * v7 - 6 * u3 * v14 * v26 * v7 +
                    24 * u * v3 * v14 * v26 * v7 - 6 * u1 * v34 * v26 * v7 +
                    24 * u * v1 * v34 * v26 * v7 - 6 * u * v134 * v26 * v7 +
                    2 * u34 * v126 * v7 - 6 * u4 * v3 * v126 * v7 -
                    6 * u3 * v4 * v126 * v7 + 24 * u * v3 * v4 * v126 * v7 -
                    6 * u * v34 * v126 * v7 + 2 * u124 * v36 * v7 -
                    6 * u24 * v1 * v36 * v7 - 6 * u14 * v2 * v36 * v7 +
                    24 * u4 * v1 * v2 * v36 * v7 - 6 * u4 * v12 * v36 * v7 -
                    6 * u12 * v4 * v36 * v7 + 24 * u2 * v1 * v4 * v36 * v7 +
                    24 * u1 * v2 * v4 * v36 * v7 -
                    120 * u * v1 * v2 * v4 * v36 * v7 +
                    24 * u * v12 * v4 * v36 * v7 - 6 * u2 * v14 * v36 * v7 +
                    24 * u * v2 * v14 * v36 * v7 - 6 * u1 * v24 * v36 * v7 +
                    24 * u * v1 * v24 * v36 * v7 - 6 * u * v124 * v36 * v7 +
                    2 * u24 * v136 * v7 - 6 * u4 * v2 * v136 * v7 -
                    6 * u2 * v4 * v136 * v7 + 24 * u * v2 * v4 * v136 * v7 -
                    6 * u * v24 * v136 * v7 + 2 * u14 * v236 * v7 -
                    6 * u4 * v1 * v236 * v7 - 6 * u1 * v4 * v236 * v7 +
                    24 * u * v1 * v4 * v236 * v7 - 6 * u * v14 * v236 * v7 +
                    2 * u4 * v1236 * v7 - 6 * u * v4 * v1236 * v7 +
                    2 * u123 * v46 * v7 - 6 * u23 * v1 * v46 * v7 -
                    6 * u13 * v2 * v46 * v7 + 24 * u3 * v1 * v2 * v46 * v7 -
                    6 * u3 * v12 * v46 * v7 - 6 * u12 * v3 * v46 * v7 +
                    24 * u2 * v1 * v3 * v46 * v7 +
                    24 * u1 * v2 * v3 * v46 * v7 -
                    120 * u * v1 * v2 * v3 * v46 * v7 +
                    24 * u * v12 * v3 * v46 * v7 - 6 * u2 * v13 * v46 * v7 +
                    24 * u * v2 * v13 * v46 * v7 - 6 * u1 * v23 * v46 * v7 +
                    24 * u * v1 * v23 * v46 * v7 - 6 * u * v123 * v46 * v7 +
                    2 * u23 * v146 * v7 - 6 * u3 * v2 * v146 * v7 -
                    6 * u2 * v3 * v146 * v7 + 24 * u * v2 * v3 * v146 * v7 -
                    6 * u * v23 * v146 * v7 + 2 * u13 * v246 * v7 -
                    6 * u3 * v1 * v246 * v7 - 6 * u1 * v3 * v246 * v7 +
                    24 * u * v1 * v3 * v246 * v7 - 6 * u * v13 * v246 * v7 +
                    2 * u3 * v1246 * v7 - 6 * u * v3 * v1246 * v7 +
                    2 * u12 * v346 * v7 - 6 * u2 * v1 * v346 * v7 -
                    6 * u1 * v2 * v346 * v7 + 24 * u * v1 * v2 * v346 * v7 -
                    6 * u * v12 * v346 * v7 + 2 * u2 * v1346 * v7 -
                    6 * u * v2 * v1346 * v7 + 2 * u1 * v2346 * v7 -
                    6 * u * v1 * v2346 * v7 + 2 * u * v12346 * v7 -
                    u2346 * v17 + 2 * u346 * v2 * v17 + 2 * u246 * v3 * v17 -
                    6 * u46 * v2 * v3 * v17 + 2 * u46 * v23 * v17 +
                    2 * u236 * v4 * v17 - 6 * u36 * v2 * v4 * v17 -
                    6 * u26 * v3 * v4 * v17 + 24 * u6 * v2 * v3 * v4 * v17 -
                    6 * u6 * v23 * v4 * v17 + 2 * u36 * v24 * v17 -
                    6 * u6 * v3 * v24 * v17 + 2 * u26 * v34 * v17 -
                    6 * u6 * v2 * v34 * v17 + 2 * u6 * v234 * v17 +
                    2 * u234 * v6 * v17 - 6 * u34 * v2 * v6 * v17 -
                    6 * u24 * v3 * v6 * v17 + 24 * u4 * v2 * v3 * v6 * v17 -
                    6 * u4 * v23 * v6 * v17 - 6 * u23 * v4 * v6 * v17 +
                    24 * u3 * v2 * v4 * v6 * v17 +
                    24 * u2 * v3 * v4 * v6 * v17 -
                    120 * u * v2 * v3 * v4 * v6 * v17 +
                    24 * u * v23 * v4 * v6 * v17 - 6 * u3 * v24 * v6 * v17 +
                    24 * u * v3 * v24 * v6 * v17 - 6 * u2 * v34 * v6 * v17 +
                    24 * u * v2 * v34 * v6 * v17 - 6 * u * v234 * v6 * v17 +
                    2 * u34 * v26 * v17 - 6 * u4 * v3 * v26 * v17 -
                    6 * u3 * v4 * v26 * v17 + 24 * u * v3 * v4 * v26 * v17 -
                    6 * u * v34 * v26 * v17 + 2 * u24 * v36 * v17 -
                    6 * u4 * v2 * v36 * v17 - 6 * u2 * v4 * v36 * v17 +
                    24 * u * v2 * v4 * v36 * v17 - 6 * u * v24 * v36 * v17 +
                    2 * u4 * v236 * v17 - 6 * u * v4 * v236 * v17 +
                    2 * u23 * v46 * v17 - 6 * u3 * v2 * v46 * v17 -
                    6 * u2 * v3 * v46 * v17 + 24 * u * v2 * v3 * v46 * v17 -
                    6 * u * v23 * v46 * v17 + 2 * u3 * v246 * v17 -
                    6 * u * v3 * v246 * v17 + 2 * u2 * v346 * v17 -
                    6 * u * v2 * v346 * v17 + 2 * u * v2346 * v17 -
                    u1346 * v27 + 2 * u346 * v1 * v27 + 2 * u146 * v3 * v27 -
                    6 * u46 * v1 * v3 * v27 + 2 * u46 * v13 * v27 +
                    2 * u136 * v4 * v27 - 6 * u36 * v1 * v4 * v27 -
                    6 * u16 * v3 * v4 * v27 + 24 * u6 * v1 * v3 * v4 * v27 -
                    6 * u6 * v13 * v4 * v27 + 2 * u36 * v14 * v27 -
                    6 * u6 * v3 * v14 * v27 + 2 * u16 * v34 * v27 -
                    6 * u6 * v1 * v34 * v27 + 2 * u6 * v134 * v27 +
                    2 * u134 * v6 * v27 - 6 * u34 * v1 * v6 * v27 -
                    6 * u14 * v3 * v6 * v27 + 24 * u4 * v1 * v3 * v6 * v27 -
                    6 * u4 * v13 * v6 * v27 - 6 * u13 * v4 * v6 * v27 +
                    24 * u3 * v1 * v4 * v6 * v27 +
                    24 * u1 * v3 * v4 * v6 * v27 -
                    120 * u * v1 * v3 * v4 * v6 * v27 +
                    24 * u * v13 * v4 * v6 * v27 - 6 * u3 * v14 * v6 * v27 +
                    24 * u * v3 * v14 * v6 * v27 - 6 * u1 * v34 * v6 * v27 +
                    24 * u * v1 * v34 * v6 * v27 - 6 * u * v134 * v6 * v27 +
                    2 * u34 * v16 * v27 - 6 * u4 * v3 * v16 * v27 -
                    6 * u3 * v4 * v16 * v27 + 24 * u * v3 * v4 * v16 * v27 -
                    6 * u * v34 * v16 * v27 + 2 * u14 * v36 * v27 -
                    6 * u4 * v1 * v36 * v27 - 6 * u1 * v4 * v36 * v27 +
                    24 * u * v1 * v4 * v36 * v27 - 6 * u * v14 * v36 * v27 +
                    2 * u4 * v136 * v27 - 6 * u * v4 * v136 * v27 +
                    2 * u13 * v46 * v27 - 6 * u3 * v1 * v46 * v27 -
                    6 * u1 * v3 * v46 * v27 + 24 * u * v1 * v3 * v46 * v27 -
                    6 * u * v13 * v46 * v27 + 2 * u3 * v146 * v27 -
                    6 * u * v3 * v146 * v27 + 2 * u1 * v346 * v27 -
                    6 * u * v1 * v346 * v27 + 2 * u * v1346 * v27 -
                    u346 * v127 + 2 * u46 * v3 * v127 + 2 * u36 * v4 * v127 -
                    6 * u6 * v3 * v4 * v127 + 2 * u6 * v34 * v127 +
                    2 * u34 * v6 * v127 - 6 * u4 * v3 * v6 * v127 -
                    6 * u3 * v4 * v6 * v127 + 24 * u * v3 * v4 * v6 * v127 -
                    6 * u * v34 * v6 * v127 + 2 * u4 * v36 * v127 -
                    6 * u * v4 * v36 * v127 + 2 * u3 * v46 * v127 -
                    6 * u * v3 * v46 * v127 + 2 * u * v346 * v127 -
                    u1246 * v37 + 2 * u246 * v1 * v37 + 2 * u146 * v2 * v37 -
                    6 * u46 * v1 * v2 * v37 + 2 * u46 * v12 * v37 +
                    2 * u126 * v4 * v37 - 6 * u26 * v1 * v4 * v37 -
                    6 * u16 * v2 * v4 * v37 + 24 * u6 * v1 * v2 * v4 * v37 -
                    6 * u6 * v12 * v4 * v37 + 2 * u26 * v14 * v37 -
                    6 * u6 * v2 * v14 * v37 + 2 * u16 * v24 * v37 -
                    6 * u6 * v1 * v24 * v37 + 2 * u6 * v124 * v37 +
                    2 * u124 * v6 * v37 - 6 * u24 * v1 * v6 * v37 -
                    6 * u14 * v2 * v6 * v37 + 24 * u4 * v1 * v2 * v6 * v37 -
                    6 * u4 * v12 * v6 * v37 - 6 * u12 * v4 * v6 * v37 +
                    24 * u2 * v1 * v4 * v6 * v37 +
                    24 * u1 * v2 * v4 * v6 * v37 -
                    120 * u * v1 * v2 * v4 * v6 * v37 +
                    24 * u * v12 * v4 * v6 * v37 - 6 * u2 * v14 * v6 * v37 +
                    24 * u * v2 * v14 * v6 * v37 - 6 * u1 * v24 * v6 * v37 +
                    24 * u * v1 * v24 * v6 * v37 - 6 * u * v124 * v6 * v37 +
                    2 * u24 * v16 * v37 - 6 * u4 * v2 * v16 * v37 -
                    6 * u2 * v4 * v16 * v37 + 24 * u * v2 * v4 * v16 * v37 -
                    6 * u * v24 * v16 * v37 + 2 * u14 * v26 * v37 -
                    6 * u4 * v1 * v26 * v37 - 6 * u1 * v4 * v26 * v37 +
                    24 * u * v1 * v4 * v26 * v37 - 6 * u * v14 * v26 * v37 +
                    2 * u4 * v126 * v37 - 6 * u * v4 * v126 * v37 +
                    2 * u12 * v46 * v37 - 6 * u2 * v1 * v46 * v37 -
                    6 * u1 * v2 * v46 * v37 + 24 * u * v1 * v2 * v46 * v37 -
                    6 * u * v12 * v46 * v37 + 2 * u2 * v146 * v37 -
                    6 * u * v2 * v146 * v37 + 2 * u1 * v246 * v37 -
                    6 * u * v1 * v246 * v37 + 2 * u * v1246 * v37 -
                    u246 * v137 + 2 * u46 * v2 * v137 + 2 * u26 * v4 * v137 -
                    6 * u6 * v2 * v4 * v137 + 2 * u6 * v24 * v137 +
                    2 * u24 * v6 * v137 - 6 * u4 * v2 * v6 * v137 -
                    6 * u2 * v4 * v6 * v137 + 24 * u * v2 * v4 * v6 * v137 -
                    6 * u * v24 * v6 * v137 + 2 * u4 * v26 * v137 -
                    6 * u * v4 * v26 * v137 + 2 * u2 * v46 * v137 -
                    6 * u * v2 * v46 * v137 + 2 * u * v246 * v137 -
                    u146 * v237 + 2 * u46 * v1 * v237 + 2 * u16 * v4 * v237 -
                    6 * u6 * v1 * v4 * v237 + 2 * u6 * v14 * v237 +
                    2 * u14 * v6 * v237 - 6 * u4 * v1 * v6 * v237 -
                    6 * u1 * v4 * v6 * v237 + 24 * u * v1 * v4 * v6 * v237 -
                    6 * u * v14 * v6 * v237 + 2 * u4 * v16 * v237 -
                    6 * u * v4 * v16 * v237 + 2 * u1 * v46 * v237 -
                    6 * u * v1 * v46 * v237 + 2 * u * v146 * v237 -
                    u46 * v1237 + 2 * u6 * v4 * v1237 + 2 * u4 * v6 * v1237 -
                    6 * u * v4 * v6 * v1237 + 2 * u * v46 * v1237 -
                    u1236 * v47 + 2 * u236 * v1 * v47 + 2 * u136 * v2 * v47 -
                    6 * u36 * v1 * v2 * v47 + 2 * u36 * v12 * v47 +
                    2 * u126 * v3 * v47 - 6 * u26 * v1 * v3 * v47 -
                    6 * u16 * v2 * v3 * v47 + 24 * u6 * v1 * v2 * v3 * v47 -
                    6 * u6 * v12 * v3 * v47 + 2 * u26 * v13 * v47 -
                    6 * u6 * v2 * v13 * v47 + 2 * u16 * v23 * v47 -
                    6 * u6 * v1 * v23 * v47 + 2 * u6 * v123 * v47 +
                    2 * u123 * v6 * v47 - 6 * u23 * v1 * v6 * v47 -
                    6 * u13 * v2 * v6 * v47 + 24 * u3 * v1 * v2 * v6 * v47 -
                    6 * u3 * v12 * v6 * v47 - 6 * u12 * v3 * v6 * v47 +
                    24 * u2 * v1 * v3 * v6 * v47 +
                    24 * u1 * v2 * v3 * v6 * v47 -
                    120 * u * v1 * v2 * v3 * v6 * v47 +
                    24 * u * v12 * v3 * v6 * v47 - 6 * u2 * v13 * v6 * v47 +
                    24 * u * v2 * v13 * v6 * v47 - 6 * u1 * v23 * v6 * v47 +
                    24 * u * v1 * v23 * v6 * v47 - 6 * u * v123 * v6 * v47 +
                    2 * u23 * v16 * v47 - 6 * u3 * v2 * v16 * v47 -
                    6 * u2 * v3 * v16 * v47 + 24 * u * v2 * v3 * v16 * v47 -
                    6 * u * v23 * v16 * v47 + 2 * u13 * v26 * v47 -
                    6 * u3 * v1 * v26 * v47 - 6 * u1 * v3 * v26 * v47 +
                    24 * u * v1 * v3 * v26 * v47 - 6 * u * v13 * v26 * v47 +
                    2 * u3 * v126 * v47 - 6 * u * v3 * v126 * v47 +
                    2 * u12 * v36 * v47 - 6 * u2 * v1 * v36 * v47 -
                    6 * u1 * v2 * v36 * v47 + 24 * u * v1 * v2 * v36 * v47 -
                    6 * u * v12 * v36 * v47 + 2 * u2 * v136 * v47 -
                    6 * u * v2 * v136 * v47 + 2 * u1 * v236 * v47 -
                    6 * u * v1 * v236 * v47 + 2 * u * v1236 * v47 -
                    u236 * v147 + 2 * u36 * v2 * v147 + 2 * u26 * v3 * v147 -
                    6 * u6 * v2 * v3 * v147 + 2 * u6 * v23 * v147 +
                    2 * u23 * v6 * v147 - 6 * u3 * v2 * v6 * v147 -
                    6 * u2 * v3 * v6 * v147 + 24 * u * v2 * v3 * v6 * v147 -
                    6 * u * v23 * v6 * v147 + 2 * u3 * v26 * v147 -
                    6 * u * v3 * v26 * v147 + 2 * u2 * v36 * v147 -
                    6 * u * v2 * v36 * v147 + 2 * u * v236 * v147 -
                    u136 * v247 + 2 * u36 * v1 * v247 + 2 * u16 * v3 * v247 -
                    6 * u6 * v1 * v3 * v247 + 2 * u6 * v13 * v247 +
                    2 * u13 * v6 * v247 - 6 * u3 * v1 * v6 * v247 -
                    6 * u1 * v3 * v6 * v247 + 24 * u * v1 * v3 * v6 * v247 -
                    6 * u * v13 * v6 * v247 + 2 * u3 * v16 * v247 -
                    6 * u * v3 * v16 * v247 + 2 * u1 * v36 * v247 -
                    6 * u * v1 * v36 * v247 + 2 * u * v136 * v247 -
                    u36 * v1247 + 2 * u6 * v3 * v1247 + 2 * u3 * v6 * v1247 -
                    6 * u * v3 * v6 * v1247 + 2 * u * v36 * v1247 -
                    u126 * v347 + 2 * u26 * v1 * v347 + 2 * u16 * v2 * v347 -
                    6 * u6 * v1 * v2 * v347 + 2 * u6 * v12 * v347 +
                    2 * u12 * v6 * v347 - 6 * u2 * v1 * v6 * v347 -
                    6 * u1 * v2 * v6 * v347 + 24 * u * v1 * v2 * v6 * v347 -
                    6 * u * v12 * v6 * v347 + 2 * u2 * v16 * v347 -
                    6 * u * v2 * v16 * v347 + 2 * u1 * v26 * v347 -
                    6 * u * v1 * v26 * v347 + 2 * u * v126 * v347 -
                    u26 * v1347 + 2 * u6 * v2 * v1347 + 2 * u2 * v6 * v1347 -
                    6 * u * v2 * v6 * v1347 + 2 * u * v26 * v1347 -
                    u16 * v2347 + 2 * u6 * v1 * v2347 + 2 * u1 * v6 * v2347 -
                    6 * u * v1 * v6 * v2347 + 2 * u * v16 * v2347 -
                    u6 * v12347 + 2 * u * v6 * v12347 - u1234 * v67 +
                    2 * u234 * v1 * v67 + 2 * u134 * v2 * v67 -
                    6 * u34 * v1 * v2 * v67 + 2 * u34 * v12 * v67 +
                    2 * u124 * v3 * v67 - 6 * u24 * v1 * v3 * v67 -
                    6 * u14 * v2 * v3 * v67 + 24 * u4 * v1 * v2 * v3 * v67 -
                    6 * u4 * v12 * v3 * v67 + 2 * u24 * v13 * v67 -
                    6 * u4 * v2 * v13 * v67 + 2 * u14 * v23 * v67 -
                    6 * u4 * v1 * v23 * v67 + 2 * u4 * v123 * v67 +
                    2 * u123 * v4 * v67 - 6 * u23 * v1 * v4 * v67 -
                    6 * u13 * v2 * v4 * v67 + 24 * u3 * v1 * v2 * v4 * v67 -
                    6 * u3 * v12 * v4 * v67 - 6 * u12 * v3 * v4 * v67 +
                    24 * u2 * v1 * v3 * v4 * v67 +
                    24 * u1 * v2 * v3 * v4 * v67 -
                    120 * u * v1 * v2 * v3 * v4 * v67 +
                    24 * u * v12 * v3 * v4 * v67 - 6 * u2 * v13 * v4 * v67 +
                    24 * u * v2 * v13 * v4 * v67 - 6 * u1 * v23 * v4 * v67 +
                    24 * u * v1 * v23 * v4 * v67 - 6 * u * v123 * v4 * v67 +
                    2 * u23 * v14 * v67 - 6 * u3 * v2 * v14 * v67 -
                    6 * u2 * v3 * v14 * v67 + 24 * u * v2 * v3 * v14 * v67 -
                    6 * u * v23 * v14 * v67 + 2 * u13 * v24 * v67 -
                    6 * u3 * v1 * v24 * v67 - 6 * u1 * v3 * v24 * v67 +
                    24 * u * v1 * v3 * v24 * v67 - 6 * u * v13 * v24 * v67 +
                    2 * u3 * v124 * v67 - 6 * u * v3 * v124 * v67 +
                    2 * u12 * v34 * v67 - 6 * u2 * v1 * v34 * v67 -
                    6 * u1 * v2 * v34 * v67 + 24 * u * v1 * v2 * v34 * v67 -
                    6 * u * v12 * v34 * v67 + 2 * u2 * v134 * v67 -
                    6 * u * v2 * v134 * v67 + 2 * u1 * v234 * v67 -
                    6 * u * v1 * v234 * v67 + 2 * u * v1234 * v67 -
                    u234 * v167 + 2 * u34 * v2 * v167 + 2 * u24 * v3 * v167 -
                    6 * u4 * v2 * v3 * v167 + 2 * u4 * v23 * v167 +
                    2 * u23 * v4 * v167 - 6 * u3 * v2 * v4 * v167 -
                    6 * u2 * v3 * v4 * v167 + 24 * u * v2 * v3 * v4 * v167 -
                    6 * u * v23 * v4 * v167 + 2 * u3 * v24 * v167 -
                    6 * u * v3 * v24 * v167 + 2 * u2 * v34 * v167 -
                    6 * u * v2 * v34 * v167 + 2 * u * v234 * v167 -
                    u134 * v267 + 2 * u34 * v1 * v267 + 2 * u14 * v3 * v267 -
                    6 * u4 * v1 * v3 * v267 + 2 * u4 * v13 * v267 +
                    2 * u13 * v4 * v267 - 6 * u3 * v1 * v4 * v267 -
                    6 * u1 * v3 * v4 * v267 + 24 * u * v1 * v3 * v4 * v267 -
                    6 * u * v13 * v4 * v267 + 2 * u3 * v14 * v267 -
                    6 * u * v3 * v14 * v267 + 2 * u1 * v34 * v267 -
                    6 * u * v1 * v34 * v267 + 2 * u * v134 * v267 -
                    u34 * v1267 + 2 * u4 * v3 * v1267 + 2 * u3 * v4 * v1267 -
                    6 * u * v3 * v4 * v1267 + 2 * u * v34 * v1267 -
                    u124 * v367 + 2 * u24 * v1 * v367 + 2 * u14 * v2 * v367 -
                    6 * u4 * v1 * v2 * v367 + 2 * u4 * v12 * v367 +
                    2 * u12 * v4 * v367 - 6 * u2 * v1 * v4 * v367 -
                    6 * u1 * v2 * v4 * v367 + 24 * u * v1 * v2 * v4 * v367 -
                    6 * u * v12 * v4 * v367 + 2 * u2 * v14 * v367 -
                    6 * u * v2 * v14 * v367 + 2 * u1 * v24 * v367 -
                    6 * u * v1 * v24 * v367 + 2 * u * v124 * v367 -
                    u24 * v1367 + 2 * u4 * v2 * v1367 + 2 * u2 * v4 * v1367 -
                    6 * u * v2 * v4 * v1367 + 2 * u * v24 * v1367 -
                    u14 * v2367 + 2 * u4 * v1 * v2367 + 2 * u1 * v4 * v2367 -
                    6 * u * v1 * v4 * v2367 + 2 * u * v14 * v2367 -
                    u4 * v12367 + 2 * u * v4 * v12367 - u123 * v467 +
                    2 * u23 * v1 * v467 + 2 * u13 * v2 * v467 -
                    6 * u3 * v1 * v2 * v467 + 2 * u3 * v12 * v467 +
                    2 * u12 * v3 * v467 - 6 * u2 * v1 * v3 * v467 -
                    6 * u1 * v2 * v3 * v467 + 24 * u * v1 * v2 * v3 * v467 -
                    6 * u * v12 * v3 * v467 + 2 * u2 * v13 * v467 -
                    6 * u * v2 * v13 * v467 + 2 * u1 * v23 * v467 -
                    6 * u * v1 * v23 * v467 + 2 * u * v123 * v467 -
                    u23 * v1467 + 2 * u3 * v2 * v1467 + 2 * u2 * v3 * v1467 -
                    6 * u * v2 * v3 * v1467 + 2 * u * v23 * v1467 -
                    u13 * v2467 + 2 * u3 * v1 * v2467 + 2 * u1 * v3 * v2467 -
                    6 * u * v1 * v3 * v2467 + 2 * u * v13 * v2467 -
                    u3 * v12467 + 2 * u * v3 * v12467 - u12 * v3467 +
                    2 * u2 * v1 * v3467 + 2 * u1 * v2 * v3467 -
                    6 * u * v1 * v2 * v3467 + 2 * u * v12 * v3467 -
                    u2 * v13467 + 2 * u * v2 * v13467 - u1 * v23467 +
                    2 * u * v1 * v23467 - u * v123467,
            .dual567 = u567 - u67 * v5 - u57 * v6 + 2 * u7 * v5 * v6 -
                       u7 * v56 - u56 * v7 + 2 * u6 * v5 * v7 +
                       2 * u5 * v6 * v7 - 6 * u * v5 * v6 * v7 +
                       2 * u * v56 * v7 - u6 * v57 + 2 * u * v6 * v57 -
                       u5 * v67 + 2 * u * v5 * v67 - u * v567,
            .dual1567 = u1567 - u567 * v1 - u167 * v5 + 2 * u67 * v1 * v5 -
                        u67 * v15 - u157 * v6 + 2 * u57 * v1 * v6 +
                        2 * u17 * v5 * v6 - 6 * u7 * v1 * v5 * v6 +
                        2 * u7 * v15 * v6 - u57 * v16 + 2 * u7 * v5 * v16 -
                        u17 * v56 + 2 * u7 * v1 * v56 - u7 * v156 - u156 * v7 +
                        2 * u56 * v1 * v7 + 2 * u16 * v5 * v7 -
                        6 * u6 * v1 * v5 * v7 + 2 * u6 * v15 * v7 +
                        2 * u15 * v6 * v7 - 6 * u5 * v1 * v6 * v7 -
                        6 * u1 * v5 * v6 * v7 + 24 * u * v1 * v5 * v6 * v7 -
                        6 * u * v15 * v6 * v7 + 2 * u5 * v16 * v7 -
                        6 * u * v5 * v16 * v7 + 2 * u1 * v56 * v7 -
                        6 * u * v1 * v56 * v7 + 2 * u * v156 * v7 - u56 * v17 +
                        2 * u6 * v5 * v17 + 2 * u5 * v6 * v17 -
                        6 * u * v5 * v6 * v17 + 2 * u * v56 * v17 - u16 * v57 +
                        2 * u6 * v1 * v57 + 2 * u1 * v6 * v57 -
                        6 * u * v1 * v6 * v57 + 2 * u * v16 * v57 - u6 * v157 +
                        2 * u * v6 * v157 - u15 * v67 + 2 * u5 * v1 * v67 +
                        2 * u1 * v5 * v67 - 6 * u * v1 * v5 * v67 +
                        2 * u * v15 * v67 - u5 * v167 + 2 * u * v5 * v167 -
                        u1 * v567 + 2 * u * v1 * v567 - u * v1567,
            .dual2567 = u2567 - u567 * v2 - u267 * v5 + 2 * u67 * v2 * v5 -
                        u67 * v25 - u257 * v6 + 2 * u57 * v2 * v6 +
                        2 * u27 * v5 * v6 - 6 * u7 * v2 * v5 * v6 +
                        2 * u7 * v25 * v6 - u57 * v26 + 2 * u7 * v5 * v26 -
                        u27 * v56 + 2 * u7 * v2 * v56 - u7 * v256 - u256 * v7 +
                        2 * u56 * v2 * v7 + 2 * u26 * v5 * v7 -
                        6 * u6 * v2 * v5 * v7 + 2 * u6 * v25 * v7 +
                        2 * u25 * v6 * v7 - 6 * u5 * v2 * v6 * v7 -
                        6 * u2 * v5 * v6 * v7 + 24 * u * v2 * v5 * v6 * v7 -
                        6 * u * v25 * v6 * v7 + 2 * u5 * v26 * v7 -
                        6 * u * v5 * v26 * v7 + 2 * u2 * v56 * v7 -
                        6 * u * v2 * v56 * v7 + 2 * u * v256 * v7 - u56 * v27 +
                        2 * u6 * v5 * v27 + 2 * u5 * v6 * v27 -
                        6 * u * v5 * v6 * v27 + 2 * u * v56 * v27 - u26 * v57 +
                        2 * u6 * v2 * v57 + 2 * u2 * v6 * v57 -
                        6 * u * v2 * v6 * v57 + 2 * u * v26 * v57 - u6 * v257 +
                        2 * u * v6 * v257 - u25 * v67 + 2 * u5 * v2 * v67 +
                        2 * u2 * v5 * v67 - 6 * u * v2 * v5 * v67 +
                        2 * u * v25 * v67 - u5 * v267 + 2 * u * v5 * v267 -
                        u2 * v567 + 2 * u * v2 * v567 - u * v2567,
            .dual12567 =
                    u12567 - u2567 * v1 - u1567 * v2 + 2 * u567 * v1 * v2 -
                    u567 * v12 - u1267 * v5 + 2 * u267 * v1 * v5 +
                    2 * u167 * v2 * v5 - 6 * u67 * v1 * v2 * v5 +
                    2 * u67 * v12 * v5 - u267 * v15 + 2 * u67 * v2 * v15 -
                    u167 * v25 + 2 * u67 * v1 * v25 - u67 * v125 - u1257 * v6 +
                    2 * u257 * v1 * v6 + 2 * u157 * v2 * v6 -
                    6 * u57 * v1 * v2 * v6 + 2 * u57 * v12 * v6 +
                    2 * u127 * v5 * v6 - 6 * u27 * v1 * v5 * v6 -
                    6 * u17 * v2 * v5 * v6 + 24 * u7 * v1 * v2 * v5 * v6 -
                    6 * u7 * v12 * v5 * v6 + 2 * u27 * v15 * v6 -
                    6 * u7 * v2 * v15 * v6 + 2 * u17 * v25 * v6 -
                    6 * u7 * v1 * v25 * v6 + 2 * u7 * v125 * v6 - u257 * v16 +
                    2 * u57 * v2 * v16 + 2 * u27 * v5 * v16 -
                    6 * u7 * v2 * v5 * v16 + 2 * u7 * v25 * v16 - u157 * v26 +
                    2 * u57 * v1 * v26 + 2 * u17 * v5 * v26 -
                    6 * u7 * v1 * v5 * v26 + 2 * u7 * v15 * v26 - u57 * v126 +
                    2 * u7 * v5 * v126 - u127 * v56 + 2 * u27 * v1 * v56 +
                    2 * u17 * v2 * v56 - 6 * u7 * v1 * v2 * v56 +
                    2 * u7 * v12 * v56 - u27 * v156 + 2 * u7 * v2 * v156 -
                    u17 * v256 + 2 * u7 * v1 * v256 - u7 * v1256 - u1256 * v7 +
                    2 * u256 * v1 * v7 + 2 * u156 * v2 * v7 -
                    6 * u56 * v1 * v2 * v7 + 2 * u56 * v12 * v7 +
                    2 * u126 * v5 * v7 - 6 * u26 * v1 * v5 * v7 -
                    6 * u16 * v2 * v5 * v7 + 24 * u6 * v1 * v2 * v5 * v7 -
                    6 * u6 * v12 * v5 * v7 + 2 * u26 * v15 * v7 -
                    6 * u6 * v2 * v15 * v7 + 2 * u16 * v25 * v7 -
                    6 * u6 * v1 * v25 * v7 + 2 * u6 * v125 * v7 +
                    2 * u125 * v6 * v7 - 6 * u25 * v1 * v6 * v7 -
                    6 * u15 * v2 * v6 * v7 + 24 * u5 * v1 * v2 * v6 * v7 -
                    6 * u5 * v12 * v6 * v7 - 6 * u12 * v5 * v6 * v7 +
                    24 * u2 * v1 * v5 * v6 * v7 + 24 * u1 * v2 * v5 * v6 * v7 -
                    120 * u * v1 * v2 * v5 * v6 * v7 +
                    24 * u * v12 * v5 * v6 * v7 - 6 * u2 * v15 * v6 * v7 +
                    24 * u * v2 * v15 * v6 * v7 - 6 * u1 * v25 * v6 * v7 +
                    24 * u * v1 * v25 * v6 * v7 - 6 * u * v125 * v6 * v7 +
                    2 * u25 * v16 * v7 - 6 * u5 * v2 * v16 * v7 -
                    6 * u2 * v5 * v16 * v7 + 24 * u * v2 * v5 * v16 * v7 -
                    6 * u * v25 * v16 * v7 + 2 * u15 * v26 * v7 -
                    6 * u5 * v1 * v26 * v7 - 6 * u1 * v5 * v26 * v7 +
                    24 * u * v1 * v5 * v26 * v7 - 6 * u * v15 * v26 * v7 +
                    2 * u5 * v126 * v7 - 6 * u * v5 * v126 * v7 +
                    2 * u12 * v56 * v7 - 6 * u2 * v1 * v56 * v7 -
                    6 * u1 * v2 * v56 * v7 + 24 * u * v1 * v2 * v56 * v7 -
                    6 * u * v12 * v56 * v7 + 2 * u2 * v156 * v7 -
                    6 * u * v2 * v156 * v7 + 2 * u1 * v256 * v7 -
                    6 * u * v1 * v256 * v7 + 2 * u * v1256 * v7 - u256 * v17 +
                    2 * u56 * v2 * v17 + 2 * u26 * v5 * v17 -
                    6 * u6 * v2 * v5 * v17 + 2 * u6 * v25 * v17 +
                    2 * u25 * v6 * v17 - 6 * u5 * v2 * v6 * v17 -
                    6 * u2 * v5 * v6 * v17 + 24 * u * v2 * v5 * v6 * v17 -
                    6 * u * v25 * v6 * v17 + 2 * u5 * v26 * v17 -
                    6 * u * v5 * v26 * v17 + 2 * u2 * v56 * v17 -
                    6 * u * v2 * v56 * v17 + 2 * u * v256 * v17 - u156 * v27 +
                    2 * u56 * v1 * v27 + 2 * u16 * v5 * v27 -
                    6 * u6 * v1 * v5 * v27 + 2 * u6 * v15 * v27 +
                    2 * u15 * v6 * v27 - 6 * u5 * v1 * v6 * v27 -
                    6 * u1 * v5 * v6 * v27 + 24 * u * v1 * v5 * v6 * v27 -
                    6 * u * v15 * v6 * v27 + 2 * u5 * v16 * v27 -
                    6 * u * v5 * v16 * v27 + 2 * u1 * v56 * v27 -
                    6 * u * v1 * v56 * v27 + 2 * u * v156 * v27 - u56 * v127 +
                    2 * u6 * v5 * v127 + 2 * u5 * v6 * v127 -
                    6 * u * v5 * v6 * v127 + 2 * u * v56 * v127 - u126 * v57 +
                    2 * u26 * v1 * v57 + 2 * u16 * v2 * v57 -
                    6 * u6 * v1 * v2 * v57 + 2 * u6 * v12 * v57 +
                    2 * u12 * v6 * v57 - 6 * u2 * v1 * v6 * v57 -
                    6 * u1 * v2 * v6 * v57 + 24 * u * v1 * v2 * v6 * v57 -
                    6 * u * v12 * v6 * v57 + 2 * u2 * v16 * v57 -
                    6 * u * v2 * v16 * v57 + 2 * u1 * v26 * v57 -
                    6 * u * v1 * v26 * v57 + 2 * u * v126 * v57 - u26 * v157 +
                    2 * u6 * v2 * v157 + 2 * u2 * v6 * v157 -
                    6 * u * v2 * v6 * v157 + 2 * u * v26 * v157 - u16 * v257 +
                    2 * u6 * v1 * v257 + 2 * u1 * v6 * v257 -
                    6 * u * v1 * v6 * v257 + 2 * u * v16 * v257 - u6 * v1257 +
                    2 * u * v6 * v1257 - u125 * v67 + 2 * u25 * v1 * v67 +
                    2 * u15 * v2 * v67 - 6 * u5 * v1 * v2 * v67 +
                    2 * u5 * v12 * v67 + 2 * u12 * v5 * v67 -
                    6 * u2 * v1 * v5 * v67 - 6 * u1 * v2 * v5 * v67 +
                    24 * u * v1 * v2 * v5 * v67 - 6 * u * v12 * v5 * v67 +
                    2 * u2 * v15 * v67 - 6 * u * v2 * v15 * v67 +
                    2 * u1 * v25 * v67 - 6 * u * v1 * v25 * v67 +
                    2 * u * v125 * v67 - u25 * v167 + 2 * u5 * v2 * v167 +
                    2 * u2 * v5 * v167 - 6 * u * v2 * v5 * v167 +
                    2 * u * v25 * v167 - u15 * v267 + 2 * u5 * v1 * v267 +
                    2 * u1 * v5 * v267 - 6 * u * v1 * v5 * v267 +
                    2 * u * v15 * v267 - u5 * v1267 + 2 * u * v5 * v1267 -
                    u12 * v567 + 2 * u2 * v1 * v567 + 2 * u1 * v2 * v567 -
                    6 * u * v1 * v2 * v567 + 2 * u * v12 * v567 - u2 * v1567 +
                    2 * u * v2 * v1567 - u1 * v2567 + 2 * u * v1 * v2567 -
                    u * v12567,
            .dual3567 = u3567 - u567 * v3 - u367 * v5 + 2 * u67 * v3 * v5 -
                        u67 * v35 - u357 * v6 + 2 * u57 * v3 * v6 +
                        2 * u37 * v5 * v6 - 6 * u7 * v3 * v5 * v6 +
                        2 * u7 * v35 * v6 - u57 * v36 + 2 * u7 * v5 * v36 -
                        u37 * v56 + 2 * u7 * v3 * v56 - u7 * v356 - u356 * v7 +
                        2 * u56 * v3 * v7 + 2 * u36 * v5 * v7 -
                        6 * u6 * v3 * v5 * v7 + 2 * u6 * v35 * v7 +
                        2 * u35 * v6 * v7 - 6 * u5 * v3 * v6 * v7 -
                        6 * u3 * v5 * v6 * v7 + 24 * u * v3 * v5 * v6 * v7 -
                        6 * u * v35 * v6 * v7 + 2 * u5 * v36 * v7 -
                        6 * u * v5 * v36 * v7 + 2 * u3 * v56 * v7 -
                        6 * u * v3 * v56 * v7 + 2 * u * v356 * v7 - u56 * v37 +
                        2 * u6 * v5 * v37 + 2 * u5 * v6 * v37 -
                        6 * u * v5 * v6 * v37 + 2 * u * v56 * v37 - u36 * v57 +
                        2 * u6 * v3 * v57 + 2 * u3 * v6 * v57 -
                        6 * u * v3 * v6 * v57 + 2 * u * v36 * v57 - u6 * v357 +
                        2 * u * v6 * v357 - u35 * v67 + 2 * u5 * v3 * v67 +
                        2 * u3 * v5 * v67 - 6 * u * v3 * v5 * v67 +
                        2 * u * v35 * v67 - u5 * v367 + 2 * u * v5 * v367 -
                        u3 * v567 + 2 * u * v3 * v567 - u * v3567,
            .dual13567 =
                    u13567 - u3567 * v1 - u1567 * v3 + 2 * u567 * v1 * v3 -
                    u567 * v13 - u1367 * v5 + 2 * u367 * v1 * v5 +
                    2 * u167 * v3 * v5 - 6 * u67 * v1 * v3 * v5 +
                    2 * u67 * v13 * v5 - u367 * v15 + 2 * u67 * v3 * v15 -
                    u167 * v35 + 2 * u67 * v1 * v35 - u67 * v135 - u1357 * v6 +
                    2 * u357 * v1 * v6 + 2 * u157 * v3 * v6 -
                    6 * u57 * v1 * v3 * v6 + 2 * u57 * v13 * v6 +
                    2 * u137 * v5 * v6 - 6 * u37 * v1 * v5 * v6 -
                    6 * u17 * v3 * v5 * v6 + 24 * u7 * v1 * v3 * v5 * v6 -
                    6 * u7 * v13 * v5 * v6 + 2 * u37 * v15 * v6 -
                    6 * u7 * v3 * v15 * v6 + 2 * u17 * v35 * v6 -
                    6 * u7 * v1 * v35 * v6 + 2 * u7 * v135 * v6 - u357 * v16 +
                    2 * u57 * v3 * v16 + 2 * u37 * v5 * v16 -
                    6 * u7 * v3 * v5 * v16 + 2 * u7 * v35 * v16 - u157 * v36 +
                    2 * u57 * v1 * v36 + 2 * u17 * v5 * v36 -
                    6 * u7 * v1 * v5 * v36 + 2 * u7 * v15 * v36 - u57 * v136 +
                    2 * u7 * v5 * v136 - u137 * v56 + 2 * u37 * v1 * v56 +
                    2 * u17 * v3 * v56 - 6 * u7 * v1 * v3 * v56 +
                    2 * u7 * v13 * v56 - u37 * v156 + 2 * u7 * v3 * v156 -
                    u17 * v356 + 2 * u7 * v1 * v356 - u7 * v1356 - u1356 * v7 +
                    2 * u356 * v1 * v7 + 2 * u156 * v3 * v7 -
                    6 * u56 * v1 * v3 * v7 + 2 * u56 * v13 * v7 +
                    2 * u136 * v5 * v7 - 6 * u36 * v1 * v5 * v7 -
                    6 * u16 * v3 * v5 * v7 + 24 * u6 * v1 * v3 * v5 * v7 -
                    6 * u6 * v13 * v5 * v7 + 2 * u36 * v15 * v7 -
                    6 * u6 * v3 * v15 * v7 + 2 * u16 * v35 * v7 -
                    6 * u6 * v1 * v35 * v7 + 2 * u6 * v135 * v7 +
                    2 * u135 * v6 * v7 - 6 * u35 * v1 * v6 * v7 -
                    6 * u15 * v3 * v6 * v7 + 24 * u5 * v1 * v3 * v6 * v7 -
                    6 * u5 * v13 * v6 * v7 - 6 * u13 * v5 * v6 * v7 +
                    24 * u3 * v1 * v5 * v6 * v7 + 24 * u1 * v3 * v5 * v6 * v7 -
                    120 * u * v1 * v3 * v5 * v6 * v7 +
                    24 * u * v13 * v5 * v6 * v7 - 6 * u3 * v15 * v6 * v7 +
                    24 * u * v3 * v15 * v6 * v7 - 6 * u1 * v35 * v6 * v7 +
                    24 * u * v1 * v35 * v6 * v7 - 6 * u * v135 * v6 * v7 +
                    2 * u35 * v16 * v7 - 6 * u5 * v3 * v16 * v7 -
                    6 * u3 * v5 * v16 * v7 + 24 * u * v3 * v5 * v16 * v7 -
                    6 * u * v35 * v16 * v7 + 2 * u15 * v36 * v7 -
                    6 * u5 * v1 * v36 * v7 - 6 * u1 * v5 * v36 * v7 +
                    24 * u * v1 * v5 * v36 * v7 - 6 * u * v15 * v36 * v7 +
                    2 * u5 * v136 * v7 - 6 * u * v5 * v136 * v7 +
                    2 * u13 * v56 * v7 - 6 * u3 * v1 * v56 * v7 -
                    6 * u1 * v3 * v56 * v7 + 24 * u * v1 * v3 * v56 * v7 -
                    6 * u * v13 * v56 * v7 + 2 * u3 * v156 * v7 -
                    6 * u * v3 * v156 * v7 + 2 * u1 * v356 * v7 -
                    6 * u * v1 * v356 * v7 + 2 * u * v1356 * v7 - u356 * v17 +
                    2 * u56 * v3 * v17 + 2 * u36 * v5 * v17 -
                    6 * u6 * v3 * v5 * v17 + 2 * u6 * v35 * v17 +
                    2 * u35 * v6 * v17 - 6 * u5 * v3 * v6 * v17 -
                    6 * u3 * v5 * v6 * v17 + 24 * u * v3 * v5 * v6 * v17 -
                    6 * u * v35 * v6 * v17 + 2 * u5 * v36 * v17 -
                    6 * u * v5 * v36 * v17 + 2 * u3 * v56 * v17 -
                    6 * u * v3 * v56 * v17 + 2 * u * v356 * v17 - u156 * v37 +
                    2 * u56 * v1 * v37 + 2 * u16 * v5 * v37 -
                    6 * u6 * v1 * v5 * v37 + 2 * u6 * v15 * v37 +
                    2 * u15 * v6 * v37 - 6 * u5 * v1 * v6 * v37 -
                    6 * u1 * v5 * v6 * v37 + 24 * u * v1 * v5 * v6 * v37 -
                    6 * u * v15 * v6 * v37 + 2 * u5 * v16 * v37 -
                    6 * u * v5 * v16 * v37 + 2 * u1 * v56 * v37 -
                    6 * u * v1 * v56 * v37 + 2 * u * v156 * v37 - u56 * v137 +
                    2 * u6 * v5 * v137 + 2 * u5 * v6 * v137 -
                    6 * u * v5 * v6 * v137 + 2 * u * v56 * v137 - u136 * v57 +
                    2 * u36 * v1 * v57 + 2 * u16 * v3 * v57 -
                    6 * u6 * v1 * v3 * v57 + 2 * u6 * v13 * v57 +
                    2 * u13 * v6 * v57 - 6 * u3 * v1 * v6 * v57 -
                    6 * u1 * v3 * v6 * v57 + 24 * u * v1 * v3 * v6 * v57 -
                    6 * u * v13 * v6 * v57 + 2 * u3 * v16 * v57 -
                    6 * u * v3 * v16 * v57 + 2 * u1 * v36 * v57 -
                    6 * u * v1 * v36 * v57 + 2 * u * v136 * v57 - u36 * v157 +
                    2 * u6 * v3 * v157 + 2 * u3 * v6 * v157 -
                    6 * u * v3 * v6 * v157 + 2 * u * v36 * v157 - u16 * v357 +
                    2 * u6 * v1 * v357 + 2 * u1 * v6 * v357 -
                    6 * u * v1 * v6 * v357 + 2 * u * v16 * v357 - u6 * v1357 +
                    2 * u * v6 * v1357 - u135 * v67 + 2 * u35 * v1 * v67 +
                    2 * u15 * v3 * v67 - 6 * u5 * v1 * v3 * v67 +
                    2 * u5 * v13 * v67 + 2 * u13 * v5 * v67 -
                    6 * u3 * v1 * v5 * v67 - 6 * u1 * v3 * v5 * v67 +
                    24 * u * v1 * v3 * v5 * v67 - 6 * u * v13 * v5 * v67 +
                    2 * u3 * v15 * v67 - 6 * u * v3 * v15 * v67 +
                    2 * u1 * v35 * v67 - 6 * u * v1 * v35 * v67 +
                    2 * u * v135 * v67 - u35 * v167 + 2 * u5 * v3 * v167 +
                    2 * u3 * v5 * v167 - 6 * u * v3 * v5 * v167 +
                    2 * u * v35 * v167 - u15 * v367 + 2 * u5 * v1 * v367 +
                    2 * u1 * v5 * v367 - 6 * u * v1 * v5 * v367 +
                    2 * u * v15 * v367 - u5 * v1367 + 2 * u * v5 * v1367 -
                    u13 * v567 + 2 * u3 * v1 * v567 + 2 * u1 * v3 * v567 -
                    6 * u * v1 * v3 * v567 + 2 * u * v13 * v567 - u3 * v1567 +
                    2 * u * v3 * v1567 - u1 * v3567 + 2 * u * v1 * v3567 -
                    u * v13567,
            .dual23567 =
                    u23567 - u3567 * v2 - u2567 * v3 + 2 * u567 * v2 * v3 -
                    u567 * v23 - u2367 * v5 + 2 * u367 * v2 * v5 +
                    2 * u267 * v3 * v5 - 6 * u67 * v2 * v3 * v5 +
                    2 * u67 * v23 * v5 - u367 * v25 + 2 * u67 * v3 * v25 -
                    u267 * v35 + 2 * u67 * v2 * v35 - u67 * v235 - u2357 * v6 +
                    2 * u357 * v2 * v6 + 2 * u257 * v3 * v6 -
                    6 * u57 * v2 * v3 * v6 + 2 * u57 * v23 * v6 +
                    2 * u237 * v5 * v6 - 6 * u37 * v2 * v5 * v6 -
                    6 * u27 * v3 * v5 * v6 + 24 * u7 * v2 * v3 * v5 * v6 -
                    6 * u7 * v23 * v5 * v6 + 2 * u37 * v25 * v6 -
                    6 * u7 * v3 * v25 * v6 + 2 * u27 * v35 * v6 -
                    6 * u7 * v2 * v35 * v6 + 2 * u7 * v235 * v6 - u357 * v26 +
                    2 * u57 * v3 * v26 + 2 * u37 * v5 * v26 -
                    6 * u7 * v3 * v5 * v26 + 2 * u7 * v35 * v26 - u257 * v36 +
                    2 * u57 * v2 * v36 + 2 * u27 * v5 * v36 -
                    6 * u7 * v2 * v5 * v36 + 2 * u7 * v25 * v36 - u57 * v236 +
                    2 * u7 * v5 * v236 - u237 * v56 + 2 * u37 * v2 * v56 +
                    2 * u27 * v3 * v56 - 6 * u7 * v2 * v3 * v56 +
                    2 * u7 * v23 * v56 - u37 * v256 + 2 * u7 * v3 * v256 -
                    u27 * v356 + 2 * u7 * v2 * v356 - u7 * v2356 - u2356 * v7 +
                    2 * u356 * v2 * v7 + 2 * u256 * v3 * v7 -
                    6 * u56 * v2 * v3 * v7 + 2 * u56 * v23 * v7 +
                    2 * u236 * v5 * v7 - 6 * u36 * v2 * v5 * v7 -
                    6 * u26 * v3 * v5 * v7 + 24 * u6 * v2 * v3 * v5 * v7 -
                    6 * u6 * v23 * v5 * v7 + 2 * u36 * v25 * v7 -
                    6 * u6 * v3 * v25 * v7 + 2 * u26 * v35 * v7 -
                    6 * u6 * v2 * v35 * v7 + 2 * u6 * v235 * v7 +
                    2 * u235 * v6 * v7 - 6 * u35 * v2 * v6 * v7 -
                    6 * u25 * v3 * v6 * v7 + 24 * u5 * v2 * v3 * v6 * v7 -
                    6 * u5 * v23 * v6 * v7 - 6 * u23 * v5 * v6 * v7 +
                    24 * u3 * v2 * v5 * v6 * v7 + 24 * u2 * v3 * v5 * v6 * v7 -
                    120 * u * v2 * v3 * v5 * v6 * v7 +
                    24 * u * v23 * v5 * v6 * v7 - 6 * u3 * v25 * v6 * v7 +
                    24 * u * v3 * v25 * v6 * v7 - 6 * u2 * v35 * v6 * v7 +
                    24 * u * v2 * v35 * v6 * v7 - 6 * u * v235 * v6 * v7 +
                    2 * u35 * v26 * v7 - 6 * u5 * v3 * v26 * v7 -
                    6 * u3 * v5 * v26 * v7 + 24 * u * v3 * v5 * v26 * v7 -
                    6 * u * v35 * v26 * v7 + 2 * u25 * v36 * v7 -
                    6 * u5 * v2 * v36 * v7 - 6 * u2 * v5 * v36 * v7 +
                    24 * u * v2 * v5 * v36 * v7 - 6 * u * v25 * v36 * v7 +
                    2 * u5 * v236 * v7 - 6 * u * v5 * v236 * v7 +
                    2 * u23 * v56 * v7 - 6 * u3 * v2 * v56 * v7 -
                    6 * u2 * v3 * v56 * v7 + 24 * u * v2 * v3 * v56 * v7 -
                    6 * u * v23 * v56 * v7 + 2 * u3 * v256 * v7 -
                    6 * u * v3 * v256 * v7 + 2 * u2 * v356 * v7 -
                    6 * u * v2 * v356 * v7 + 2 * u * v2356 * v7 - u356 * v27 +
                    2 * u56 * v3 * v27 + 2 * u36 * v5 * v27 -
                    6 * u6 * v3 * v5 * v27 + 2 * u6 * v35 * v27 +
                    2 * u35 * v6 * v27 - 6 * u5 * v3 * v6 * v27 -
                    6 * u3 * v5 * v6 * v27 + 24 * u * v3 * v5 * v6 * v27 -
                    6 * u * v35 * v6 * v27 + 2 * u5 * v36 * v27 -
                    6 * u * v5 * v36 * v27 + 2 * u3 * v56 * v27 -
                    6 * u * v3 * v56 * v27 + 2 * u * v356 * v27 - u256 * v37 +
                    2 * u56 * v2 * v37 + 2 * u26 * v5 * v37 -
                    6 * u6 * v2 * v5 * v37 + 2 * u6 * v25 * v37 +
                    2 * u25 * v6 * v37 - 6 * u5 * v2 * v6 * v37 -
                    6 * u2 * v5 * v6 * v37 + 24 * u * v2 * v5 * v6 * v37 -
                    6 * u * v25 * v6 * v37 + 2 * u5 * v26 * v37 -
                    6 * u * v5 * v26 * v37 + 2 * u2 * v56 * v37 -
                    6 * u * v2 * v56 * v37 + 2 * u * v256 * v37 - u56 * v237 +
                    2 * u6 * v5 * v237 + 2 * u5 * v6 * v237 -
                    6 * u * v5 * v6 * v237 + 2 * u * v56 * v237 - u236 * v57 +
                    2 * u36 * v2 * v57 + 2 * u26 * v3 * v57 -
                    6 * u6 * v2 * v3 * v57 + 2 * u6 * v23 * v57 +
                    2 * u23 * v6 * v57 - 6 * u3 * v2 * v6 * v57 -
                    6 * u2 * v3 * v6 * v57 + 24 * u * v2 * v3 * v6 * v57 -
                    6 * u * v23 * v6 * v57 + 2 * u3 * v26 * v57 -
                    6 * u * v3 * v26 * v57 + 2 * u2 * v36 * v57 -
                    6 * u * v2 * v36 * v57 + 2 * u * v236 * v57 - u36 * v257 +
                    2 * u6 * v3 * v257 + 2 * u3 * v6 * v257 -
                    6 * u * v3 * v6 * v257 + 2 * u * v36 * v257 - u26 * v357 +
                    2 * u6 * v2 * v357 + 2 * u2 * v6 * v357 -
                    6 * u * v2 * v6 * v357 + 2 * u * v26 * v357 - u6 * v2357 +
                    2 * u * v6 * v2357 - u235 * v67 + 2 * u35 * v2 * v67 +
                    2 * u25 * v3 * v67 - 6 * u5 * v2 * v3 * v67 +
                    2 * u5 * v23 * v67 + 2 * u23 * v5 * v67 -
                    6 * u3 * v2 * v5 * v67 - 6 * u2 * v3 * v5 * v67 +
                    24 * u * v2 * v3 * v5 * v67 - 6 * u * v23 * v5 * v67 +
                    2 * u3 * v25 * v67 - 6 * u * v3 * v25 * v67 +
                    2 * u2 * v35 * v67 - 6 * u * v2 * v35 * v67 +
                    2 * u * v235 * v67 - u35 * v267 + 2 * u5 * v3 * v267 +
                    2 * u3 * v5 * v267 - 6 * u * v3 * v5 * v267 +
                    2 * u * v35 * v267 - u25 * v367 + 2 * u5 * v2 * v367 +
                    2 * u2 * v5 * v367 - 6 * u * v2 * v5 * v367 +
                    2 * u * v25 * v367 - u5 * v2367 + 2 * u * v5 * v2367 -
                    u23 * v567 + 2 * u3 * v2 * v567 + 2 * u2 * v3 * v567 -
                    6 * u * v2 * v3 * v567 + 2 * u * v23 * v567 - u3 * v2567 +
                    2 * u * v3 * v2567 - u2 * v3567 + 2 * u * v2 * v3567 -
                    u * v23567,
            .dual123567 =
                    u123567 - u23567 * v1 - u13567 * v2 + 2 * u3567 * v1 * v2 -
                    u3567 * v12 - u12567 * v3 + 2 * u2567 * v1 * v3 +
                    2 * u1567 * v2 * v3 - 6 * u567 * v1 * v2 * v3 +
                    2 * u567 * v12 * v3 - u2567 * v13 + 2 * u567 * v2 * v13 -
                    u1567 * v23 + 2 * u567 * v1 * v23 - u567 * v123 -
                    u12367 * v5 + 2 * u2367 * v1 * v5 + 2 * u1367 * v2 * v5 -
                    6 * u367 * v1 * v2 * v5 + 2 * u367 * v12 * v5 +
                    2 * u1267 * v3 * v5 - 6 * u267 * v1 * v3 * v5 -
                    6 * u167 * v2 * v3 * v5 + 24 * u67 * v1 * v2 * v3 * v5 -
                    6 * u67 * v12 * v3 * v5 + 2 * u267 * v13 * v5 -
                    6 * u67 * v2 * v13 * v5 + 2 * u167 * v23 * v5 -
                    6 * u67 * v1 * v23 * v5 + 2 * u67 * v123 * v5 -
                    u2367 * v15 + 2 * u367 * v2 * v15 + 2 * u267 * v3 * v15 -
                    6 * u67 * v2 * v3 * v15 + 2 * u67 * v23 * v15 -
                    u1367 * v25 + 2 * u367 * v1 * v25 + 2 * u167 * v3 * v25 -
                    6 * u67 * v1 * v3 * v25 + 2 * u67 * v13 * v25 -
                    u367 * v125 + 2 * u67 * v3 * v125 - u1267 * v35 +
                    2 * u267 * v1 * v35 + 2 * u167 * v2 * v35 -
                    6 * u67 * v1 * v2 * v35 + 2 * u67 * v12 * v35 -
                    u267 * v135 + 2 * u67 * v2 * v135 - u167 * v235 +
                    2 * u67 * v1 * v235 - u67 * v1235 - u12357 * v6 +
                    2 * u2357 * v1 * v6 + 2 * u1357 * v2 * v6 -
                    6 * u357 * v1 * v2 * v6 + 2 * u357 * v12 * v6 +
                    2 * u1257 * v3 * v6 - 6 * u257 * v1 * v3 * v6 -
                    6 * u157 * v2 * v3 * v6 + 24 * u57 * v1 * v2 * v3 * v6 -
                    6 * u57 * v12 * v3 * v6 + 2 * u257 * v13 * v6 -
                    6 * u57 * v2 * v13 * v6 + 2 * u157 * v23 * v6 -
                    6 * u57 * v1 * v23 * v6 + 2 * u57 * v123 * v6 +
                    2 * u1237 * v5 * v6 - 6 * u237 * v1 * v5 * v6 -
                    6 * u137 * v2 * v5 * v6 + 24 * u37 * v1 * v2 * v5 * v6 -
                    6 * u37 * v12 * v5 * v6 - 6 * u127 * v3 * v5 * v6 +
                    24 * u27 * v1 * v3 * v5 * v6 +
                    24 * u17 * v2 * v3 * v5 * v6 -
                    120 * u7 * v1 * v2 * v3 * v5 * v6 +
                    24 * u7 * v12 * v3 * v5 * v6 - 6 * u27 * v13 * v5 * v6 +
                    24 * u7 * v2 * v13 * v5 * v6 - 6 * u17 * v23 * v5 * v6 +
                    24 * u7 * v1 * v23 * v5 * v6 - 6 * u7 * v123 * v5 * v6 +
                    2 * u237 * v15 * v6 - 6 * u37 * v2 * v15 * v6 -
                    6 * u27 * v3 * v15 * v6 + 24 * u7 * v2 * v3 * v15 * v6 -
                    6 * u7 * v23 * v15 * v6 + 2 * u137 * v25 * v6 -
                    6 * u37 * v1 * v25 * v6 - 6 * u17 * v3 * v25 * v6 +
                    24 * u7 * v1 * v3 * v25 * v6 - 6 * u7 * v13 * v25 * v6 +
                    2 * u37 * v125 * v6 - 6 * u7 * v3 * v125 * v6 +
                    2 * u127 * v35 * v6 - 6 * u27 * v1 * v35 * v6 -
                    6 * u17 * v2 * v35 * v6 + 24 * u7 * v1 * v2 * v35 * v6 -
                    6 * u7 * v12 * v35 * v6 + 2 * u27 * v135 * v6 -
                    6 * u7 * v2 * v135 * v6 + 2 * u17 * v235 * v6 -
                    6 * u7 * v1 * v235 * v6 + 2 * u7 * v1235 * v6 -
                    u2357 * v16 + 2 * u357 * v2 * v16 + 2 * u257 * v3 * v16 -
                    6 * u57 * v2 * v3 * v16 + 2 * u57 * v23 * v16 +
                    2 * u237 * v5 * v16 - 6 * u37 * v2 * v5 * v16 -
                    6 * u27 * v3 * v5 * v16 + 24 * u7 * v2 * v3 * v5 * v16 -
                    6 * u7 * v23 * v5 * v16 + 2 * u37 * v25 * v16 -
                    6 * u7 * v3 * v25 * v16 + 2 * u27 * v35 * v16 -
                    6 * u7 * v2 * v35 * v16 + 2 * u7 * v235 * v16 -
                    u1357 * v26 + 2 * u357 * v1 * v26 + 2 * u157 * v3 * v26 -
                    6 * u57 * v1 * v3 * v26 + 2 * u57 * v13 * v26 +
                    2 * u137 * v5 * v26 - 6 * u37 * v1 * v5 * v26 -
                    6 * u17 * v3 * v5 * v26 + 24 * u7 * v1 * v3 * v5 * v26 -
                    6 * u7 * v13 * v5 * v26 + 2 * u37 * v15 * v26 -
                    6 * u7 * v3 * v15 * v26 + 2 * u17 * v35 * v26 -
                    6 * u7 * v1 * v35 * v26 + 2 * u7 * v135 * v26 -
                    u357 * v126 + 2 * u57 * v3 * v126 + 2 * u37 * v5 * v126 -
                    6 * u7 * v3 * v5 * v126 + 2 * u7 * v35 * v126 -
                    u1257 * v36 + 2 * u257 * v1 * v36 + 2 * u157 * v2 * v36 -
                    6 * u57 * v1 * v2 * v36 + 2 * u57 * v12 * v36 +
                    2 * u127 * v5 * v36 - 6 * u27 * v1 * v5 * v36 -
                    6 * u17 * v2 * v5 * v36 + 24 * u7 * v1 * v2 * v5 * v36 -
                    6 * u7 * v12 * v5 * v36 + 2 * u27 * v15 * v36 -
                    6 * u7 * v2 * v15 * v36 + 2 * u17 * v25 * v36 -
                    6 * u7 * v1 * v25 * v36 + 2 * u7 * v125 * v36 -
                    u257 * v136 + 2 * u57 * v2 * v136 + 2 * u27 * v5 * v136 -
                    6 * u7 * v2 * v5 * v136 + 2 * u7 * v25 * v136 -
                    u157 * v236 + 2 * u57 * v1 * v236 + 2 * u17 * v5 * v236 -
                    6 * u7 * v1 * v5 * v236 + 2 * u7 * v15 * v236 -
                    u57 * v1236 + 2 * u7 * v5 * v1236 - u1237 * v56 +
                    2 * u237 * v1 * v56 + 2 * u137 * v2 * v56 -
                    6 * u37 * v1 * v2 * v56 + 2 * u37 * v12 * v56 +
                    2 * u127 * v3 * v56 - 6 * u27 * v1 * v3 * v56 -
                    6 * u17 * v2 * v3 * v56 + 24 * u7 * v1 * v2 * v3 * v56 -
                    6 * u7 * v12 * v3 * v56 + 2 * u27 * v13 * v56 -
                    6 * u7 * v2 * v13 * v56 + 2 * u17 * v23 * v56 -
                    6 * u7 * v1 * v23 * v56 + 2 * u7 * v123 * v56 -
                    u237 * v156 + 2 * u37 * v2 * v156 + 2 * u27 * v3 * v156 -
                    6 * u7 * v2 * v3 * v156 + 2 * u7 * v23 * v156 -
                    u137 * v256 + 2 * u37 * v1 * v256 + 2 * u17 * v3 * v256 -
                    6 * u7 * v1 * v3 * v256 + 2 * u7 * v13 * v256 -
                    u37 * v1256 + 2 * u7 * v3 * v1256 - u127 * v356 +
                    2 * u27 * v1 * v356 + 2 * u17 * v2 * v356 -
                    6 * u7 * v1 * v2 * v356 + 2 * u7 * v12 * v356 -
                    u27 * v1356 + 2 * u7 * v2 * v1356 - u17 * v2356 +
                    2 * u7 * v1 * v2356 - u7 * v12356 - u12356 * v7 +
                    2 * u2356 * v1 * v7 + 2 * u1356 * v2 * v7 -
                    6 * u356 * v1 * v2 * v7 + 2 * u356 * v12 * v7 +
                    2 * u1256 * v3 * v7 - 6 * u256 * v1 * v3 * v7 -
                    6 * u156 * v2 * v3 * v7 + 24 * u56 * v1 * v2 * v3 * v7 -
                    6 * u56 * v12 * v3 * v7 + 2 * u256 * v13 * v7 -
                    6 * u56 * v2 * v13 * v7 + 2 * u156 * v23 * v7 -
                    6 * u56 * v1 * v23 * v7 + 2 * u56 * v123 * v7 +
                    2 * u1236 * v5 * v7 - 6 * u236 * v1 * v5 * v7 -
                    6 * u136 * v2 * v5 * v7 + 24 * u36 * v1 * v2 * v5 * v7 -
                    6 * u36 * v12 * v5 * v7 - 6 * u126 * v3 * v5 * v7 +
                    24 * u26 * v1 * v3 * v5 * v7 +
                    24 * u16 * v2 * v3 * v5 * v7 -
                    120 * u6 * v1 * v2 * v3 * v5 * v7 +
                    24 * u6 * v12 * v3 * v5 * v7 - 6 * u26 * v13 * v5 * v7 +
                    24 * u6 * v2 * v13 * v5 * v7 - 6 * u16 * v23 * v5 * v7 +
                    24 * u6 * v1 * v23 * v5 * v7 - 6 * u6 * v123 * v5 * v7 +
                    2 * u236 * v15 * v7 - 6 * u36 * v2 * v15 * v7 -
                    6 * u26 * v3 * v15 * v7 + 24 * u6 * v2 * v3 * v15 * v7 -
                    6 * u6 * v23 * v15 * v7 + 2 * u136 * v25 * v7 -
                    6 * u36 * v1 * v25 * v7 - 6 * u16 * v3 * v25 * v7 +
                    24 * u6 * v1 * v3 * v25 * v7 - 6 * u6 * v13 * v25 * v7 +
                    2 * u36 * v125 * v7 - 6 * u6 * v3 * v125 * v7 +
                    2 * u126 * v35 * v7 - 6 * u26 * v1 * v35 * v7 -
                    6 * u16 * v2 * v35 * v7 + 24 * u6 * v1 * v2 * v35 * v7 -
                    6 * u6 * v12 * v35 * v7 + 2 * u26 * v135 * v7 -
                    6 * u6 * v2 * v135 * v7 + 2 * u16 * v235 * v7 -
                    6 * u6 * v1 * v235 * v7 + 2 * u6 * v1235 * v7 +
                    2 * u1235 * v6 * v7 - 6 * u235 * v1 * v6 * v7 -
                    6 * u135 * v2 * v6 * v7 + 24 * u35 * v1 * v2 * v6 * v7 -
                    6 * u35 * v12 * v6 * v7 - 6 * u125 * v3 * v6 * v7 +
                    24 * u25 * v1 * v3 * v6 * v7 +
                    24 * u15 * v2 * v3 * v6 * v7 -
                    120 * u5 * v1 * v2 * v3 * v6 * v7 +
                    24 * u5 * v12 * v3 * v6 * v7 - 6 * u25 * v13 * v6 * v7 +
                    24 * u5 * v2 * v13 * v6 * v7 - 6 * u15 * v23 * v6 * v7 +
                    24 * u5 * v1 * v23 * v6 * v7 - 6 * u5 * v123 * v6 * v7 -
                    6 * u123 * v5 * v6 * v7 + 24 * u23 * v1 * v5 * v6 * v7 +
                    24 * u13 * v2 * v5 * v6 * v7 -
                    120 * u3 * v1 * v2 * v5 * v6 * v7 +
                    24 * u3 * v12 * v5 * v6 * v7 +
                    24 * u12 * v3 * v5 * v6 * v7 -
                    120 * u2 * v1 * v3 * v5 * v6 * v7 -
                    120 * u1 * v2 * v3 * v5 * v6 * v7 +
                    720 * u * v1 * v2 * v3 * v5 * v6 * v7 -
                    120 * u * v12 * v3 * v5 * v6 * v7 +
                    24 * u2 * v13 * v5 * v6 * v7 -
                    120 * u * v2 * v13 * v5 * v6 * v7 +
                    24 * u1 * v23 * v5 * v6 * v7 -
                    120 * u * v1 * v23 * v5 * v6 * v7 +
                    24 * u * v123 * v5 * v6 * v7 - 6 * u23 * v15 * v6 * v7 +
                    24 * u3 * v2 * v15 * v6 * v7 +
                    24 * u2 * v3 * v15 * v6 * v7 -
                    120 * u * v2 * v3 * v15 * v6 * v7 +
                    24 * u * v23 * v15 * v6 * v7 - 6 * u13 * v25 * v6 * v7 +
                    24 * u3 * v1 * v25 * v6 * v7 +
                    24 * u1 * v3 * v25 * v6 * v7 -
                    120 * u * v1 * v3 * v25 * v6 * v7 +
                    24 * u * v13 * v25 * v6 * v7 - 6 * u3 * v125 * v6 * v7 +
                    24 * u * v3 * v125 * v6 * v7 - 6 * u12 * v35 * v6 * v7 +
                    24 * u2 * v1 * v35 * v6 * v7 +
                    24 * u1 * v2 * v35 * v6 * v7 -
                    120 * u * v1 * v2 * v35 * v6 * v7 +
                    24 * u * v12 * v35 * v6 * v7 - 6 * u2 * v135 * v6 * v7 +
                    24 * u * v2 * v135 * v6 * v7 - 6 * u1 * v235 * v6 * v7 +
                    24 * u * v1 * v235 * v6 * v7 - 6 * u * v1235 * v6 * v7 +
                    2 * u235 * v16 * v7 - 6 * u35 * v2 * v16 * v7 -
                    6 * u25 * v3 * v16 * v7 + 24 * u5 * v2 * v3 * v16 * v7 -
                    6 * u5 * v23 * v16 * v7 - 6 * u23 * v5 * v16 * v7 +
                    24 * u3 * v2 * v5 * v16 * v7 +
                    24 * u2 * v3 * v5 * v16 * v7 -
                    120 * u * v2 * v3 * v5 * v16 * v7 +
                    24 * u * v23 * v5 * v16 * v7 - 6 * u3 * v25 * v16 * v7 +
                    24 * u * v3 * v25 * v16 * v7 - 6 * u2 * v35 * v16 * v7 +
                    24 * u * v2 * v35 * v16 * v7 - 6 * u * v235 * v16 * v7 +
                    2 * u135 * v26 * v7 - 6 * u35 * v1 * v26 * v7 -
                    6 * u15 * v3 * v26 * v7 + 24 * u5 * v1 * v3 * v26 * v7 -
                    6 * u5 * v13 * v26 * v7 - 6 * u13 * v5 * v26 * v7 +
                    24 * u3 * v1 * v5 * v26 * v7 +
                    24 * u1 * v3 * v5 * v26 * v7 -
                    120 * u * v1 * v3 * v5 * v26 * v7 +
                    24 * u * v13 * v5 * v26 * v7 - 6 * u3 * v15 * v26 * v7 +
                    24 * u * v3 * v15 * v26 * v7 - 6 * u1 * v35 * v26 * v7 +
                    24 * u * v1 * v35 * v26 * v7 - 6 * u * v135 * v26 * v7 +
                    2 * u35 * v126 * v7 - 6 * u5 * v3 * v126 * v7 -
                    6 * u3 * v5 * v126 * v7 + 24 * u * v3 * v5 * v126 * v7 -
                    6 * u * v35 * v126 * v7 + 2 * u125 * v36 * v7 -
                    6 * u25 * v1 * v36 * v7 - 6 * u15 * v2 * v36 * v7 +
                    24 * u5 * v1 * v2 * v36 * v7 - 6 * u5 * v12 * v36 * v7 -
                    6 * u12 * v5 * v36 * v7 + 24 * u2 * v1 * v5 * v36 * v7 +
                    24 * u1 * v2 * v5 * v36 * v7 -
                    120 * u * v1 * v2 * v5 * v36 * v7 +
                    24 * u * v12 * v5 * v36 * v7 - 6 * u2 * v15 * v36 * v7 +
                    24 * u * v2 * v15 * v36 * v7 - 6 * u1 * v25 * v36 * v7 +
                    24 * u * v1 * v25 * v36 * v7 - 6 * u * v125 * v36 * v7 +
                    2 * u25 * v136 * v7 - 6 * u5 * v2 * v136 * v7 -
                    6 * u2 * v5 * v136 * v7 + 24 * u * v2 * v5 * v136 * v7 -
                    6 * u * v25 * v136 * v7 + 2 * u15 * v236 * v7 -
                    6 * u5 * v1 * v236 * v7 - 6 * u1 * v5 * v236 * v7 +
                    24 * u * v1 * v5 * v236 * v7 - 6 * u * v15 * v236 * v7 +
                    2 * u5 * v1236 * v7 - 6 * u * v5 * v1236 * v7 +
                    2 * u123 * v56 * v7 - 6 * u23 * v1 * v56 * v7 -
                    6 * u13 * v2 * v56 * v7 + 24 * u3 * v1 * v2 * v56 * v7 -
                    6 * u3 * v12 * v56 * v7 - 6 * u12 * v3 * v56 * v7 +
                    24 * u2 * v1 * v3 * v56 * v7 +
                    24 * u1 * v2 * v3 * v56 * v7 -
                    120 * u * v1 * v2 * v3 * v56 * v7 +
                    24 * u * v12 * v3 * v56 * v7 - 6 * u2 * v13 * v56 * v7 +
                    24 * u * v2 * v13 * v56 * v7 - 6 * u1 * v23 * v56 * v7 +
                    24 * u * v1 * v23 * v56 * v7 - 6 * u * v123 * v56 * v7 +
                    2 * u23 * v156 * v7 - 6 * u3 * v2 * v156 * v7 -
                    6 * u2 * v3 * v156 * v7 + 24 * u * v2 * v3 * v156 * v7 -
                    6 * u * v23 * v156 * v7 + 2 * u13 * v256 * v7 -
                    6 * u3 * v1 * v256 * v7 - 6 * u1 * v3 * v256 * v7 +
                    24 * u * v1 * v3 * v256 * v7 - 6 * u * v13 * v256 * v7 +
                    2 * u3 * v1256 * v7 - 6 * u * v3 * v1256 * v7 +
                    2 * u12 * v356 * v7 - 6 * u2 * v1 * v356 * v7 -
                    6 * u1 * v2 * v356 * v7 + 24 * u * v1 * v2 * v356 * v7 -
                    6 * u * v12 * v356 * v7 + 2 * u2 * v1356 * v7 -
                    6 * u * v2 * v1356 * v7 + 2 * u1 * v2356 * v7 -
                    6 * u * v1 * v2356 * v7 + 2 * u * v12356 * v7 -
                    u2356 * v17 + 2 * u356 * v2 * v17 + 2 * u256 * v3 * v17 -
                    6 * u56 * v2 * v3 * v17 + 2 * u56 * v23 * v17 +
                    2 * u236 * v5 * v17 - 6 * u36 * v2 * v5 * v17 -
                    6 * u26 * v3 * v5 * v17 + 24 * u6 * v2 * v3 * v5 * v17 -
                    6 * u6 * v23 * v5 * v17 + 2 * u36 * v25 * v17 -
                    6 * u6 * v3 * v25 * v17 + 2 * u26 * v35 * v17 -
                    6 * u6 * v2 * v35 * v17 + 2 * u6 * v235 * v17 +
                    2 * u235 * v6 * v17 - 6 * u35 * v2 * v6 * v17 -
                    6 * u25 * v3 * v6 * v17 + 24 * u5 * v2 * v3 * v6 * v17 -
                    6 * u5 * v23 * v6 * v17 - 6 * u23 * v5 * v6 * v17 +
                    24 * u3 * v2 * v5 * v6 * v17 +
                    24 * u2 * v3 * v5 * v6 * v17 -
                    120 * u * v2 * v3 * v5 * v6 * v17 +
                    24 * u * v23 * v5 * v6 * v17 - 6 * u3 * v25 * v6 * v17 +
                    24 * u * v3 * v25 * v6 * v17 - 6 * u2 * v35 * v6 * v17 +
                    24 * u * v2 * v35 * v6 * v17 - 6 * u * v235 * v6 * v17 +
                    2 * u35 * v26 * v17 - 6 * u5 * v3 * v26 * v17 -
                    6 * u3 * v5 * v26 * v17 + 24 * u * v3 * v5 * v26 * v17 -
                    6 * u * v35 * v26 * v17 + 2 * u25 * v36 * v17 -
                    6 * u5 * v2 * v36 * v17 - 6 * u2 * v5 * v36 * v17 +
                    24 * u * v2 * v5 * v36 * v17 - 6 * u * v25 * v36 * v17 +
                    2 * u5 * v236 * v17 - 6 * u * v5 * v236 * v17 +
                    2 * u23 * v56 * v17 - 6 * u3 * v2 * v56 * v17 -
                    6 * u2 * v3 * v56 * v17 + 24 * u * v2 * v3 * v56 * v17 -
                    6 * u * v23 * v56 * v17 + 2 * u3 * v256 * v17 -
                    6 * u * v3 * v256 * v17 + 2 * u2 * v356 * v17 -
                    6 * u * v2 * v356 * v17 + 2 * u * v2356 * v17 -
                    u1356 * v27 + 2 * u356 * v1 * v27 + 2 * u156 * v3 * v27 -
                    6 * u56 * v1 * v3 * v27 + 2 * u56 * v13 * v27 +
                    2 * u136 * v5 * v27 - 6 * u36 * v1 * v5 * v27 -
                    6 * u16 * v3 * v5 * v27 + 24 * u6 * v1 * v3 * v5 * v27 -
                    6 * u6 * v13 * v5 * v27 + 2 * u36 * v15 * v27 -
                    6 * u6 * v3 * v15 * v27 + 2 * u16 * v35 * v27 -
                    6 * u6 * v1 * v35 * v27 + 2 * u6 * v135 * v27 +
                    2 * u135 * v6 * v27 - 6 * u35 * v1 * v6 * v27 -
                    6 * u15 * v3 * v6 * v27 + 24 * u5 * v1 * v3 * v6 * v27 -
                    6 * u5 * v13 * v6 * v27 - 6 * u13 * v5 * v6 * v27 +
                    24 * u3 * v1 * v5 * v6 * v27 +
                    24 * u1 * v3 * v5 * v6 * v27 -
                    120 * u * v1 * v3 * v5 * v6 * v27 +
                    24 * u * v13 * v5 * v6 * v27 - 6 * u3 * v15 * v6 * v27 +
                    24 * u * v3 * v15 * v6 * v27 - 6 * u1 * v35 * v6 * v27 +
                    24 * u * v1 * v35 * v6 * v27 - 6 * u * v135 * v6 * v27 +
                    2 * u35 * v16 * v27 - 6 * u5 * v3 * v16 * v27 -
                    6 * u3 * v5 * v16 * v27 + 24 * u * v3 * v5 * v16 * v27 -
                    6 * u * v35 * v16 * v27 + 2 * u15 * v36 * v27 -
                    6 * u5 * v1 * v36 * v27 - 6 * u1 * v5 * v36 * v27 +
                    24 * u * v1 * v5 * v36 * v27 - 6 * u * v15 * v36 * v27 +
                    2 * u5 * v136 * v27 - 6 * u * v5 * v136 * v27 +
                    2 * u13 * v56 * v27 - 6 * u3 * v1 * v56 * v27 -
                    6 * u1 * v3 * v56 * v27 + 24 * u * v1 * v3 * v56 * v27 -
                    6 * u * v13 * v56 * v27 + 2 * u3 * v156 * v27 -
                    6 * u * v3 * v156 * v27 + 2 * u1 * v356 * v27 -
                    6 * u * v1 * v356 * v27 + 2 * u * v1356 * v27 -
                    u356 * v127 + 2 * u56 * v3 * v127 + 2 * u36 * v5 * v127 -
                    6 * u6 * v3 * v5 * v127 + 2 * u6 * v35 * v127 +
                    2 * u35 * v6 * v127 - 6 * u5 * v3 * v6 * v127 -
                    6 * u3 * v5 * v6 * v127 + 24 * u * v3 * v5 * v6 * v127 -
                    6 * u * v35 * v6 * v127 + 2 * u5 * v36 * v127 -
                    6 * u * v5 * v36 * v127 + 2 * u3 * v56 * v127 -
                    6 * u * v3 * v56 * v127 + 2 * u * v356 * v127 -
                    u1256 * v37 + 2 * u256 * v1 * v37 + 2 * u156 * v2 * v37 -
                    6 * u56 * v1 * v2 * v37 + 2 * u56 * v12 * v37 +
                    2 * u126 * v5 * v37 - 6 * u26 * v1 * v5 * v37 -
                    6 * u16 * v2 * v5 * v37 + 24 * u6 * v1 * v2 * v5 * v37 -
                    6 * u6 * v12 * v5 * v37 + 2 * u26 * v15 * v37 -
                    6 * u6 * v2 * v15 * v37 + 2 * u16 * v25 * v37 -
                    6 * u6 * v1 * v25 * v37 + 2 * u6 * v125 * v37 +
                    2 * u125 * v6 * v37 - 6 * u25 * v1 * v6 * v37 -
                    6 * u15 * v2 * v6 * v37 + 24 * u5 * v1 * v2 * v6 * v37 -
                    6 * u5 * v12 * v6 * v37 - 6 * u12 * v5 * v6 * v37 +
                    24 * u2 * v1 * v5 * v6 * v37 +
                    24 * u1 * v2 * v5 * v6 * v37 -
                    120 * u * v1 * v2 * v5 * v6 * v37 +
                    24 * u * v12 * v5 * v6 * v37 - 6 * u2 * v15 * v6 * v37 +
                    24 * u * v2 * v15 * v6 * v37 - 6 * u1 * v25 * v6 * v37 +
                    24 * u * v1 * v25 * v6 * v37 - 6 * u * v125 * v6 * v37 +
                    2 * u25 * v16 * v37 - 6 * u5 * v2 * v16 * v37 -
                    6 * u2 * v5 * v16 * v37 + 24 * u * v2 * v5 * v16 * v37 -
                    6 * u * v25 * v16 * v37 + 2 * u15 * v26 * v37 -
                    6 * u5 * v1 * v26 * v37 - 6 * u1 * v5 * v26 * v37 +
                    24 * u * v1 * v5 * v26 * v37 - 6 * u * v15 * v26 * v37 +
                    2 * u5 * v126 * v37 - 6 * u * v5 * v126 * v37 +
                    2 * u12 * v56 * v37 - 6 * u2 * v1 * v56 * v37 -
                    6 * u1 * v2 * v56 * v37 + 24 * u * v1 * v2 * v56 * v37 -
                    6 * u * v12 * v56 * v37 + 2 * u2 * v156 * v37 -
                    6 * u * v2 * v156 * v37 + 2 * u1 * v256 * v37 -
                    6 * u * v1 * v256 * v37 + 2 * u * v1256 * v37 -
                    u256 * v137 + 2 * u56 * v2 * v137 + 2 * u26 * v5 * v137 -
                    6 * u6 * v2 * v5 * v137 + 2 * u6 * v25 * v137 +
                    2 * u25 * v6 * v137 - 6 * u5 * v2 * v6 * v137 -
                    6 * u2 * v5 * v6 * v137 + 24 * u * v2 * v5 * v6 * v137 -
                    6 * u * v25 * v6 * v137 + 2 * u5 * v26 * v137 -
                    6 * u * v5 * v26 * v137 + 2 * u2 * v56 * v137 -
                    6 * u * v2 * v56 * v137 + 2 * u * v256 * v137 -
                    u156 * v237 + 2 * u56 * v1 * v237 + 2 * u16 * v5 * v237 -
                    6 * u6 * v1 * v5 * v237 + 2 * u6 * v15 * v237 +
                    2 * u15 * v6 * v237 - 6 * u5 * v1 * v6 * v237 -
                    6 * u1 * v5 * v6 * v237 + 24 * u * v1 * v5 * v6 * v237 -
                    6 * u * v15 * v6 * v237 + 2 * u5 * v16 * v237 -
                    6 * u * v5 * v16 * v237 + 2 * u1 * v56 * v237 -
                    6 * u * v1 * v56 * v237 + 2 * u * v156 * v237 -
                    u56 * v1237 + 2 * u6 * v5 * v1237 + 2 * u5 * v6 * v1237 -
                    6 * u * v5 * v6 * v1237 + 2 * u * v56 * v1237 -
                    u1236 * v57 + 2 * u236 * v1 * v57 + 2 * u136 * v2 * v57 -
                    6 * u36 * v1 * v2 * v57 + 2 * u36 * v12 * v57 +
                    2 * u126 * v3 * v57 - 6 * u26 * v1 * v3 * v57 -
                    6 * u16 * v2 * v3 * v57 + 24 * u6 * v1 * v2 * v3 * v57 -
                    6 * u6 * v12 * v3 * v57 + 2 * u26 * v13 * v57 -
                    6 * u6 * v2 * v13 * v57 + 2 * u16 * v23 * v57 -
                    6 * u6 * v1 * v23 * v57 + 2 * u6 * v123 * v57 +
                    2 * u123 * v6 * v57 - 6 * u23 * v1 * v6 * v57 -
                    6 * u13 * v2 * v6 * v57 + 24 * u3 * v1 * v2 * v6 * v57 -
                    6 * u3 * v12 * v6 * v57 - 6 * u12 * v3 * v6 * v57 +
                    24 * u2 * v1 * v3 * v6 * v57 +
                    24 * u1 * v2 * v3 * v6 * v57 -
                    120 * u * v1 * v2 * v3 * v6 * v57 +
                    24 * u * v12 * v3 * v6 * v57 - 6 * u2 * v13 * v6 * v57 +
                    24 * u * v2 * v13 * v6 * v57 - 6 * u1 * v23 * v6 * v57 +
                    24 * u * v1 * v23 * v6 * v57 - 6 * u * v123 * v6 * v57 +
                    2 * u23 * v16 * v57 - 6 * u3 * v2 * v16 * v57 -
                    6 * u2 * v3 * v16 * v57 + 24 * u * v2 * v3 * v16 * v57 -
                    6 * u * v23 * v16 * v57 + 2 * u13 * v26 * v57 -
                    6 * u3 * v1 * v26 * v57 - 6 * u1 * v3 * v26 * v57 +
                    24 * u * v1 * v3 * v26 * v57 - 6 * u * v13 * v26 * v57 +
                    2 * u3 * v126 * v57 - 6 * u * v3 * v126 * v57 +
                    2 * u12 * v36 * v57 - 6 * u2 * v1 * v36 * v57 -
                    6 * u1 * v2 * v36 * v57 + 24 * u * v1 * v2 * v36 * v57 -
                    6 * u * v12 * v36 * v57 + 2 * u2 * v136 * v57 -
                    6 * u * v2 * v136 * v57 + 2 * u1 * v236 * v57 -
                    6 * u * v1 * v236 * v57 + 2 * u * v1236 * v57 -
                    u236 * v157 + 2 * u36 * v2 * v157 + 2 * u26 * v3 * v157 -
                    6 * u6 * v2 * v3 * v157 + 2 * u6 * v23 * v157 +
                    2 * u23 * v6 * v157 - 6 * u3 * v2 * v6 * v157 -
                    6 * u2 * v3 * v6 * v157 + 24 * u * v2 * v3 * v6 * v157 -
                    6 * u * v23 * v6 * v157 + 2 * u3 * v26 * v157 -
                    6 * u * v3 * v26 * v157 + 2 * u2 * v36 * v157 -
                    6 * u * v2 * v36 * v157 + 2 * u * v236 * v157 -
                    u136 * v257 + 2 * u36 * v1 * v257 + 2 * u16 * v3 * v257 -
                    6 * u6 * v1 * v3 * v257 + 2 * u6 * v13 * v257 +
                    2 * u13 * v6 * v257 - 6 * u3 * v1 * v6 * v257 -
                    6 * u1 * v3 * v6 * v257 + 24 * u * v1 * v3 * v6 * v257 -
                    6 * u * v13 * v6 * v257 + 2 * u3 * v16 * v257 -
                    6 * u * v3 * v16 * v257 + 2 * u1 * v36 * v257 -
                    6 * u * v1 * v36 * v257 + 2 * u * v136 * v257 -
                    u36 * v1257 + 2 * u6 * v3 * v1257 + 2 * u3 * v6 * v1257 -
                    6 * u * v3 * v6 * v1257 + 2 * u * v36 * v1257 -
                    u126 * v357 + 2 * u26 * v1 * v357 + 2 * u16 * v2 * v357 -
                    6 * u6 * v1 * v2 * v357 + 2 * u6 * v12 * v357 +
                    2 * u12 * v6 * v357 - 6 * u2 * v1 * v6 * v357 -
                    6 * u1 * v2 * v6 * v357 + 24 * u * v1 * v2 * v6 * v357 -
                    6 * u * v12 * v6 * v357 + 2 * u2 * v16 * v357 -
                    6 * u * v2 * v16 * v357 + 2 * u1 * v26 * v357 -
                    6 * u * v1 * v26 * v357 + 2 * u * v126 * v357 -
                    u26 * v1357 + 2 * u6 * v2 * v1357 + 2 * u2 * v6 * v1357 -
                    6 * u * v2 * v6 * v1357 + 2 * u * v26 * v1357 -
                    u16 * v2357 + 2 * u6 * v1 * v2357 + 2 * u1 * v6 * v2357 -
                    6 * u * v1 * v6 * v2357 + 2 * u * v16 * v2357 -
                    u6 * v12357 + 2 * u * v6 * v12357 - u1235 * v67 +
                    2 * u235 * v1 * v67 + 2 * u135 * v2 * v67 -
                    6 * u35 * v1 * v2 * v67 + 2 * u35 * v12 * v67 +
                    2 * u125 * v3 * v67 - 6 * u25 * v1 * v3 * v67 -
                    6 * u15 * v2 * v3 * v67 + 24 * u5 * v1 * v2 * v3 * v67 -
                    6 * u5 * v12 * v3 * v67 + 2 * u25 * v13 * v67 -
                    6 * u5 * v2 * v13 * v67 + 2 * u15 * v23 * v67 -
                    6 * u5 * v1 * v23 * v67 + 2 * u5 * v123 * v67 +
                    2 * u123 * v5 * v67 - 6 * u23 * v1 * v5 * v67 -
                    6 * u13 * v2 * v5 * v67 + 24 * u3 * v1 * v2 * v5 * v67 -
                    6 * u3 * v12 * v5 * v67 - 6 * u12 * v3 * v5 * v67 +
                    24 * u2 * v1 * v3 * v5 * v67 +
                    24 * u1 * v2 * v3 * v5 * v67 -
                    120 * u * v1 * v2 * v3 * v5 * v67 +
                    24 * u * v12 * v3 * v5 * v67 - 6 * u2 * v13 * v5 * v67 +
                    24 * u * v2 * v13 * v5 * v67 - 6 * u1 * v23 * v5 * v67 +
                    24 * u * v1 * v23 * v5 * v67 - 6 * u * v123 * v5 * v67 +
                    2 * u23 * v15 * v67 - 6 * u3 * v2 * v15 * v67 -
                    6 * u2 * v3 * v15 * v67 + 24 * u * v2 * v3 * v15 * v67 -
                    6 * u * v23 * v15 * v67 + 2 * u13 * v25 * v67 -
                    6 * u3 * v1 * v25 * v67 - 6 * u1 * v3 * v25 * v67 +
                    24 * u * v1 * v3 * v25 * v67 - 6 * u * v13 * v25 * v67 +
                    2 * u3 * v125 * v67 - 6 * u * v3 * v125 * v67 +
                    2 * u12 * v35 * v67 - 6 * u2 * v1 * v35 * v67 -
                    6 * u1 * v2 * v35 * v67 + 24 * u * v1 * v2 * v35 * v67 -
                    6 * u * v12 * v35 * v67 + 2 * u2 * v135 * v67 -
                    6 * u * v2 * v135 * v67 + 2 * u1 * v235 * v67 -
                    6 * u * v1 * v235 * v67 + 2 * u * v1235 * v67 -
                    u235 * v167 + 2 * u35 * v2 * v167 + 2 * u25 * v3 * v167 -
                    6 * u5 * v2 * v3 * v167 + 2 * u5 * v23 * v167 +
                    2 * u23 * v5 * v167 - 6 * u3 * v2 * v5 * v167 -
                    6 * u2 * v3 * v5 * v167 + 24 * u * v2 * v3 * v5 * v167 -
                    6 * u * v23 * v5 * v167 + 2 * u3 * v25 * v167 -
                    6 * u * v3 * v25 * v167 + 2 * u2 * v35 * v167 -
                    6 * u * v2 * v35 * v167 + 2 * u * v235 * v167 -
                    u135 * v267 + 2 * u35 * v1 * v267 + 2 * u15 * v3 * v267 -
                    6 * u5 * v1 * v3 * v267 + 2 * u5 * v13 * v267 +
                    2 * u13 * v5 * v267 - 6 * u3 * v1 * v5 * v267 -
                    6 * u1 * v3 * v5 * v267 + 24 * u * v1 * v3 * v5 * v267 -
                    6 * u * v13 * v5 * v267 + 2 * u3 * v15 * v267 -
                    6 * u * v3 * v15 * v267 + 2 * u1 * v35 * v267 -
                    6 * u * v1 * v35 * v267 + 2 * u * v135 * v267 -
                    u35 * v1267 + 2 * u5 * v3 * v1267 + 2 * u3 * v5 * v1267 -
                    6 * u * v3 * v5 * v1267 + 2 * u * v35 * v1267 -
                    u125 * v367 + 2 * u25 * v1 * v367 + 2 * u15 * v2 * v367 -
                    6 * u5 * v1 * v2 * v367 + 2 * u5 * v12 * v367 +
                    2 * u12 * v5 * v367 - 6 * u2 * v1 * v5 * v367 -
                    6 * u1 * v2 * v5 * v367 + 24 * u * v1 * v2 * v5 * v367 -
                    6 * u * v12 * v5 * v367 + 2 * u2 * v15 * v367 -
                    6 * u * v2 * v15 * v367 + 2 * u1 * v25 * v367 -
                    6 * u * v1 * v25 * v367 + 2 * u * v125 * v367 -
                    u25 * v1367 + 2 * u5 * v2 * v1367 + 2 * u2 * v5 * v1367 -
                    6 * u * v2 * v5 * v1367 + 2 * u * v25 * v1367 -
                    u15 * v2367 + 2 * u5 * v1 * v2367 + 2 * u1 * v5 * v2367 -
                    6 * u * v1 * v5 * v2367 + 2 * u * v15 * v2367 -
                    u5 * v12367 + 2 * u * v5 * v12367 - u123 * v567 +
                    2 * u23 * v1 * v567 + 2 * u13 * v2 * v567 -
                    6 * u3 * v1 * v2 * v567 + 2 * u3 * v12 * v567 +
                    2 * u12 * v3 * v567 - 6 * u2 * v1 * v3 * v567 -
                    6 * u1 * v2 * v3 * v567 + 24 * u * v1 * v2 * v3 * v567 -
                    6 * u * v12 * v3 * v567 + 2 * u2 * v13 * v567 -
                    6 * u * v2 * v13 * v567 + 2 * u1 * v23 * v567 -
                    6 * u * v1 * v23 * v567 + 2 * u * v123 * v567 -
                    u23 * v1567 + 2 * u3 * v2 * v1567 + 2 * u2 * v3 * v1567 -
                    6 * u * v2 * v3 * v1567 + 2 * u * v23 * v1567 -
                    u13 * v2567 + 2 * u3 * v1 * v2567 + 2 * u1 * v3 * v2567 -
                    6 * u * v1 * v3 * v2567 + 2 * u * v13 * v2567 -
                    u3 * v12567 + 2 * u * v3 * v12567 - u12 * v3567 +
                    2 * u2 * v1 * v3567 + 2 * u1 * v2 * v3567 -
                    6 * u * v1 * v2 * v3567 + 2 * u * v12 * v3567 -
                    u2 * v13567 + 2 * u * v2 * v13567 - u1 * v23567 +
                    2 * u * v1 * v23567 - u * v123567,
            .dual4567 = u4567 - u567 * v4 - u467 * v5 + 2 * u67 * v4 * v5 -
                        u67 * v45 - u457 * v6 + 2 * u57 * v4 * v6 +
                        2 * u47 * v5 * v6 - 6 * u7 * v4 * v5 * v6 +
                        2 * u7 * v45 * v6 - u57 * v46 + 2 * u7 * v5 * v46 -
                        u47 * v56 + 2 * u7 * v4 * v56 - u7 * v456 - u456 * v7 +
                        2 * u56 * v4 * v7 + 2 * u46 * v5 * v7 -
                        6 * u6 * v4 * v5 * v7 + 2 * u6 * v45 * v7 +
                        2 * u45 * v6 * v7 - 6 * u5 * v4 * v6 * v7 -
                        6 * u4 * v5 * v6 * v7 + 24 * u * v4 * v5 * v6 * v7 -
                        6 * u * v45 * v6 * v7 + 2 * u5 * v46 * v7 -
                        6 * u * v5 * v46 * v7 + 2 * u4 * v56 * v7 -
                        6 * u * v4 * v56 * v7 + 2 * u * v456 * v7 - u56 * v47 +
                        2 * u6 * v5 * v47 + 2 * u5 * v6 * v47 -
                        6 * u * v5 * v6 * v47 + 2 * u * v56 * v47 - u46 * v57 +
                        2 * u6 * v4 * v57 + 2 * u4 * v6 * v57 -
                        6 * u * v4 * v6 * v57 + 2 * u * v46 * v57 - u6 * v457 +
                        2 * u * v6 * v457 - u45 * v67 + 2 * u5 * v4 * v67 +
                        2 * u4 * v5 * v67 - 6 * u * v4 * v5 * v67 +
                        2 * u * v45 * v67 - u5 * v467 + 2 * u * v5 * v467 -
                        u4 * v567 + 2 * u * v4 * v567 - u * v4567,
            .dual14567 =
                    u14567 - u4567 * v1 - u1567 * v4 + 2 * u567 * v1 * v4 -
                    u567 * v14 - u1467 * v5 + 2 * u467 * v1 * v5 +
                    2 * u167 * v4 * v5 - 6 * u67 * v1 * v4 * v5 +
                    2 * u67 * v14 * v5 - u467 * v15 + 2 * u67 * v4 * v15 -
                    u167 * v45 + 2 * u67 * v1 * v45 - u67 * v145 - u1457 * v6 +
                    2 * u457 * v1 * v6 + 2 * u157 * v4 * v6 -
                    6 * u57 * v1 * v4 * v6 + 2 * u57 * v14 * v6 +
                    2 * u147 * v5 * v6 - 6 * u47 * v1 * v5 * v6 -
                    6 * u17 * v4 * v5 * v6 + 24 * u7 * v1 * v4 * v5 * v6 -
                    6 * u7 * v14 * v5 * v6 + 2 * u47 * v15 * v6 -
                    6 * u7 * v4 * v15 * v6 + 2 * u17 * v45 * v6 -
                    6 * u7 * v1 * v45 * v6 + 2 * u7 * v145 * v6 - u457 * v16 +
                    2 * u57 * v4 * v16 + 2 * u47 * v5 * v16 -
                    6 * u7 * v4 * v5 * v16 + 2 * u7 * v45 * v16 - u157 * v46 +
                    2 * u57 * v1 * v46 + 2 * u17 * v5 * v46 -
                    6 * u7 * v1 * v5 * v46 + 2 * u7 * v15 * v46 - u57 * v146 +
                    2 * u7 * v5 * v146 - u147 * v56 + 2 * u47 * v1 * v56 +
                    2 * u17 * v4 * v56 - 6 * u7 * v1 * v4 * v56 +
                    2 * u7 * v14 * v56 - u47 * v156 + 2 * u7 * v4 * v156 -
                    u17 * v456 + 2 * u7 * v1 * v456 - u7 * v1456 - u1456 * v7 +
                    2 * u456 * v1 * v7 + 2 * u156 * v4 * v7 -
                    6 * u56 * v1 * v4 * v7 + 2 * u56 * v14 * v7 +
                    2 * u146 * v5 * v7 - 6 * u46 * v1 * v5 * v7 -
                    6 * u16 * v4 * v5 * v7 + 24 * u6 * v1 * v4 * v5 * v7 -
                    6 * u6 * v14 * v5 * v7 + 2 * u46 * v15 * v7 -
                    6 * u6 * v4 * v15 * v7 + 2 * u16 * v45 * v7 -
                    6 * u6 * v1 * v45 * v7 + 2 * u6 * v145 * v7 +
                    2 * u145 * v6 * v7 - 6 * u45 * v1 * v6 * v7 -
                    6 * u15 * v4 * v6 * v7 + 24 * u5 * v1 * v4 * v6 * v7 -
                    6 * u5 * v14 * v6 * v7 - 6 * u14 * v5 * v6 * v7 +
                    24 * u4 * v1 * v5 * v6 * v7 + 24 * u1 * v4 * v5 * v6 * v7 -
                    120 * u * v1 * v4 * v5 * v6 * v7 +
                    24 * u * v14 * v5 * v6 * v7 - 6 * u4 * v15 * v6 * v7 +
                    24 * u * v4 * v15 * v6 * v7 - 6 * u1 * v45 * v6 * v7 +
                    24 * u * v1 * v45 * v6 * v7 - 6 * u * v145 * v6 * v7 +
                    2 * u45 * v16 * v7 - 6 * u5 * v4 * v16 * v7 -
                    6 * u4 * v5 * v16 * v7 + 24 * u * v4 * v5 * v16 * v7 -
                    6 * u * v45 * v16 * v7 + 2 * u15 * v46 * v7 -
                    6 * u5 * v1 * v46 * v7 - 6 * u1 * v5 * v46 * v7 +
                    24 * u * v1 * v5 * v46 * v7 - 6 * u * v15 * v46 * v7 +
                    2 * u5 * v146 * v7 - 6 * u * v5 * v146 * v7 +
                    2 * u14 * v56 * v7 - 6 * u4 * v1 * v56 * v7 -
                    6 * u1 * v4 * v56 * v7 + 24 * u * v1 * v4 * v56 * v7 -
                    6 * u * v14 * v56 * v7 + 2 * u4 * v156 * v7 -
                    6 * u * v4 * v156 * v7 + 2 * u1 * v456 * v7 -
                    6 * u * v1 * v456 * v7 + 2 * u * v1456 * v7 - u456 * v17 +
                    2 * u56 * v4 * v17 + 2 * u46 * v5 * v17 -
                    6 * u6 * v4 * v5 * v17 + 2 * u6 * v45 * v17 +
                    2 * u45 * v6 * v17 - 6 * u5 * v4 * v6 * v17 -
                    6 * u4 * v5 * v6 * v17 + 24 * u * v4 * v5 * v6 * v17 -
                    6 * u * v45 * v6 * v17 + 2 * u5 * v46 * v17 -
                    6 * u * v5 * v46 * v17 + 2 * u4 * v56 * v17 -
                    6 * u * v4 * v56 * v17 + 2 * u * v456 * v17 - u156 * v47 +
                    2 * u56 * v1 * v47 + 2 * u16 * v5 * v47 -
                    6 * u6 * v1 * v5 * v47 + 2 * u6 * v15 * v47 +
                    2 * u15 * v6 * v47 - 6 * u5 * v1 * v6 * v47 -
                    6 * u1 * v5 * v6 * v47 + 24 * u * v1 * v5 * v6 * v47 -
                    6 * u * v15 * v6 * v47 + 2 * u5 * v16 * v47 -
                    6 * u * v5 * v16 * v47 + 2 * u1 * v56 * v47 -
                    6 * u * v1 * v56 * v47 + 2 * u * v156 * v47 - u56 * v147 +
                    2 * u6 * v5 * v147 + 2 * u5 * v6 * v147 -
                    6 * u * v5 * v6 * v147 + 2 * u * v56 * v147 - u146 * v57 +
                    2 * u46 * v1 * v57 + 2 * u16 * v4 * v57 -
                    6 * u6 * v1 * v4 * v57 + 2 * u6 * v14 * v57 +
                    2 * u14 * v6 * v57 - 6 * u4 * v1 * v6 * v57 -
                    6 * u1 * v4 * v6 * v57 + 24 * u * v1 * v4 * v6 * v57 -
                    6 * u * v14 * v6 * v57 + 2 * u4 * v16 * v57 -
                    6 * u * v4 * v16 * v57 + 2 * u1 * v46 * v57 -
                    6 * u * v1 * v46 * v57 + 2 * u * v146 * v57 - u46 * v157 +
                    2 * u6 * v4 * v157 + 2 * u4 * v6 * v157 -
                    6 * u * v4 * v6 * v157 + 2 * u * v46 * v157 - u16 * v457 +
                    2 * u6 * v1 * v457 + 2 * u1 * v6 * v457 -
                    6 * u * v1 * v6 * v457 + 2 * u * v16 * v457 - u6 * v1457 +
                    2 * u * v6 * v1457 - u145 * v67 + 2 * u45 * v1 * v67 +
                    2 * u15 * v4 * v67 - 6 * u5 * v1 * v4 * v67 +
                    2 * u5 * v14 * v67 + 2 * u14 * v5 * v67 -
                    6 * u4 * v1 * v5 * v67 - 6 * u1 * v4 * v5 * v67 +
                    24 * u * v1 * v4 * v5 * v67 - 6 * u * v14 * v5 * v67 +
                    2 * u4 * v15 * v67 - 6 * u * v4 * v15 * v67 +
                    2 * u1 * v45 * v67 - 6 * u * v1 * v45 * v67 +
                    2 * u * v145 * v67 - u45 * v167 + 2 * u5 * v4 * v167 +
                    2 * u4 * v5 * v167 - 6 * u * v4 * v5 * v167 +
                    2 * u * v45 * v167 - u15 * v467 + 2 * u5 * v1 * v467 +
                    2 * u1 * v5 * v467 - 6 * u * v1 * v5 * v467 +
                    2 * u * v15 * v467 - u5 * v1467 + 2 * u * v5 * v1467 -
                    u14 * v567 + 2 * u4 * v1 * v567 + 2 * u1 * v4 * v567 -
                    6 * u * v1 * v4 * v567 + 2 * u * v14 * v567 - u4 * v1567 +
                    2 * u * v4 * v1567 - u1 * v4567 + 2 * u * v1 * v4567 -
                    u * v14567,
            .dual24567 =
                    u24567 - u4567 * v2 - u2567 * v4 + 2 * u567 * v2 * v4 -
                    u567 * v24 - u2467 * v5 + 2 * u467 * v2 * v5 +
                    2 * u267 * v4 * v5 - 6 * u67 * v2 * v4 * v5 +
                    2 * u67 * v24 * v5 - u467 * v25 + 2 * u67 * v4 * v25 -
                    u267 * v45 + 2 * u67 * v2 * v45 - u67 * v245 - u2457 * v6 +
                    2 * u457 * v2 * v6 + 2 * u257 * v4 * v6 -
                    6 * u57 * v2 * v4 * v6 + 2 * u57 * v24 * v6 +
                    2 * u247 * v5 * v6 - 6 * u47 * v2 * v5 * v6 -
                    6 * u27 * v4 * v5 * v6 + 24 * u7 * v2 * v4 * v5 * v6 -
                    6 * u7 * v24 * v5 * v6 + 2 * u47 * v25 * v6 -
                    6 * u7 * v4 * v25 * v6 + 2 * u27 * v45 * v6 -
                    6 * u7 * v2 * v45 * v6 + 2 * u7 * v245 * v6 - u457 * v26 +
                    2 * u57 * v4 * v26 + 2 * u47 * v5 * v26 -
                    6 * u7 * v4 * v5 * v26 + 2 * u7 * v45 * v26 - u257 * v46 +
                    2 * u57 * v2 * v46 + 2 * u27 * v5 * v46 -
                    6 * u7 * v2 * v5 * v46 + 2 * u7 * v25 * v46 - u57 * v246 +
                    2 * u7 * v5 * v246 - u247 * v56 + 2 * u47 * v2 * v56 +
                    2 * u27 * v4 * v56 - 6 * u7 * v2 * v4 * v56 +
                    2 * u7 * v24 * v56 - u47 * v256 + 2 * u7 * v4 * v256 -
                    u27 * v456 + 2 * u7 * v2 * v456 - u7 * v2456 - u2456 * v7 +
                    2 * u456 * v2 * v7 + 2 * u256 * v4 * v7 -
                    6 * u56 * v2 * v4 * v7 + 2 * u56 * v24 * v7 +
                    2 * u246 * v5 * v7 - 6 * u46 * v2 * v5 * v7 -
                    6 * u26 * v4 * v5 * v7 + 24 * u6 * v2 * v4 * v5 * v7 -
                    6 * u6 * v24 * v5 * v7 + 2 * u46 * v25 * v7 -
                    6 * u6 * v4 * v25 * v7 + 2 * u26 * v45 * v7 -
                    6 * u6 * v2 * v45 * v7 + 2 * u6 * v245 * v7 +
                    2 * u245 * v6 * v7 - 6 * u45 * v2 * v6 * v7 -
                    6 * u25 * v4 * v6 * v7 + 24 * u5 * v2 * v4 * v6 * v7 -
                    6 * u5 * v24 * v6 * v7 - 6 * u24 * v5 * v6 * v7 +
                    24 * u4 * v2 * v5 * v6 * v7 + 24 * u2 * v4 * v5 * v6 * v7 -
                    120 * u * v2 * v4 * v5 * v6 * v7 +
                    24 * u * v24 * v5 * v6 * v7 - 6 * u4 * v25 * v6 * v7 +
                    24 * u * v4 * v25 * v6 * v7 - 6 * u2 * v45 * v6 * v7 +
                    24 * u * v2 * v45 * v6 * v7 - 6 * u * v245 * v6 * v7 +
                    2 * u45 * v26 * v7 - 6 * u5 * v4 * v26 * v7 -
                    6 * u4 * v5 * v26 * v7 + 24 * u * v4 * v5 * v26 * v7 -
                    6 * u * v45 * v26 * v7 + 2 * u25 * v46 * v7 -
                    6 * u5 * v2 * v46 * v7 - 6 * u2 * v5 * v46 * v7 +
                    24 * u * v2 * v5 * v46 * v7 - 6 * u * v25 * v46 * v7 +
                    2 * u5 * v246 * v7 - 6 * u * v5 * v246 * v7 +
                    2 * u24 * v56 * v7 - 6 * u4 * v2 * v56 * v7 -
                    6 * u2 * v4 * v56 * v7 + 24 * u * v2 * v4 * v56 * v7 -
                    6 * u * v24 * v56 * v7 + 2 * u4 * v256 * v7 -
                    6 * u * v4 * v256 * v7 + 2 * u2 * v456 * v7 -
                    6 * u * v2 * v456 * v7 + 2 * u * v2456 * v7 - u456 * v27 +
                    2 * u56 * v4 * v27 + 2 * u46 * v5 * v27 -
                    6 * u6 * v4 * v5 * v27 + 2 * u6 * v45 * v27 +
                    2 * u45 * v6 * v27 - 6 * u5 * v4 * v6 * v27 -
                    6 * u4 * v5 * v6 * v27 + 24 * u * v4 * v5 * v6 * v27 -
                    6 * u * v45 * v6 * v27 + 2 * u5 * v46 * v27 -
                    6 * u * v5 * v46 * v27 + 2 * u4 * v56 * v27 -
                    6 * u * v4 * v56 * v27 + 2 * u * v456 * v27 - u256 * v47 +
                    2 * u56 * v2 * v47 + 2 * u26 * v5 * v47 -
                    6 * u6 * v2 * v5 * v47 + 2 * u6 * v25 * v47 +
                    2 * u25 * v6 * v47 - 6 * u5 * v2 * v6 * v47 -
                    6 * u2 * v5 * v6 * v47 + 24 * u * v2 * v5 * v6 * v47 -
                    6 * u * v25 * v6 * v47 + 2 * u5 * v26 * v47 -
                    6 * u * v5 * v26 * v47 + 2 * u2 * v56 * v47 -
                    6 * u * v2 * v56 * v47 + 2 * u * v256 * v47 - u56 * v247 +
                    2 * u6 * v5 * v247 + 2 * u5 * v6 * v247 -
                    6 * u * v5 * v6 * v247 + 2 * u * v56 * v247 - u246 * v57 +
                    2 * u46 * v2 * v57 + 2 * u26 * v4 * v57 -
                    6 * u6 * v2 * v4 * v57 + 2 * u6 * v24 * v57 +
                    2 * u24 * v6 * v57 - 6 * u4 * v2 * v6 * v57 -
                    6 * u2 * v4 * v6 * v57 + 24 * u * v2 * v4 * v6 * v57 -
                    6 * u * v24 * v6 * v57 + 2 * u4 * v26 * v57 -
                    6 * u * v4 * v26 * v57 + 2 * u2 * v46 * v57 -
                    6 * u * v2 * v46 * v57 + 2 * u * v246 * v57 - u46 * v257 +
                    2 * u6 * v4 * v257 + 2 * u4 * v6 * v257 -
                    6 * u * v4 * v6 * v257 + 2 * u * v46 * v257 - u26 * v457 +
                    2 * u6 * v2 * v457 + 2 * u2 * v6 * v457 -
                    6 * u * v2 * v6 * v457 + 2 * u * v26 * v457 - u6 * v2457 +
                    2 * u * v6 * v2457 - u245 * v67 + 2 * u45 * v2 * v67 +
                    2 * u25 * v4 * v67 - 6 * u5 * v2 * v4 * v67 +
                    2 * u5 * v24 * v67 + 2 * u24 * v5 * v67 -
                    6 * u4 * v2 * v5 * v67 - 6 * u2 * v4 * v5 * v67 +
                    24 * u * v2 * v4 * v5 * v67 - 6 * u * v24 * v5 * v67 +
                    2 * u4 * v25 * v67 - 6 * u * v4 * v25 * v67 +
                    2 * u2 * v45 * v67 - 6 * u * v2 * v45 * v67 +
                    2 * u * v245 * v67 - u45 * v267 + 2 * u5 * v4 * v267 +
                    2 * u4 * v5 * v267 - 6 * u * v4 * v5 * v267 +
                    2 * u * v45 * v267 - u25 * v467 + 2 * u5 * v2 * v467 +
                    2 * u2 * v5 * v467 - 6 * u * v2 * v5 * v467 +
                    2 * u * v25 * v467 - u5 * v2467 + 2 * u * v5 * v2467 -
                    u24 * v567 + 2 * u4 * v2 * v567 + 2 * u2 * v4 * v567 -
                    6 * u * v2 * v4 * v567 + 2 * u * v24 * v567 - u4 * v2567 +
                    2 * u * v4 * v2567 - u2 * v4567 + 2 * u * v2 * v4567 -
                    u * v24567,
            .dual124567 =
                    u124567 - u24567 * v1 - u14567 * v2 + 2 * u4567 * v1 * v2 -
                    u4567 * v12 - u12567 * v4 + 2 * u2567 * v1 * v4 +
                    2 * u1567 * v2 * v4 - 6 * u567 * v1 * v2 * v4 +
                    2 * u567 * v12 * v4 - u2567 * v14 + 2 * u567 * v2 * v14 -
                    u1567 * v24 + 2 * u567 * v1 * v24 - u567 * v124 -
                    u12467 * v5 + 2 * u2467 * v1 * v5 + 2 * u1467 * v2 * v5 -
                    6 * u467 * v1 * v2 * v5 + 2 * u467 * v12 * v5 +
                    2 * u1267 * v4 * v5 - 6 * u267 * v1 * v4 * v5 -
                    6 * u167 * v2 * v4 * v5 + 24 * u67 * v1 * v2 * v4 * v5 -
                    6 * u67 * v12 * v4 * v5 + 2 * u267 * v14 * v5 -
                    6 * u67 * v2 * v14 * v5 + 2 * u167 * v24 * v5 -
                    6 * u67 * v1 * v24 * v5 + 2 * u67 * v124 * v5 -
                    u2467 * v15 + 2 * u467 * v2 * v15 + 2 * u267 * v4 * v15 -
                    6 * u67 * v2 * v4 * v15 + 2 * u67 * v24 * v15 -
                    u1467 * v25 + 2 * u467 * v1 * v25 + 2 * u167 * v4 * v25 -
                    6 * u67 * v1 * v4 * v25 + 2 * u67 * v14 * v25 -
                    u467 * v125 + 2 * u67 * v4 * v125 - u1267 * v45 +
                    2 * u267 * v1 * v45 + 2 * u167 * v2 * v45 -
                    6 * u67 * v1 * v2 * v45 + 2 * u67 * v12 * v45 -
                    u267 * v145 + 2 * u67 * v2 * v145 - u167 * v245 +
                    2 * u67 * v1 * v245 - u67 * v1245 - u12457 * v6 +
                    2 * u2457 * v1 * v6 + 2 * u1457 * v2 * v6 -
                    6 * u457 * v1 * v2 * v6 + 2 * u457 * v12 * v6 +
                    2 * u1257 * v4 * v6 - 6 * u257 * v1 * v4 * v6 -
                    6 * u157 * v2 * v4 * v6 + 24 * u57 * v1 * v2 * v4 * v6 -
                    6 * u57 * v12 * v4 * v6 + 2 * u257 * v14 * v6 -
                    6 * u57 * v2 * v14 * v6 + 2 * u157 * v24 * v6 -
                    6 * u57 * v1 * v24 * v6 + 2 * u57 * v124 * v6 +
                    2 * u1247 * v5 * v6 - 6 * u247 * v1 * v5 * v6 -
                    6 * u147 * v2 * v5 * v6 + 24 * u47 * v1 * v2 * v5 * v6 -
                    6 * u47 * v12 * v5 * v6 - 6 * u127 * v4 * v5 * v6 +
                    24 * u27 * v1 * v4 * v5 * v6 +
                    24 * u17 * v2 * v4 * v5 * v6 -
                    120 * u7 * v1 * v2 * v4 * v5 * v6 +
                    24 * u7 * v12 * v4 * v5 * v6 - 6 * u27 * v14 * v5 * v6 +
                    24 * u7 * v2 * v14 * v5 * v6 - 6 * u17 * v24 * v5 * v6 +
                    24 * u7 * v1 * v24 * v5 * v6 - 6 * u7 * v124 * v5 * v6 +
                    2 * u247 * v15 * v6 - 6 * u47 * v2 * v15 * v6 -
                    6 * u27 * v4 * v15 * v6 + 24 * u7 * v2 * v4 * v15 * v6 -
                    6 * u7 * v24 * v15 * v6 + 2 * u147 * v25 * v6 -
                    6 * u47 * v1 * v25 * v6 - 6 * u17 * v4 * v25 * v6 +
                    24 * u7 * v1 * v4 * v25 * v6 - 6 * u7 * v14 * v25 * v6 +
                    2 * u47 * v125 * v6 - 6 * u7 * v4 * v125 * v6 +
                    2 * u127 * v45 * v6 - 6 * u27 * v1 * v45 * v6 -
                    6 * u17 * v2 * v45 * v6 + 24 * u7 * v1 * v2 * v45 * v6 -
                    6 * u7 * v12 * v45 * v6 + 2 * u27 * v145 * v6 -
                    6 * u7 * v2 * v145 * v6 + 2 * u17 * v245 * v6 -
                    6 * u7 * v1 * v245 * v6 + 2 * u7 * v1245 * v6 -
                    u2457 * v16 + 2 * u457 * v2 * v16 + 2 * u257 * v4 * v16 -
                    6 * u57 * v2 * v4 * v16 + 2 * u57 * v24 * v16 +
                    2 * u247 * v5 * v16 - 6 * u47 * v2 * v5 * v16 -
                    6 * u27 * v4 * v5 * v16 + 24 * u7 * v2 * v4 * v5 * v16 -
                    6 * u7 * v24 * v5 * v16 + 2 * u47 * v25 * v16 -
                    6 * u7 * v4 * v25 * v16 + 2 * u27 * v45 * v16 -
                    6 * u7 * v2 * v45 * v16 + 2 * u7 * v245 * v16 -
                    u1457 * v26 + 2 * u457 * v1 * v26 + 2 * u157 * v4 * v26 -
                    6 * u57 * v1 * v4 * v26 + 2 * u57 * v14 * v26 +
                    2 * u147 * v5 * v26 - 6 * u47 * v1 * v5 * v26 -
                    6 * u17 * v4 * v5 * v26 + 24 * u7 * v1 * v4 * v5 * v26 -
                    6 * u7 * v14 * v5 * v26 + 2 * u47 * v15 * v26 -
                    6 * u7 * v4 * v15 * v26 + 2 * u17 * v45 * v26 -
                    6 * u7 * v1 * v45 * v26 + 2 * u7 * v145 * v26 -
                    u457 * v126 + 2 * u57 * v4 * v126 + 2 * u47 * v5 * v126 -
                    6 * u7 * v4 * v5 * v126 + 2 * u7 * v45 * v126 -
                    u1257 * v46 + 2 * u257 * v1 * v46 + 2 * u157 * v2 * v46 -
                    6 * u57 * v1 * v2 * v46 + 2 * u57 * v12 * v46 +
                    2 * u127 * v5 * v46 - 6 * u27 * v1 * v5 * v46 -
                    6 * u17 * v2 * v5 * v46 + 24 * u7 * v1 * v2 * v5 * v46 -
                    6 * u7 * v12 * v5 * v46 + 2 * u27 * v15 * v46 -
                    6 * u7 * v2 * v15 * v46 + 2 * u17 * v25 * v46 -
                    6 * u7 * v1 * v25 * v46 + 2 * u7 * v125 * v46 -
                    u257 * v146 + 2 * u57 * v2 * v146 + 2 * u27 * v5 * v146 -
                    6 * u7 * v2 * v5 * v146 + 2 * u7 * v25 * v146 -
                    u157 * v246 + 2 * u57 * v1 * v246 + 2 * u17 * v5 * v246 -
                    6 * u7 * v1 * v5 * v246 + 2 * u7 * v15 * v246 -
                    u57 * v1246 + 2 * u7 * v5 * v1246 - u1247 * v56 +
                    2 * u247 * v1 * v56 + 2 * u147 * v2 * v56 -
                    6 * u47 * v1 * v2 * v56 + 2 * u47 * v12 * v56 +
                    2 * u127 * v4 * v56 - 6 * u27 * v1 * v4 * v56 -
                    6 * u17 * v2 * v4 * v56 + 24 * u7 * v1 * v2 * v4 * v56 -
                    6 * u7 * v12 * v4 * v56 + 2 * u27 * v14 * v56 -
                    6 * u7 * v2 * v14 * v56 + 2 * u17 * v24 * v56 -
                    6 * u7 * v1 * v24 * v56 + 2 * u7 * v124 * v56 -
                    u247 * v156 + 2 * u47 * v2 * v156 + 2 * u27 * v4 * v156 -
                    6 * u7 * v2 * v4 * v156 + 2 * u7 * v24 * v156 -
                    u147 * v256 + 2 * u47 * v1 * v256 + 2 * u17 * v4 * v256 -
                    6 * u7 * v1 * v4 * v256 + 2 * u7 * v14 * v256 -
                    u47 * v1256 + 2 * u7 * v4 * v1256 - u127 * v456 +
                    2 * u27 * v1 * v456 + 2 * u17 * v2 * v456 -
                    6 * u7 * v1 * v2 * v456 + 2 * u7 * v12 * v456 -
                    u27 * v1456 + 2 * u7 * v2 * v1456 - u17 * v2456 +
                    2 * u7 * v1 * v2456 - u7 * v12456 - u12456 * v7 +
                    2 * u2456 * v1 * v7 + 2 * u1456 * v2 * v7 -
                    6 * u456 * v1 * v2 * v7 + 2 * u456 * v12 * v7 +
                    2 * u1256 * v4 * v7 - 6 * u256 * v1 * v4 * v7 -
                    6 * u156 * v2 * v4 * v7 + 24 * u56 * v1 * v2 * v4 * v7 -
                    6 * u56 * v12 * v4 * v7 + 2 * u256 * v14 * v7 -
                    6 * u56 * v2 * v14 * v7 + 2 * u156 * v24 * v7 -
                    6 * u56 * v1 * v24 * v7 + 2 * u56 * v124 * v7 +
                    2 * u1246 * v5 * v7 - 6 * u246 * v1 * v5 * v7 -
                    6 * u146 * v2 * v5 * v7 + 24 * u46 * v1 * v2 * v5 * v7 -
                    6 * u46 * v12 * v5 * v7 - 6 * u126 * v4 * v5 * v7 +
                    24 * u26 * v1 * v4 * v5 * v7 +
                    24 * u16 * v2 * v4 * v5 * v7 -
                    120 * u6 * v1 * v2 * v4 * v5 * v7 +
                    24 * u6 * v12 * v4 * v5 * v7 - 6 * u26 * v14 * v5 * v7 +
                    24 * u6 * v2 * v14 * v5 * v7 - 6 * u16 * v24 * v5 * v7 +
                    24 * u6 * v1 * v24 * v5 * v7 - 6 * u6 * v124 * v5 * v7 +
                    2 * u246 * v15 * v7 - 6 * u46 * v2 * v15 * v7 -
                    6 * u26 * v4 * v15 * v7 + 24 * u6 * v2 * v4 * v15 * v7 -
                    6 * u6 * v24 * v15 * v7 + 2 * u146 * v25 * v7 -
                    6 * u46 * v1 * v25 * v7 - 6 * u16 * v4 * v25 * v7 +
                    24 * u6 * v1 * v4 * v25 * v7 - 6 * u6 * v14 * v25 * v7 +
                    2 * u46 * v125 * v7 - 6 * u6 * v4 * v125 * v7 +
                    2 * u126 * v45 * v7 - 6 * u26 * v1 * v45 * v7 -
                    6 * u16 * v2 * v45 * v7 + 24 * u6 * v1 * v2 * v45 * v7 -
                    6 * u6 * v12 * v45 * v7 + 2 * u26 * v145 * v7 -
                    6 * u6 * v2 * v145 * v7 + 2 * u16 * v245 * v7 -
                    6 * u6 * v1 * v245 * v7 + 2 * u6 * v1245 * v7 +
                    2 * u1245 * v6 * v7 - 6 * u245 * v1 * v6 * v7 -
                    6 * u145 * v2 * v6 * v7 + 24 * u45 * v1 * v2 * v6 * v7 -
                    6 * u45 * v12 * v6 * v7 - 6 * u125 * v4 * v6 * v7 +
                    24 * u25 * v1 * v4 * v6 * v7 +
                    24 * u15 * v2 * v4 * v6 * v7 -
                    120 * u5 * v1 * v2 * v4 * v6 * v7 +
                    24 * u5 * v12 * v4 * v6 * v7 - 6 * u25 * v14 * v6 * v7 +
                    24 * u5 * v2 * v14 * v6 * v7 - 6 * u15 * v24 * v6 * v7 +
                    24 * u5 * v1 * v24 * v6 * v7 - 6 * u5 * v124 * v6 * v7 -
                    6 * u124 * v5 * v6 * v7 + 24 * u24 * v1 * v5 * v6 * v7 +
                    24 * u14 * v2 * v5 * v6 * v7 -
                    120 * u4 * v1 * v2 * v5 * v6 * v7 +
                    24 * u4 * v12 * v5 * v6 * v7 +
                    24 * u12 * v4 * v5 * v6 * v7 -
                    120 * u2 * v1 * v4 * v5 * v6 * v7 -
                    120 * u1 * v2 * v4 * v5 * v6 * v7 +
                    720 * u * v1 * v2 * v4 * v5 * v6 * v7 -
                    120 * u * v12 * v4 * v5 * v6 * v7 +
                    24 * u2 * v14 * v5 * v6 * v7 -
                    120 * u * v2 * v14 * v5 * v6 * v7 +
                    24 * u1 * v24 * v5 * v6 * v7 -
                    120 * u * v1 * v24 * v5 * v6 * v7 +
                    24 * u * v124 * v5 * v6 * v7 - 6 * u24 * v15 * v6 * v7 +
                    24 * u4 * v2 * v15 * v6 * v7 +
                    24 * u2 * v4 * v15 * v6 * v7 -
                    120 * u * v2 * v4 * v15 * v6 * v7 +
                    24 * u * v24 * v15 * v6 * v7 - 6 * u14 * v25 * v6 * v7 +
                    24 * u4 * v1 * v25 * v6 * v7 +
                    24 * u1 * v4 * v25 * v6 * v7 -
                    120 * u * v1 * v4 * v25 * v6 * v7 +
                    24 * u * v14 * v25 * v6 * v7 - 6 * u4 * v125 * v6 * v7 +
                    24 * u * v4 * v125 * v6 * v7 - 6 * u12 * v45 * v6 * v7 +
                    24 * u2 * v1 * v45 * v6 * v7 +
                    24 * u1 * v2 * v45 * v6 * v7 -
                    120 * u * v1 * v2 * v45 * v6 * v7 +
                    24 * u * v12 * v45 * v6 * v7 - 6 * u2 * v145 * v6 * v7 +
                    24 * u * v2 * v145 * v6 * v7 - 6 * u1 * v245 * v6 * v7 +
                    24 * u * v1 * v245 * v6 * v7 - 6 * u * v1245 * v6 * v7 +
                    2 * u245 * v16 * v7 - 6 * u45 * v2 * v16 * v7 -
                    6 * u25 * v4 * v16 * v7 + 24 * u5 * v2 * v4 * v16 * v7 -
                    6 * u5 * v24 * v16 * v7 - 6 * u24 * v5 * v16 * v7 +
                    24 * u4 * v2 * v5 * v16 * v7 +
                    24 * u2 * v4 * v5 * v16 * v7 -
                    120 * u * v2 * v4 * v5 * v16 * v7 +
                    24 * u * v24 * v5 * v16 * v7 - 6 * u4 * v25 * v16 * v7 +
                    24 * u * v4 * v25 * v16 * v7 - 6 * u2 * v45 * v16 * v7 +
                    24 * u * v2 * v45 * v16 * v7 - 6 * u * v245 * v16 * v7 +
                    2 * u145 * v26 * v7 - 6 * u45 * v1 * v26 * v7 -
                    6 * u15 * v4 * v26 * v7 + 24 * u5 * v1 * v4 * v26 * v7 -
                    6 * u5 * v14 * v26 * v7 - 6 * u14 * v5 * v26 * v7 +
                    24 * u4 * v1 * v5 * v26 * v7 +
                    24 * u1 * v4 * v5 * v26 * v7 -
                    120 * u * v1 * v4 * v5 * v26 * v7 +
                    24 * u * v14 * v5 * v26 * v7 - 6 * u4 * v15 * v26 * v7 +
                    24 * u * v4 * v15 * v26 * v7 - 6 * u1 * v45 * v26 * v7 +
                    24 * u * v1 * v45 * v26 * v7 - 6 * u * v145 * v26 * v7 +
                    2 * u45 * v126 * v7 - 6 * u5 * v4 * v126 * v7 -
                    6 * u4 * v5 * v126 * v7 + 24 * u * v4 * v5 * v126 * v7 -
                    6 * u * v45 * v126 * v7 + 2 * u125 * v46 * v7 -
                    6 * u25 * v1 * v46 * v7 - 6 * u15 * v2 * v46 * v7 +
                    24 * u5 * v1 * v2 * v46 * v7 - 6 * u5 * v12 * v46 * v7 -
                    6 * u12 * v5 * v46 * v7 + 24 * u2 * v1 * v5 * v46 * v7 +
                    24 * u1 * v2 * v5 * v46 * v7 -
                    120 * u * v1 * v2 * v5 * v46 * v7 +
                    24 * u * v12 * v5 * v46 * v7 - 6 * u2 * v15 * v46 * v7 +
                    24 * u * v2 * v15 * v46 * v7 - 6 * u1 * v25 * v46 * v7 +
                    24 * u * v1 * v25 * v46 * v7 - 6 * u * v125 * v46 * v7 +
                    2 * u25 * v146 * v7 - 6 * u5 * v2 * v146 * v7 -
                    6 * u2 * v5 * v146 * v7 + 24 * u * v2 * v5 * v146 * v7 -
                    6 * u * v25 * v146 * v7 + 2 * u15 * v246 * v7 -
                    6 * u5 * v1 * v246 * v7 - 6 * u1 * v5 * v246 * v7 +
                    24 * u * v1 * v5 * v246 * v7 - 6 * u * v15 * v246 * v7 +
                    2 * u5 * v1246 * v7 - 6 * u * v5 * v1246 * v7 +
                    2 * u124 * v56 * v7 - 6 * u24 * v1 * v56 * v7 -
                    6 * u14 * v2 * v56 * v7 + 24 * u4 * v1 * v2 * v56 * v7 -
                    6 * u4 * v12 * v56 * v7 - 6 * u12 * v4 * v56 * v7 +
                    24 * u2 * v1 * v4 * v56 * v7 +
                    24 * u1 * v2 * v4 * v56 * v7 -
                    120 * u * v1 * v2 * v4 * v56 * v7 +
                    24 * u * v12 * v4 * v56 * v7 - 6 * u2 * v14 * v56 * v7 +
                    24 * u * v2 * v14 * v56 * v7 - 6 * u1 * v24 * v56 * v7 +
                    24 * u * v1 * v24 * v56 * v7 - 6 * u * v124 * v56 * v7 +
                    2 * u24 * v156 * v7 - 6 * u4 * v2 * v156 * v7 -
                    6 * u2 * v4 * v156 * v7 + 24 * u * v2 * v4 * v156 * v7 -
                    6 * u * v24 * v156 * v7 + 2 * u14 * v256 * v7 -
                    6 * u4 * v1 * v256 * v7 - 6 * u1 * v4 * v256 * v7 +
                    24 * u * v1 * v4 * v256 * v7 - 6 * u * v14 * v256 * v7 +
                    2 * u4 * v1256 * v7 - 6 * u * v4 * v1256 * v7 +
                    2 * u12 * v456 * v7 - 6 * u2 * v1 * v456 * v7 -
                    6 * u1 * v2 * v456 * v7 + 24 * u * v1 * v2 * v456 * v7 -
                    6 * u * v12 * v456 * v7 + 2 * u2 * v1456 * v7 -
                    6 * u * v2 * v1456 * v7 + 2 * u1 * v2456 * v7 -
                    6 * u * v1 * v2456 * v7 + 2 * u * v12456 * v7 -
                    u2456 * v17 + 2 * u456 * v2 * v17 + 2 * u256 * v4 * v17 -
                    6 * u56 * v2 * v4 * v17 + 2 * u56 * v24 * v17 +
                    2 * u246 * v5 * v17 - 6 * u46 * v2 * v5 * v17 -
                    6 * u26 * v4 * v5 * v17 + 24 * u6 * v2 * v4 * v5 * v17 -
                    6 * u6 * v24 * v5 * v17 + 2 * u46 * v25 * v17 -
                    6 * u6 * v4 * v25 * v17 + 2 * u26 * v45 * v17 -
                    6 * u6 * v2 * v45 * v17 + 2 * u6 * v245 * v17 +
                    2 * u245 * v6 * v17 - 6 * u45 * v2 * v6 * v17 -
                    6 * u25 * v4 * v6 * v17 + 24 * u5 * v2 * v4 * v6 * v17 -
                    6 * u5 * v24 * v6 * v17 - 6 * u24 * v5 * v6 * v17 +
                    24 * u4 * v2 * v5 * v6 * v17 +
                    24 * u2 * v4 * v5 * v6 * v17 -
                    120 * u * v2 * v4 * v5 * v6 * v17 +
                    24 * u * v24 * v5 * v6 * v17 - 6 * u4 * v25 * v6 * v17 +
                    24 * u * v4 * v25 * v6 * v17 - 6 * u2 * v45 * v6 * v17 +
                    24 * u * v2 * v45 * v6 * v17 - 6 * u * v245 * v6 * v17 +
                    2 * u45 * v26 * v17 - 6 * u5 * v4 * v26 * v17 -
                    6 * u4 * v5 * v26 * v17 + 24 * u * v4 * v5 * v26 * v17 -
                    6 * u * v45 * v26 * v17 + 2 * u25 * v46 * v17 -
                    6 * u5 * v2 * v46 * v17 - 6 * u2 * v5 * v46 * v17 +
                    24 * u * v2 * v5 * v46 * v17 - 6 * u * v25 * v46 * v17 +
                    2 * u5 * v246 * v17 - 6 * u * v5 * v246 * v17 +
                    2 * u24 * v56 * v17 - 6 * u4 * v2 * v56 * v17 -
                    6 * u2 * v4 * v56 * v17 + 24 * u * v2 * v4 * v56 * v17 -
                    6 * u * v24 * v56 * v17 + 2 * u4 * v256 * v17 -
                    6 * u * v4 * v256 * v17 + 2 * u2 * v456 * v17 -
                    6 * u * v2 * v456 * v17 + 2 * u * v2456 * v17 -
                    u1456 * v27 + 2 * u456 * v1 * v27 + 2 * u156 * v4 * v27 -
                    6 * u56 * v1 * v4 * v27 + 2 * u56 * v14 * v27 +
                    2 * u146 * v5 * v27 - 6 * u46 * v1 * v5 * v27 -
                    6 * u16 * v4 * v5 * v27 + 24 * u6 * v1 * v4 * v5 * v27 -
                    6 * u6 * v14 * v5 * v27 + 2 * u46 * v15 * v27 -
                    6 * u6 * v4 * v15 * v27 + 2 * u16 * v45 * v27 -
                    6 * u6 * v1 * v45 * v27 + 2 * u6 * v145 * v27 +
                    2 * u145 * v6 * v27 - 6 * u45 * v1 * v6 * v27 -
                    6 * u15 * v4 * v6 * v27 + 24 * u5 * v1 * v4 * v6 * v27 -
                    6 * u5 * v14 * v6 * v27 - 6 * u14 * v5 * v6 * v27 +
                    24 * u4 * v1 * v5 * v6 * v27 +
                    24 * u1 * v4 * v5 * v6 * v27 -
                    120 * u * v1 * v4 * v5 * v6 * v27 +
                    24 * u * v14 * v5 * v6 * v27 - 6 * u4 * v15 * v6 * v27 +
                    24 * u * v4 * v15 * v6 * v27 - 6 * u1 * v45 * v6 * v27 +
                    24 * u * v1 * v45 * v6 * v27 - 6 * u * v145 * v6 * v27 +
                    2 * u45 * v16 * v27 - 6 * u5 * v4 * v16 * v27 -
                    6 * u4 * v5 * v16 * v27 + 24 * u * v4 * v5 * v16 * v27 -
                    6 * u * v45 * v16 * v27 + 2 * u15 * v46 * v27 -
                    6 * u5 * v1 * v46 * v27 - 6 * u1 * v5 * v46 * v27 +
                    24 * u * v1 * v5 * v46 * v27 - 6 * u * v15 * v46 * v27 +
                    2 * u5 * v146 * v27 - 6 * u * v5 * v146 * v27 +
                    2 * u14 * v56 * v27 - 6 * u4 * v1 * v56 * v27 -
                    6 * u1 * v4 * v56 * v27 + 24 * u * v1 * v4 * v56 * v27 -
                    6 * u * v14 * v56 * v27 + 2 * u4 * v156 * v27 -
                    6 * u * v4 * v156 * v27 + 2 * u1 * v456 * v27 -
                    6 * u * v1 * v456 * v27 + 2 * u * v1456 * v27 -
                    u456 * v127 + 2 * u56 * v4 * v127 + 2 * u46 * v5 * v127 -
                    6 * u6 * v4 * v5 * v127 + 2 * u6 * v45 * v127 +
                    2 * u45 * v6 * v127 - 6 * u5 * v4 * v6 * v127 -
                    6 * u4 * v5 * v6 * v127 + 24 * u * v4 * v5 * v6 * v127 -
                    6 * u * v45 * v6 * v127 + 2 * u5 * v46 * v127 -
                    6 * u * v5 * v46 * v127 + 2 * u4 * v56 * v127 -
                    6 * u * v4 * v56 * v127 + 2 * u * v456 * v127 -
                    u1256 * v47 + 2 * u256 * v1 * v47 + 2 * u156 * v2 * v47 -
                    6 * u56 * v1 * v2 * v47 + 2 * u56 * v12 * v47 +
                    2 * u126 * v5 * v47 - 6 * u26 * v1 * v5 * v47 -
                    6 * u16 * v2 * v5 * v47 + 24 * u6 * v1 * v2 * v5 * v47 -
                    6 * u6 * v12 * v5 * v47 + 2 * u26 * v15 * v47 -
                    6 * u6 * v2 * v15 * v47 + 2 * u16 * v25 * v47 -
                    6 * u6 * v1 * v25 * v47 + 2 * u6 * v125 * v47 +
                    2 * u125 * v6 * v47 - 6 * u25 * v1 * v6 * v47 -
                    6 * u15 * v2 * v6 * v47 + 24 * u5 * v1 * v2 * v6 * v47 -
                    6 * u5 * v12 * v6 * v47 - 6 * u12 * v5 * v6 * v47 +
                    24 * u2 * v1 * v5 * v6 * v47 +
                    24 * u1 * v2 * v5 * v6 * v47 -
                    120 * u * v1 * v2 * v5 * v6 * v47 +
                    24 * u * v12 * v5 * v6 * v47 - 6 * u2 * v15 * v6 * v47 +
                    24 * u * v2 * v15 * v6 * v47 - 6 * u1 * v25 * v6 * v47 +
                    24 * u * v1 * v25 * v6 * v47 - 6 * u * v125 * v6 * v47 +
                    2 * u25 * v16 * v47 - 6 * u5 * v2 * v16 * v47 -
                    6 * u2 * v5 * v16 * v47 + 24 * u * v2 * v5 * v16 * v47 -
                    6 * u * v25 * v16 * v47 + 2 * u15 * v26 * v47 -
                    6 * u5 * v1 * v26 * v47 - 6 * u1 * v5 * v26 * v47 +
                    24 * u * v1 * v5 * v26 * v47 - 6 * u * v15 * v26 * v47 +
                    2 * u5 * v126 * v47 - 6 * u * v5 * v126 * v47 +
                    2 * u12 * v56 * v47 - 6 * u2 * v1 * v56 * v47 -
                    6 * u1 * v2 * v56 * v47 + 24 * u * v1 * v2 * v56 * v47 -
                    6 * u * v12 * v56 * v47 + 2 * u2 * v156 * v47 -
                    6 * u * v2 * v156 * v47 + 2 * u1 * v256 * v47 -
                    6 * u * v1 * v256 * v47 + 2 * u * v1256 * v47 -
                    u256 * v147 + 2 * u56 * v2 * v147 + 2 * u26 * v5 * v147 -
                    6 * u6 * v2 * v5 * v147 + 2 * u6 * v25 * v147 +
                    2 * u25 * v6 * v147 - 6 * u5 * v2 * v6 * v147 -
                    6 * u2 * v5 * v6 * v147 + 24 * u * v2 * v5 * v6 * v147 -
                    6 * u * v25 * v6 * v147 + 2 * u5 * v26 * v147 -
                    6 * u * v5 * v26 * v147 + 2 * u2 * v56 * v147 -
                    6 * u * v2 * v56 * v147 + 2 * u * v256 * v147 -
                    u156 * v247 + 2 * u56 * v1 * v247 + 2 * u16 * v5 * v247 -
                    6 * u6 * v1 * v5 * v247 + 2 * u6 * v15 * v247 +
                    2 * u15 * v6 * v247 - 6 * u5 * v1 * v6 * v247 -
                    6 * u1 * v5 * v6 * v247 + 24 * u * v1 * v5 * v6 * v247 -
                    6 * u * v15 * v6 * v247 + 2 * u5 * v16 * v247 -
                    6 * u * v5 * v16 * v247 + 2 * u1 * v56 * v247 -
                    6 * u * v1 * v56 * v247 + 2 * u * v156 * v247 -
                    u56 * v1247 + 2 * u6 * v5 * v1247 + 2 * u5 * v6 * v1247 -
                    6 * u * v5 * v6 * v1247 + 2 * u * v56 * v1247 -
                    u1246 * v57 + 2 * u246 * v1 * v57 + 2 * u146 * v2 * v57 -
                    6 * u46 * v1 * v2 * v57 + 2 * u46 * v12 * v57 +
                    2 * u126 * v4 * v57 - 6 * u26 * v1 * v4 * v57 -
                    6 * u16 * v2 * v4 * v57 + 24 * u6 * v1 * v2 * v4 * v57 -
                    6 * u6 * v12 * v4 * v57 + 2 * u26 * v14 * v57 -
                    6 * u6 * v2 * v14 * v57 + 2 * u16 * v24 * v57 -
                    6 * u6 * v1 * v24 * v57 + 2 * u6 * v124 * v57 +
                    2 * u124 * v6 * v57 - 6 * u24 * v1 * v6 * v57 -
                    6 * u14 * v2 * v6 * v57 + 24 * u4 * v1 * v2 * v6 * v57 -
                    6 * u4 * v12 * v6 * v57 - 6 * u12 * v4 * v6 * v57 +
                    24 * u2 * v1 * v4 * v6 * v57 +
                    24 * u1 * v2 * v4 * v6 * v57 -
                    120 * u * v1 * v2 * v4 * v6 * v57 +
                    24 * u * v12 * v4 * v6 * v57 - 6 * u2 * v14 * v6 * v57 +
                    24 * u * v2 * v14 * v6 * v57 - 6 * u1 * v24 * v6 * v57 +
                    24 * u * v1 * v24 * v6 * v57 - 6 * u * v124 * v6 * v57 +
                    2 * u24 * v16 * v57 - 6 * u4 * v2 * v16 * v57 -
                    6 * u2 * v4 * v16 * v57 + 24 * u * v2 * v4 * v16 * v57 -
                    6 * u * v24 * v16 * v57 + 2 * u14 * v26 * v57 -
                    6 * u4 * v1 * v26 * v57 - 6 * u1 * v4 * v26 * v57 +
                    24 * u * v1 * v4 * v26 * v57 - 6 * u * v14 * v26 * v57 +
                    2 * u4 * v126 * v57 - 6 * u * v4 * v126 * v57 +
                    2 * u12 * v46 * v57 - 6 * u2 * v1 * v46 * v57 -
                    6 * u1 * v2 * v46 * v57 + 24 * u * v1 * v2 * v46 * v57 -
                    6 * u * v12 * v46 * v57 + 2 * u2 * v146 * v57 -
                    6 * u * v2 * v146 * v57 + 2 * u1 * v246 * v57 -
                    6 * u * v1 * v246 * v57 + 2 * u * v1246 * v57 -
                    u246 * v157 + 2 * u46 * v2 * v157 + 2 * u26 * v4 * v157 -
                    6 * u6 * v2 * v4 * v157 + 2 * u6 * v24 * v157 +
                    2 * u24 * v6 * v157 - 6 * u4 * v2 * v6 * v157 -
                    6 * u2 * v4 * v6 * v157 + 24 * u * v2 * v4 * v6 * v157 -
                    6 * u * v24 * v6 * v157 + 2 * u4 * v26 * v157 -
                    6 * u * v4 * v26 * v157 + 2 * u2 * v46 * v157 -
                    6 * u * v2 * v46 * v157 + 2 * u * v246 * v157 -
                    u146 * v257 + 2 * u46 * v1 * v257 + 2 * u16 * v4 * v257 -
                    6 * u6 * v1 * v4 * v257 + 2 * u6 * v14 * v257 +
                    2 * u14 * v6 * v257 - 6 * u4 * v1 * v6 * v257 -
                    6 * u1 * v4 * v6 * v257 + 24 * u * v1 * v4 * v6 * v257 -
                    6 * u * v14 * v6 * v257 + 2 * u4 * v16 * v257 -
                    6 * u * v4 * v16 * v257 + 2 * u1 * v46 * v257 -
                    6 * u * v1 * v46 * v257 + 2 * u * v146 * v257 -
                    u46 * v1257 + 2 * u6 * v4 * v1257 + 2 * u4 * v6 * v1257 -
                    6 * u * v4 * v6 * v1257 + 2 * u * v46 * v1257 -
                    u126 * v457 + 2 * u26 * v1 * v457 + 2 * u16 * v2 * v457 -
                    6 * u6 * v1 * v2 * v457 + 2 * u6 * v12 * v457 +
                    2 * u12 * v6 * v457 - 6 * u2 * v1 * v6 * v457 -
                    6 * u1 * v2 * v6 * v457 + 24 * u * v1 * v2 * v6 * v457 -
                    6 * u * v12 * v6 * v457 + 2 * u2 * v16 * v457 -
                    6 * u * v2 * v16 * v457 + 2 * u1 * v26 * v457 -
                    6 * u * v1 * v26 * v457 + 2 * u * v126 * v457 -
                    u26 * v1457 + 2 * u6 * v2 * v1457 + 2 * u2 * v6 * v1457 -
                    6 * u * v2 * v6 * v1457 + 2 * u * v26 * v1457 -
                    u16 * v2457 + 2 * u6 * v1 * v2457 + 2 * u1 * v6 * v2457 -
                    6 * u * v1 * v6 * v2457 + 2 * u * v16 * v2457 -
                    u6 * v12457 + 2 * u * v6 * v12457 - u1245 * v67 +
                    2 * u245 * v1 * v67 + 2 * u145 * v2 * v67 -
                    6 * u45 * v1 * v2 * v67 + 2 * u45 * v12 * v67 +
                    2 * u125 * v4 * v67 - 6 * u25 * v1 * v4 * v67 -
                    6 * u15 * v2 * v4 * v67 + 24 * u5 * v1 * v2 * v4 * v67 -
                    6 * u5 * v12 * v4 * v67 + 2 * u25 * v14 * v67 -
                    6 * u5 * v2 * v14 * v67 + 2 * u15 * v24 * v67 -
                    6 * u5 * v1 * v24 * v67 + 2 * u5 * v124 * v67 +
                    2 * u124 * v5 * v67 - 6 * u24 * v1 * v5 * v67 -
                    6 * u14 * v2 * v5 * v67 + 24 * u4 * v1 * v2 * v5 * v67 -
                    6 * u4 * v12 * v5 * v67 - 6 * u12 * v4 * v5 * v67 +
                    24 * u2 * v1 * v4 * v5 * v67 +
                    24 * u1 * v2 * v4 * v5 * v67 -
                    120 * u * v1 * v2 * v4 * v5 * v67 +
                    24 * u * v12 * v4 * v5 * v67 - 6 * u2 * v14 * v5 * v67 +
                    24 * u * v2 * v14 * v5 * v67 - 6 * u1 * v24 * v5 * v67 +
                    24 * u * v1 * v24 * v5 * v67 - 6 * u * v124 * v5 * v67 +
                    2 * u24 * v15 * v67 - 6 * u4 * v2 * v15 * v67 -
                    6 * u2 * v4 * v15 * v67 + 24 * u * v2 * v4 * v15 * v67 -
                    6 * u * v24 * v15 * v67 + 2 * u14 * v25 * v67 -
                    6 * u4 * v1 * v25 * v67 - 6 * u1 * v4 * v25 * v67 +
                    24 * u * v1 * v4 * v25 * v67 - 6 * u * v14 * v25 * v67 +
                    2 * u4 * v125 * v67 - 6 * u * v4 * v125 * v67 +
                    2 * u12 * v45 * v67 - 6 * u2 * v1 * v45 * v67 -
                    6 * u1 * v2 * v45 * v67 + 24 * u * v1 * v2 * v45 * v67 -
                    6 * u * v12 * v45 * v67 + 2 * u2 * v145 * v67 -
                    6 * u * v2 * v145 * v67 + 2 * u1 * v245 * v67 -
                    6 * u * v1 * v245 * v67 + 2 * u * v1245 * v67 -
                    u245 * v167 + 2 * u45 * v2 * v167 + 2 * u25 * v4 * v167 -
                    6 * u5 * v2 * v4 * v167 + 2 * u5 * v24 * v167 +
                    2 * u24 * v5 * v167 - 6 * u4 * v2 * v5 * v167 -
                    6 * u2 * v4 * v5 * v167 + 24 * u * v2 * v4 * v5 * v167 -
                    6 * u * v24 * v5 * v167 + 2 * u4 * v25 * v167 -
                    6 * u * v4 * v25 * v167 + 2 * u2 * v45 * v167 -
                    6 * u * v2 * v45 * v167 + 2 * u * v245 * v167 -
                    u145 * v267 + 2 * u45 * v1 * v267 + 2 * u15 * v4 * v267 -
                    6 * u5 * v1 * v4 * v267 + 2 * u5 * v14 * v267 +
                    2 * u14 * v5 * v267 - 6 * u4 * v1 * v5 * v267 -
                    6 * u1 * v4 * v5 * v267 + 24 * u * v1 * v4 * v5 * v267 -
                    6 * u * v14 * v5 * v267 + 2 * u4 * v15 * v267 -
                    6 * u * v4 * v15 * v267 + 2 * u1 * v45 * v267 -
                    6 * u * v1 * v45 * v267 + 2 * u * v145 * v267 -
                    u45 * v1267 + 2 * u5 * v4 * v1267 + 2 * u4 * v5 * v1267 -
                    6 * u * v4 * v5 * v1267 + 2 * u * v45 * v1267 -
                    u125 * v467 + 2 * u25 * v1 * v467 + 2 * u15 * v2 * v467 -
                    6 * u5 * v1 * v2 * v467 + 2 * u5 * v12 * v467 +
                    2 * u12 * v5 * v467 - 6 * u2 * v1 * v5 * v467 -
                    6 * u1 * v2 * v5 * v467 + 24 * u * v1 * v2 * v5 * v467 -
                    6 * u * v12 * v5 * v467 + 2 * u2 * v15 * v467 -
                    6 * u * v2 * v15 * v467 + 2 * u1 * v25 * v467 -
                    6 * u * v1 * v25 * v467 + 2 * u * v125 * v467 -
                    u25 * v1467 + 2 * u5 * v2 * v1467 + 2 * u2 * v5 * v1467 -
                    6 * u * v2 * v5 * v1467 + 2 * u * v25 * v1467 -
                    u15 * v2467 + 2 * u5 * v1 * v2467 + 2 * u1 * v5 * v2467 -
                    6 * u * v1 * v5 * v2467 + 2 * u * v15 * v2467 -
                    u5 * v12467 + 2 * u * v5 * v12467 - u124 * v567 +
                    2 * u24 * v1 * v567 + 2 * u14 * v2 * v567 -
                    6 * u4 * v1 * v2 * v567 + 2 * u4 * v12 * v567 +
                    2 * u12 * v4 * v567 - 6 * u2 * v1 * v4 * v567 -
                    6 * u1 * v2 * v4 * v567 + 24 * u * v1 * v2 * v4 * v567 -
                    6 * u * v12 * v4 * v567 + 2 * u2 * v14 * v567 -
                    6 * u * v2 * v14 * v567 + 2 * u1 * v24 * v567 -
                    6 * u * v1 * v24 * v567 + 2 * u * v124 * v567 -
                    u24 * v1567 + 2 * u4 * v2 * v1567 + 2 * u2 * v4 * v1567 -
                    6 * u * v2 * v4 * v1567 + 2 * u * v24 * v1567 -
                    u14 * v2567 + 2 * u4 * v1 * v2567 + 2 * u1 * v4 * v2567 -
                    6 * u * v1 * v4 * v2567 + 2 * u * v14 * v2567 -
                    u4 * v12567 + 2 * u * v4 * v12567 - u12 * v4567 +
                    2 * u2 * v1 * v4567 + 2 * u1 * v2 * v4567 -
                    6 * u * v1 * v2 * v4567 + 2 * u * v12 * v4567 -
                    u2 * v14567 + 2 * u * v2 * v14567 - u1 * v24567 +
                    2 * u * v1 * v24567 - u * v124567,
            .dual34567 =
                    u34567 - u4567 * v3 - u3567 * v4 + 2 * u567 * v3 * v4 -
                    u567 * v34 - u3467 * v5 + 2 * u467 * v3 * v5 +
                    2 * u367 * v4 * v5 - 6 * u67 * v3 * v4 * v5 +
                    2 * u67 * v34 * v5 - u467 * v35 + 2 * u67 * v4 * v35 -
                    u367 * v45 + 2 * u67 * v3 * v45 - u67 * v345 - u3457 * v6 +
                    2 * u457 * v3 * v6 + 2 * u357 * v4 * v6 -
                    6 * u57 * v3 * v4 * v6 + 2 * u57 * v34 * v6 +
                    2 * u347 * v5 * v6 - 6 * u47 * v3 * v5 * v6 -
                    6 * u37 * v4 * v5 * v6 + 24 * u7 * v3 * v4 * v5 * v6 -
                    6 * u7 * v34 * v5 * v6 + 2 * u47 * v35 * v6 -
                    6 * u7 * v4 * v35 * v6 + 2 * u37 * v45 * v6 -
                    6 * u7 * v3 * v45 * v6 + 2 * u7 * v345 * v6 - u457 * v36 +
                    2 * u57 * v4 * v36 + 2 * u47 * v5 * v36 -
                    6 * u7 * v4 * v5 * v36 + 2 * u7 * v45 * v36 - u357 * v46 +
                    2 * u57 * v3 * v46 + 2 * u37 * v5 * v46 -
                    6 * u7 * v3 * v5 * v46 + 2 * u7 * v35 * v46 - u57 * v346 +
                    2 * u7 * v5 * v346 - u347 * v56 + 2 * u47 * v3 * v56 +
                    2 * u37 * v4 * v56 - 6 * u7 * v3 * v4 * v56 +
                    2 * u7 * v34 * v56 - u47 * v356 + 2 * u7 * v4 * v356 -
                    u37 * v456 + 2 * u7 * v3 * v456 - u7 * v3456 - u3456 * v7 +
                    2 * u456 * v3 * v7 + 2 * u356 * v4 * v7 -
                    6 * u56 * v3 * v4 * v7 + 2 * u56 * v34 * v7 +
                    2 * u346 * v5 * v7 - 6 * u46 * v3 * v5 * v7 -
                    6 * u36 * v4 * v5 * v7 + 24 * u6 * v3 * v4 * v5 * v7 -
                    6 * u6 * v34 * v5 * v7 + 2 * u46 * v35 * v7 -
                    6 * u6 * v4 * v35 * v7 + 2 * u36 * v45 * v7 -
                    6 * u6 * v3 * v45 * v7 + 2 * u6 * v345 * v7 +
                    2 * u345 * v6 * v7 - 6 * u45 * v3 * v6 * v7 -
                    6 * u35 * v4 * v6 * v7 + 24 * u5 * v3 * v4 * v6 * v7 -
                    6 * u5 * v34 * v6 * v7 - 6 * u34 * v5 * v6 * v7 +
                    24 * u4 * v3 * v5 * v6 * v7 + 24 * u3 * v4 * v5 * v6 * v7 -
                    120 * u * v3 * v4 * v5 * v6 * v7 +
                    24 * u * v34 * v5 * v6 * v7 - 6 * u4 * v35 * v6 * v7 +
                    24 * u * v4 * v35 * v6 * v7 - 6 * u3 * v45 * v6 * v7 +
                    24 * u * v3 * v45 * v6 * v7 - 6 * u * v345 * v6 * v7 +
                    2 * u45 * v36 * v7 - 6 * u5 * v4 * v36 * v7 -
                    6 * u4 * v5 * v36 * v7 + 24 * u * v4 * v5 * v36 * v7 -
                    6 * u * v45 * v36 * v7 + 2 * u35 * v46 * v7 -
                    6 * u5 * v3 * v46 * v7 - 6 * u3 * v5 * v46 * v7 +
                    24 * u * v3 * v5 * v46 * v7 - 6 * u * v35 * v46 * v7 +
                    2 * u5 * v346 * v7 - 6 * u * v5 * v346 * v7 +
                    2 * u34 * v56 * v7 - 6 * u4 * v3 * v56 * v7 -
                    6 * u3 * v4 * v56 * v7 + 24 * u * v3 * v4 * v56 * v7 -
                    6 * u * v34 * v56 * v7 + 2 * u4 * v356 * v7 -
                    6 * u * v4 * v356 * v7 + 2 * u3 * v456 * v7 -
                    6 * u * v3 * v456 * v7 + 2 * u * v3456 * v7 - u456 * v37 +
                    2 * u56 * v4 * v37 + 2 * u46 * v5 * v37 -
                    6 * u6 * v4 * v5 * v37 + 2 * u6 * v45 * v37 +
                    2 * u45 * v6 * v37 - 6 * u5 * v4 * v6 * v37 -
                    6 * u4 * v5 * v6 * v37 + 24 * u * v4 * v5 * v6 * v37 -
                    6 * u * v45 * v6 * v37 + 2 * u5 * v46 * v37 -
                    6 * u * v5 * v46 * v37 + 2 * u4 * v56 * v37 -
                    6 * u * v4 * v56 * v37 + 2 * u * v456 * v37 - u356 * v47 +
                    2 * u56 * v3 * v47 + 2 * u36 * v5 * v47 -
                    6 * u6 * v3 * v5 * v47 + 2 * u6 * v35 * v47 +
                    2 * u35 * v6 * v47 - 6 * u5 * v3 * v6 * v47 -
                    6 * u3 * v5 * v6 * v47 + 24 * u * v3 * v5 * v6 * v47 -
                    6 * u * v35 * v6 * v47 + 2 * u5 * v36 * v47 -
                    6 * u * v5 * v36 * v47 + 2 * u3 * v56 * v47 -
                    6 * u * v3 * v56 * v47 + 2 * u * v356 * v47 - u56 * v347 +
                    2 * u6 * v5 * v347 + 2 * u5 * v6 * v347 -
                    6 * u * v5 * v6 * v347 + 2 * u * v56 * v347 - u346 * v57 +
                    2 * u46 * v3 * v57 + 2 * u36 * v4 * v57 -
                    6 * u6 * v3 * v4 * v57 + 2 * u6 * v34 * v57 +
                    2 * u34 * v6 * v57 - 6 * u4 * v3 * v6 * v57 -
                    6 * u3 * v4 * v6 * v57 + 24 * u * v3 * v4 * v6 * v57 -
                    6 * u * v34 * v6 * v57 + 2 * u4 * v36 * v57 -
                    6 * u * v4 * v36 * v57 + 2 * u3 * v46 * v57 -
                    6 * u * v3 * v46 * v57 + 2 * u * v346 * v57 - u46 * v357 +
                    2 * u6 * v4 * v357 + 2 * u4 * v6 * v357 -
                    6 * u * v4 * v6 * v357 + 2 * u * v46 * v357 - u36 * v457 +
                    2 * u6 * v3 * v457 + 2 * u3 * v6 * v457 -
                    6 * u * v3 * v6 * v457 + 2 * u * v36 * v457 - u6 * v3457 +
                    2 * u * v6 * v3457 - u345 * v67 + 2 * u45 * v3 * v67 +
                    2 * u35 * v4 * v67 - 6 * u5 * v3 * v4 * v67 +
                    2 * u5 * v34 * v67 + 2 * u34 * v5 * v67 -
                    6 * u4 * v3 * v5 * v67 - 6 * u3 * v4 * v5 * v67 +
                    24 * u * v3 * v4 * v5 * v67 - 6 * u * v34 * v5 * v67 +
                    2 * u4 * v35 * v67 - 6 * u * v4 * v35 * v67 +
                    2 * u3 * v45 * v67 - 6 * u * v3 * v45 * v67 +
                    2 * u * v345 * v67 - u45 * v367 + 2 * u5 * v4 * v367 +
                    2 * u4 * v5 * v367 - 6 * u * v4 * v5 * v367 +
                    2 * u * v45 * v367 - u35 * v467 + 2 * u5 * v3 * v467 +
                    2 * u3 * v5 * v467 - 6 * u * v3 * v5 * v467 +
                    2 * u * v35 * v467 - u5 * v3467 + 2 * u * v5 * v3467 -
                    u34 * v567 + 2 * u4 * v3 * v567 + 2 * u3 * v4 * v567 -
                    6 * u * v3 * v4 * v567 + 2 * u * v34 * v567 - u4 * v3567 +
                    2 * u * v4 * v3567 - u3 * v4567 + 2 * u * v3 * v4567 -
                    u * v34567,
            .dual134567 =
                    u134567 - u34567 * v1 - u14567 * v3 + 2 * u4567 * v1 * v3 -
                    u4567 * v13 - u13567 * v4 + 2 * u3567 * v1 * v4 +
                    2 * u1567 * v3 * v4 - 6 * u567 * v1 * v3 * v4 +
                    2 * u567 * v13 * v4 - u3567 * v14 + 2 * u567 * v3 * v14 -
                    u1567 * v34 + 2 * u567 * v1 * v34 - u567 * v134 -
                    u13467 * v5 + 2 * u3467 * v1 * v5 + 2 * u1467 * v3 * v5 -
                    6 * u467 * v1 * v3 * v5 + 2 * u467 * v13 * v5 +
                    2 * u1367 * v4 * v5 - 6 * u367 * v1 * v4 * v5 -
                    6 * u167 * v3 * v4 * v5 + 24 * u67 * v1 * v3 * v4 * v5 -
                    6 * u67 * v13 * v4 * v5 + 2 * u367 * v14 * v5 -
                    6 * u67 * v3 * v14 * v5 + 2 * u167 * v34 * v5 -
                    6 * u67 * v1 * v34 * v5 + 2 * u67 * v134 * v5 -
                    u3467 * v15 + 2 * u467 * v3 * v15 + 2 * u367 * v4 * v15 -
                    6 * u67 * v3 * v4 * v15 + 2 * u67 * v34 * v15 -
                    u1467 * v35 + 2 * u467 * v1 * v35 + 2 * u167 * v4 * v35 -
                    6 * u67 * v1 * v4 * v35 + 2 * u67 * v14 * v35 -
                    u467 * v135 + 2 * u67 * v4 * v135 - u1367 * v45 +
                    2 * u367 * v1 * v45 + 2 * u167 * v3 * v45 -
                    6 * u67 * v1 * v3 * v45 + 2 * u67 * v13 * v45 -
                    u367 * v145 + 2 * u67 * v3 * v145 - u167 * v345 +
                    2 * u67 * v1 * v345 - u67 * v1345 - u13457 * v6 +
                    2 * u3457 * v1 * v6 + 2 * u1457 * v3 * v6 -
                    6 * u457 * v1 * v3 * v6 + 2 * u457 * v13 * v6 +
                    2 * u1357 * v4 * v6 - 6 * u357 * v1 * v4 * v6 -
                    6 * u157 * v3 * v4 * v6 + 24 * u57 * v1 * v3 * v4 * v6 -
                    6 * u57 * v13 * v4 * v6 + 2 * u357 * v14 * v6 -
                    6 * u57 * v3 * v14 * v6 + 2 * u157 * v34 * v6 -
                    6 * u57 * v1 * v34 * v6 + 2 * u57 * v134 * v6 +
                    2 * u1347 * v5 * v6 - 6 * u347 * v1 * v5 * v6 -
                    6 * u147 * v3 * v5 * v6 + 24 * u47 * v1 * v3 * v5 * v6 -
                    6 * u47 * v13 * v5 * v6 - 6 * u137 * v4 * v5 * v6 +
                    24 * u37 * v1 * v4 * v5 * v6 +
                    24 * u17 * v3 * v4 * v5 * v6 -
                    120 * u7 * v1 * v3 * v4 * v5 * v6 +
                    24 * u7 * v13 * v4 * v5 * v6 - 6 * u37 * v14 * v5 * v6 +
                    24 * u7 * v3 * v14 * v5 * v6 - 6 * u17 * v34 * v5 * v6 +
                    24 * u7 * v1 * v34 * v5 * v6 - 6 * u7 * v134 * v5 * v6 +
                    2 * u347 * v15 * v6 - 6 * u47 * v3 * v15 * v6 -
                    6 * u37 * v4 * v15 * v6 + 24 * u7 * v3 * v4 * v15 * v6 -
                    6 * u7 * v34 * v15 * v6 + 2 * u147 * v35 * v6 -
                    6 * u47 * v1 * v35 * v6 - 6 * u17 * v4 * v35 * v6 +
                    24 * u7 * v1 * v4 * v35 * v6 - 6 * u7 * v14 * v35 * v6 +
                    2 * u47 * v135 * v6 - 6 * u7 * v4 * v135 * v6 +
                    2 * u137 * v45 * v6 - 6 * u37 * v1 * v45 * v6 -
                    6 * u17 * v3 * v45 * v6 + 24 * u7 * v1 * v3 * v45 * v6 -
                    6 * u7 * v13 * v45 * v6 + 2 * u37 * v145 * v6 -
                    6 * u7 * v3 * v145 * v6 + 2 * u17 * v345 * v6 -
                    6 * u7 * v1 * v345 * v6 + 2 * u7 * v1345 * v6 -
                    u3457 * v16 + 2 * u457 * v3 * v16 + 2 * u357 * v4 * v16 -
                    6 * u57 * v3 * v4 * v16 + 2 * u57 * v34 * v16 +
                    2 * u347 * v5 * v16 - 6 * u47 * v3 * v5 * v16 -
                    6 * u37 * v4 * v5 * v16 + 24 * u7 * v3 * v4 * v5 * v16 -
                    6 * u7 * v34 * v5 * v16 + 2 * u47 * v35 * v16 -
                    6 * u7 * v4 * v35 * v16 + 2 * u37 * v45 * v16 -
                    6 * u7 * v3 * v45 * v16 + 2 * u7 * v345 * v16 -
                    u1457 * v36 + 2 * u457 * v1 * v36 + 2 * u157 * v4 * v36 -
                    6 * u57 * v1 * v4 * v36 + 2 * u57 * v14 * v36 +
                    2 * u147 * v5 * v36 - 6 * u47 * v1 * v5 * v36 -
                    6 * u17 * v4 * v5 * v36 + 24 * u7 * v1 * v4 * v5 * v36 -
                    6 * u7 * v14 * v5 * v36 + 2 * u47 * v15 * v36 -
                    6 * u7 * v4 * v15 * v36 + 2 * u17 * v45 * v36 -
                    6 * u7 * v1 * v45 * v36 + 2 * u7 * v145 * v36 -
                    u457 * v136 + 2 * u57 * v4 * v136 + 2 * u47 * v5 * v136 -
                    6 * u7 * v4 * v5 * v136 + 2 * u7 * v45 * v136 -
                    u1357 * v46 + 2 * u357 * v1 * v46 + 2 * u157 * v3 * v46 -
                    6 * u57 * v1 * v3 * v46 + 2 * u57 * v13 * v46 +
                    2 * u137 * v5 * v46 - 6 * u37 * v1 * v5 * v46 -
                    6 * u17 * v3 * v5 * v46 + 24 * u7 * v1 * v3 * v5 * v46 -
                    6 * u7 * v13 * v5 * v46 + 2 * u37 * v15 * v46 -
                    6 * u7 * v3 * v15 * v46 + 2 * u17 * v35 * v46 -
                    6 * u7 * v1 * v35 * v46 + 2 * u7 * v135 * v46 -
                    u357 * v146 + 2 * u57 * v3 * v146 + 2 * u37 * v5 * v146 -
                    6 * u7 * v3 * v5 * v146 + 2 * u7 * v35 * v146 -
                    u157 * v346 + 2 * u57 * v1 * v346 + 2 * u17 * v5 * v346 -
                    6 * u7 * v1 * v5 * v346 + 2 * u7 * v15 * v346 -
                    u57 * v1346 + 2 * u7 * v5 * v1346 - u1347 * v56 +
                    2 * u347 * v1 * v56 + 2 * u147 * v3 * v56 -
                    6 * u47 * v1 * v3 * v56 + 2 * u47 * v13 * v56 +
                    2 * u137 * v4 * v56 - 6 * u37 * v1 * v4 * v56 -
                    6 * u17 * v3 * v4 * v56 + 24 * u7 * v1 * v3 * v4 * v56 -
                    6 * u7 * v13 * v4 * v56 + 2 * u37 * v14 * v56 -
                    6 * u7 * v3 * v14 * v56 + 2 * u17 * v34 * v56 -
                    6 * u7 * v1 * v34 * v56 + 2 * u7 * v134 * v56 -
                    u347 * v156 + 2 * u47 * v3 * v156 + 2 * u37 * v4 * v156 -
                    6 * u7 * v3 * v4 * v156 + 2 * u7 * v34 * v156 -
                    u147 * v356 + 2 * u47 * v1 * v356 + 2 * u17 * v4 * v356 -
                    6 * u7 * v1 * v4 * v356 + 2 * u7 * v14 * v356 -
                    u47 * v1356 + 2 * u7 * v4 * v1356 - u137 * v456 +
                    2 * u37 * v1 * v456 + 2 * u17 * v3 * v456 -
                    6 * u7 * v1 * v3 * v456 + 2 * u7 * v13 * v456 -
                    u37 * v1456 + 2 * u7 * v3 * v1456 - u17 * v3456 +
                    2 * u7 * v1 * v3456 - u7 * v13456 - u13456 * v7 +
                    2 * u3456 * v1 * v7 + 2 * u1456 * v3 * v7 -
                    6 * u456 * v1 * v3 * v7 + 2 * u456 * v13 * v7 +
                    2 * u1356 * v4 * v7 - 6 * u356 * v1 * v4 * v7 -
                    6 * u156 * v3 * v4 * v7 + 24 * u56 * v1 * v3 * v4 * v7 -
                    6 * u56 * v13 * v4 * v7 + 2 * u356 * v14 * v7 -
                    6 * u56 * v3 * v14 * v7 + 2 * u156 * v34 * v7 -
                    6 * u56 * v1 * v34 * v7 + 2 * u56 * v134 * v7 +
                    2 * u1346 * v5 * v7 - 6 * u346 * v1 * v5 * v7 -
                    6 * u146 * v3 * v5 * v7 + 24 * u46 * v1 * v3 * v5 * v7 -
                    6 * u46 * v13 * v5 * v7 - 6 * u136 * v4 * v5 * v7 +
                    24 * u36 * v1 * v4 * v5 * v7 +
                    24 * u16 * v3 * v4 * v5 * v7 -
                    120 * u6 * v1 * v3 * v4 * v5 * v7 +
                    24 * u6 * v13 * v4 * v5 * v7 - 6 * u36 * v14 * v5 * v7 +
                    24 * u6 * v3 * v14 * v5 * v7 - 6 * u16 * v34 * v5 * v7 +
                    24 * u6 * v1 * v34 * v5 * v7 - 6 * u6 * v134 * v5 * v7 +
                    2 * u346 * v15 * v7 - 6 * u46 * v3 * v15 * v7 -
                    6 * u36 * v4 * v15 * v7 + 24 * u6 * v3 * v4 * v15 * v7 -
                    6 * u6 * v34 * v15 * v7 + 2 * u146 * v35 * v7 -
                    6 * u46 * v1 * v35 * v7 - 6 * u16 * v4 * v35 * v7 +
                    24 * u6 * v1 * v4 * v35 * v7 - 6 * u6 * v14 * v35 * v7 +
                    2 * u46 * v135 * v7 - 6 * u6 * v4 * v135 * v7 +
                    2 * u136 * v45 * v7 - 6 * u36 * v1 * v45 * v7 -
                    6 * u16 * v3 * v45 * v7 + 24 * u6 * v1 * v3 * v45 * v7 -
                    6 * u6 * v13 * v45 * v7 + 2 * u36 * v145 * v7 -
                    6 * u6 * v3 * v145 * v7 + 2 * u16 * v345 * v7 -
                    6 * u6 * v1 * v345 * v7 + 2 * u6 * v1345 * v7 +
                    2 * u1345 * v6 * v7 - 6 * u345 * v1 * v6 * v7 -
                    6 * u145 * v3 * v6 * v7 + 24 * u45 * v1 * v3 * v6 * v7 -
                    6 * u45 * v13 * v6 * v7 - 6 * u135 * v4 * v6 * v7 +
                    24 * u35 * v1 * v4 * v6 * v7 +
                    24 * u15 * v3 * v4 * v6 * v7 -
                    120 * u5 * v1 * v3 * v4 * v6 * v7 +
                    24 * u5 * v13 * v4 * v6 * v7 - 6 * u35 * v14 * v6 * v7 +
                    24 * u5 * v3 * v14 * v6 * v7 - 6 * u15 * v34 * v6 * v7 +
                    24 * u5 * v1 * v34 * v6 * v7 - 6 * u5 * v134 * v6 * v7 -
                    6 * u134 * v5 * v6 * v7 + 24 * u34 * v1 * v5 * v6 * v7 +
                    24 * u14 * v3 * v5 * v6 * v7 -
                    120 * u4 * v1 * v3 * v5 * v6 * v7 +
                    24 * u4 * v13 * v5 * v6 * v7 +
                    24 * u13 * v4 * v5 * v6 * v7 -
                    120 * u3 * v1 * v4 * v5 * v6 * v7 -
                    120 * u1 * v3 * v4 * v5 * v6 * v7 +
                    720 * u * v1 * v3 * v4 * v5 * v6 * v7 -
                    120 * u * v13 * v4 * v5 * v6 * v7 +
                    24 * u3 * v14 * v5 * v6 * v7 -
                    120 * u * v3 * v14 * v5 * v6 * v7 +
                    24 * u1 * v34 * v5 * v6 * v7 -
                    120 * u * v1 * v34 * v5 * v6 * v7 +
                    24 * u * v134 * v5 * v6 * v7 - 6 * u34 * v15 * v6 * v7 +
                    24 * u4 * v3 * v15 * v6 * v7 +
                    24 * u3 * v4 * v15 * v6 * v7 -
                    120 * u * v3 * v4 * v15 * v6 * v7 +
                    24 * u * v34 * v15 * v6 * v7 - 6 * u14 * v35 * v6 * v7 +
                    24 * u4 * v1 * v35 * v6 * v7 +
                    24 * u1 * v4 * v35 * v6 * v7 -
                    120 * u * v1 * v4 * v35 * v6 * v7 +
                    24 * u * v14 * v35 * v6 * v7 - 6 * u4 * v135 * v6 * v7 +
                    24 * u * v4 * v135 * v6 * v7 - 6 * u13 * v45 * v6 * v7 +
                    24 * u3 * v1 * v45 * v6 * v7 +
                    24 * u1 * v3 * v45 * v6 * v7 -
                    120 * u * v1 * v3 * v45 * v6 * v7 +
                    24 * u * v13 * v45 * v6 * v7 - 6 * u3 * v145 * v6 * v7 +
                    24 * u * v3 * v145 * v6 * v7 - 6 * u1 * v345 * v6 * v7 +
                    24 * u * v1 * v345 * v6 * v7 - 6 * u * v1345 * v6 * v7 +
                    2 * u345 * v16 * v7 - 6 * u45 * v3 * v16 * v7 -
                    6 * u35 * v4 * v16 * v7 + 24 * u5 * v3 * v4 * v16 * v7 -
                    6 * u5 * v34 * v16 * v7 - 6 * u34 * v5 * v16 * v7 +
                    24 * u4 * v3 * v5 * v16 * v7 +
                    24 * u3 * v4 * v5 * v16 * v7 -
                    120 * u * v3 * v4 * v5 * v16 * v7 +
                    24 * u * v34 * v5 * v16 * v7 - 6 * u4 * v35 * v16 * v7 +
                    24 * u * v4 * v35 * v16 * v7 - 6 * u3 * v45 * v16 * v7 +
                    24 * u * v3 * v45 * v16 * v7 - 6 * u * v345 * v16 * v7 +
                    2 * u145 * v36 * v7 - 6 * u45 * v1 * v36 * v7 -
                    6 * u15 * v4 * v36 * v7 + 24 * u5 * v1 * v4 * v36 * v7 -
                    6 * u5 * v14 * v36 * v7 - 6 * u14 * v5 * v36 * v7 +
                    24 * u4 * v1 * v5 * v36 * v7 +
                    24 * u1 * v4 * v5 * v36 * v7 -
                    120 * u * v1 * v4 * v5 * v36 * v7 +
                    24 * u * v14 * v5 * v36 * v7 - 6 * u4 * v15 * v36 * v7 +
                    24 * u * v4 * v15 * v36 * v7 - 6 * u1 * v45 * v36 * v7 +
                    24 * u * v1 * v45 * v36 * v7 - 6 * u * v145 * v36 * v7 +
                    2 * u45 * v136 * v7 - 6 * u5 * v4 * v136 * v7 -
                    6 * u4 * v5 * v136 * v7 + 24 * u * v4 * v5 * v136 * v7 -
                    6 * u * v45 * v136 * v7 + 2 * u135 * v46 * v7 -
                    6 * u35 * v1 * v46 * v7 - 6 * u15 * v3 * v46 * v7 +
                    24 * u5 * v1 * v3 * v46 * v7 - 6 * u5 * v13 * v46 * v7 -
                    6 * u13 * v5 * v46 * v7 + 24 * u3 * v1 * v5 * v46 * v7 +
                    24 * u1 * v3 * v5 * v46 * v7 -
                    120 * u * v1 * v3 * v5 * v46 * v7 +
                    24 * u * v13 * v5 * v46 * v7 - 6 * u3 * v15 * v46 * v7 +
                    24 * u * v3 * v15 * v46 * v7 - 6 * u1 * v35 * v46 * v7 +
                    24 * u * v1 * v35 * v46 * v7 - 6 * u * v135 * v46 * v7 +
                    2 * u35 * v146 * v7 - 6 * u5 * v3 * v146 * v7 -
                    6 * u3 * v5 * v146 * v7 + 24 * u * v3 * v5 * v146 * v7 -
                    6 * u * v35 * v146 * v7 + 2 * u15 * v346 * v7 -
                    6 * u5 * v1 * v346 * v7 - 6 * u1 * v5 * v346 * v7 +
                    24 * u * v1 * v5 * v346 * v7 - 6 * u * v15 * v346 * v7 +
                    2 * u5 * v1346 * v7 - 6 * u * v5 * v1346 * v7 +
                    2 * u134 * v56 * v7 - 6 * u34 * v1 * v56 * v7 -
                    6 * u14 * v3 * v56 * v7 + 24 * u4 * v1 * v3 * v56 * v7 -
                    6 * u4 * v13 * v56 * v7 - 6 * u13 * v4 * v56 * v7 +
                    24 * u3 * v1 * v4 * v56 * v7 +
                    24 * u1 * v3 * v4 * v56 * v7 -
                    120 * u * v1 * v3 * v4 * v56 * v7 +
                    24 * u * v13 * v4 * v56 * v7 - 6 * u3 * v14 * v56 * v7 +
                    24 * u * v3 * v14 * v56 * v7 - 6 * u1 * v34 * v56 * v7 +
                    24 * u * v1 * v34 * v56 * v7 - 6 * u * v134 * v56 * v7 +
                    2 * u34 * v156 * v7 - 6 * u4 * v3 * v156 * v7 -
                    6 * u3 * v4 * v156 * v7 + 24 * u * v3 * v4 * v156 * v7 -
                    6 * u * v34 * v156 * v7 + 2 * u14 * v356 * v7 -
                    6 * u4 * v1 * v356 * v7 - 6 * u1 * v4 * v356 * v7 +
                    24 * u * v1 * v4 * v356 * v7 - 6 * u * v14 * v356 * v7 +
                    2 * u4 * v1356 * v7 - 6 * u * v4 * v1356 * v7 +
                    2 * u13 * v456 * v7 - 6 * u3 * v1 * v456 * v7 -
                    6 * u1 * v3 * v456 * v7 + 24 * u * v1 * v3 * v456 * v7 -
                    6 * u * v13 * v456 * v7 + 2 * u3 * v1456 * v7 -
                    6 * u * v3 * v1456 * v7 + 2 * u1 * v3456 * v7 -
                    6 * u * v1 * v3456 * v7 + 2 * u * v13456 * v7 -
                    u3456 * v17 + 2 * u456 * v3 * v17 + 2 * u356 * v4 * v17 -
                    6 * u56 * v3 * v4 * v17 + 2 * u56 * v34 * v17 +
                    2 * u346 * v5 * v17 - 6 * u46 * v3 * v5 * v17 -
                    6 * u36 * v4 * v5 * v17 + 24 * u6 * v3 * v4 * v5 * v17 -
                    6 * u6 * v34 * v5 * v17 + 2 * u46 * v35 * v17 -
                    6 * u6 * v4 * v35 * v17 + 2 * u36 * v45 * v17 -
                    6 * u6 * v3 * v45 * v17 + 2 * u6 * v345 * v17 +
                    2 * u345 * v6 * v17 - 6 * u45 * v3 * v6 * v17 -
                    6 * u35 * v4 * v6 * v17 + 24 * u5 * v3 * v4 * v6 * v17 -
                    6 * u5 * v34 * v6 * v17 - 6 * u34 * v5 * v6 * v17 +
                    24 * u4 * v3 * v5 * v6 * v17 +
                    24 * u3 * v4 * v5 * v6 * v17 -
                    120 * u * v3 * v4 * v5 * v6 * v17 +
                    24 * u * v34 * v5 * v6 * v17 - 6 * u4 * v35 * v6 * v17 +
                    24 * u * v4 * v35 * v6 * v17 - 6 * u3 * v45 * v6 * v17 +
                    24 * u * v3 * v45 * v6 * v17 - 6 * u * v345 * v6 * v17 +
                    2 * u45 * v36 * v17 - 6 * u5 * v4 * v36 * v17 -
                    6 * u4 * v5 * v36 * v17 + 24 * u * v4 * v5 * v36 * v17 -
                    6 * u * v45 * v36 * v17 + 2 * u35 * v46 * v17 -
                    6 * u5 * v3 * v46 * v17 - 6 * u3 * v5 * v46 * v17 +
                    24 * u * v3 * v5 * v46 * v17 - 6 * u * v35 * v46 * v17 +
                    2 * u5 * v346 * v17 - 6 * u * v5 * v346 * v17 +
                    2 * u34 * v56 * v17 - 6 * u4 * v3 * v56 * v17 -
                    6 * u3 * v4 * v56 * v17 + 24 * u * v3 * v4 * v56 * v17 -
                    6 * u * v34 * v56 * v17 + 2 * u4 * v356 * v17 -
                    6 * u * v4 * v356 * v17 + 2 * u3 * v456 * v17 -
                    6 * u * v3 * v456 * v17 + 2 * u * v3456 * v17 -
                    u1456 * v37 + 2 * u456 * v1 * v37 + 2 * u156 * v4 * v37 -
                    6 * u56 * v1 * v4 * v37 + 2 * u56 * v14 * v37 +
                    2 * u146 * v5 * v37 - 6 * u46 * v1 * v5 * v37 -
                    6 * u16 * v4 * v5 * v37 + 24 * u6 * v1 * v4 * v5 * v37 -
                    6 * u6 * v14 * v5 * v37 + 2 * u46 * v15 * v37 -
                    6 * u6 * v4 * v15 * v37 + 2 * u16 * v45 * v37 -
                    6 * u6 * v1 * v45 * v37 + 2 * u6 * v145 * v37 +
                    2 * u145 * v6 * v37 - 6 * u45 * v1 * v6 * v37 -
                    6 * u15 * v4 * v6 * v37 + 24 * u5 * v1 * v4 * v6 * v37 -
                    6 * u5 * v14 * v6 * v37 - 6 * u14 * v5 * v6 * v37 +
                    24 * u4 * v1 * v5 * v6 * v37 +
                    24 * u1 * v4 * v5 * v6 * v37 -
                    120 * u * v1 * v4 * v5 * v6 * v37 +
                    24 * u * v14 * v5 * v6 * v37 - 6 * u4 * v15 * v6 * v37 +
                    24 * u * v4 * v15 * v6 * v37 - 6 * u1 * v45 * v6 * v37 +
                    24 * u * v1 * v45 * v6 * v37 - 6 * u * v145 * v6 * v37 +
                    2 * u45 * v16 * v37 - 6 * u5 * v4 * v16 * v37 -
                    6 * u4 * v5 * v16 * v37 + 24 * u * v4 * v5 * v16 * v37 -
                    6 * u * v45 * v16 * v37 + 2 * u15 * v46 * v37 -
                    6 * u5 * v1 * v46 * v37 - 6 * u1 * v5 * v46 * v37 +
                    24 * u * v1 * v5 * v46 * v37 - 6 * u * v15 * v46 * v37 +
                    2 * u5 * v146 * v37 - 6 * u * v5 * v146 * v37 +
                    2 * u14 * v56 * v37 - 6 * u4 * v1 * v56 * v37 -
                    6 * u1 * v4 * v56 * v37 + 24 * u * v1 * v4 * v56 * v37 -
                    6 * u * v14 * v56 * v37 + 2 * u4 * v156 * v37 -
                    6 * u * v4 * v156 * v37 + 2 * u1 * v456 * v37 -
                    6 * u * v1 * v456 * v37 + 2 * u * v1456 * v37 -
                    u456 * v137 + 2 * u56 * v4 * v137 + 2 * u46 * v5 * v137 -
                    6 * u6 * v4 * v5 * v137 + 2 * u6 * v45 * v137 +
                    2 * u45 * v6 * v137 - 6 * u5 * v4 * v6 * v137 -
                    6 * u4 * v5 * v6 * v137 + 24 * u * v4 * v5 * v6 * v137 -
                    6 * u * v45 * v6 * v137 + 2 * u5 * v46 * v137 -
                    6 * u * v5 * v46 * v137 + 2 * u4 * v56 * v137 -
                    6 * u * v4 * v56 * v137 + 2 * u * v456 * v137 -
                    u1356 * v47 + 2 * u356 * v1 * v47 + 2 * u156 * v3 * v47 -
                    6 * u56 * v1 * v3 * v47 + 2 * u56 * v13 * v47 +
                    2 * u136 * v5 * v47 - 6 * u36 * v1 * v5 * v47 -
                    6 * u16 * v3 * v5 * v47 + 24 * u6 * v1 * v3 * v5 * v47 -
                    6 * u6 * v13 * v5 * v47 + 2 * u36 * v15 * v47 -
                    6 * u6 * v3 * v15 * v47 + 2 * u16 * v35 * v47 -
                    6 * u6 * v1 * v35 * v47 + 2 * u6 * v135 * v47 +
                    2 * u135 * v6 * v47 - 6 * u35 * v1 * v6 * v47 -
                    6 * u15 * v3 * v6 * v47 + 24 * u5 * v1 * v3 * v6 * v47 -
                    6 * u5 * v13 * v6 * v47 - 6 * u13 * v5 * v6 * v47 +
                    24 * u3 * v1 * v5 * v6 * v47 +
                    24 * u1 * v3 * v5 * v6 * v47 -
                    120 * u * v1 * v3 * v5 * v6 * v47 +
                    24 * u * v13 * v5 * v6 * v47 - 6 * u3 * v15 * v6 * v47 +
                    24 * u * v3 * v15 * v6 * v47 - 6 * u1 * v35 * v6 * v47 +
                    24 * u * v1 * v35 * v6 * v47 - 6 * u * v135 * v6 * v47 +
                    2 * u35 * v16 * v47 - 6 * u5 * v3 * v16 * v47 -
                    6 * u3 * v5 * v16 * v47 + 24 * u * v3 * v5 * v16 * v47 -
                    6 * u * v35 * v16 * v47 + 2 * u15 * v36 * v47 -
                    6 * u5 * v1 * v36 * v47 - 6 * u1 * v5 * v36 * v47 +
                    24 * u * v1 * v5 * v36 * v47 - 6 * u * v15 * v36 * v47 +
                    2 * u5 * v136 * v47 - 6 * u * v5 * v136 * v47 +
                    2 * u13 * v56 * v47 - 6 * u3 * v1 * v56 * v47 -
                    6 * u1 * v3 * v56 * v47 + 24 * u * v1 * v3 * v56 * v47 -
                    6 * u * v13 * v56 * v47 + 2 * u3 * v156 * v47 -
                    6 * u * v3 * v156 * v47 + 2 * u1 * v356 * v47 -
                    6 * u * v1 * v356 * v47 + 2 * u * v1356 * v47 -
                    u356 * v147 + 2 * u56 * v3 * v147 + 2 * u36 * v5 * v147 -
                    6 * u6 * v3 * v5 * v147 + 2 * u6 * v35 * v147 +
                    2 * u35 * v6 * v147 - 6 * u5 * v3 * v6 * v147 -
                    6 * u3 * v5 * v6 * v147 + 24 * u * v3 * v5 * v6 * v147 -
                    6 * u * v35 * v6 * v147 + 2 * u5 * v36 * v147 -
                    6 * u * v5 * v36 * v147 + 2 * u3 * v56 * v147 -
                    6 * u * v3 * v56 * v147 + 2 * u * v356 * v147 -
                    u156 * v347 + 2 * u56 * v1 * v347 + 2 * u16 * v5 * v347 -
                    6 * u6 * v1 * v5 * v347 + 2 * u6 * v15 * v347 +
                    2 * u15 * v6 * v347 - 6 * u5 * v1 * v6 * v347 -
                    6 * u1 * v5 * v6 * v347 + 24 * u * v1 * v5 * v6 * v347 -
                    6 * u * v15 * v6 * v347 + 2 * u5 * v16 * v347 -
                    6 * u * v5 * v16 * v347 + 2 * u1 * v56 * v347 -
                    6 * u * v1 * v56 * v347 + 2 * u * v156 * v347 -
                    u56 * v1347 + 2 * u6 * v5 * v1347 + 2 * u5 * v6 * v1347 -
                    6 * u * v5 * v6 * v1347 + 2 * u * v56 * v1347 -
                    u1346 * v57 + 2 * u346 * v1 * v57 + 2 * u146 * v3 * v57 -
                    6 * u46 * v1 * v3 * v57 + 2 * u46 * v13 * v57 +
                    2 * u136 * v4 * v57 - 6 * u36 * v1 * v4 * v57 -
                    6 * u16 * v3 * v4 * v57 + 24 * u6 * v1 * v3 * v4 * v57 -
                    6 * u6 * v13 * v4 * v57 + 2 * u36 * v14 * v57 -
                    6 * u6 * v3 * v14 * v57 + 2 * u16 * v34 * v57 -
                    6 * u6 * v1 * v34 * v57 + 2 * u6 * v134 * v57 +
                    2 * u134 * v6 * v57 - 6 * u34 * v1 * v6 * v57 -
                    6 * u14 * v3 * v6 * v57 + 24 * u4 * v1 * v3 * v6 * v57 -
                    6 * u4 * v13 * v6 * v57 - 6 * u13 * v4 * v6 * v57 +
                    24 * u3 * v1 * v4 * v6 * v57 +
                    24 * u1 * v3 * v4 * v6 * v57 -
                    120 * u * v1 * v3 * v4 * v6 * v57 +
                    24 * u * v13 * v4 * v6 * v57 - 6 * u3 * v14 * v6 * v57 +
                    24 * u * v3 * v14 * v6 * v57 - 6 * u1 * v34 * v6 * v57 +
                    24 * u * v1 * v34 * v6 * v57 - 6 * u * v134 * v6 * v57 +
                    2 * u34 * v16 * v57 - 6 * u4 * v3 * v16 * v57 -
                    6 * u3 * v4 * v16 * v57 + 24 * u * v3 * v4 * v16 * v57 -
                    6 * u * v34 * v16 * v57 + 2 * u14 * v36 * v57 -
                    6 * u4 * v1 * v36 * v57 - 6 * u1 * v4 * v36 * v57 +
                    24 * u * v1 * v4 * v36 * v57 - 6 * u * v14 * v36 * v57 +
                    2 * u4 * v136 * v57 - 6 * u * v4 * v136 * v57 +
                    2 * u13 * v46 * v57 - 6 * u3 * v1 * v46 * v57 -
                    6 * u1 * v3 * v46 * v57 + 24 * u * v1 * v3 * v46 * v57 -
                    6 * u * v13 * v46 * v57 + 2 * u3 * v146 * v57 -
                    6 * u * v3 * v146 * v57 + 2 * u1 * v346 * v57 -
                    6 * u * v1 * v346 * v57 + 2 * u * v1346 * v57 -
                    u346 * v157 + 2 * u46 * v3 * v157 + 2 * u36 * v4 * v157 -
                    6 * u6 * v3 * v4 * v157 + 2 * u6 * v34 * v157 +
                    2 * u34 * v6 * v157 - 6 * u4 * v3 * v6 * v157 -
                    6 * u3 * v4 * v6 * v157 + 24 * u * v3 * v4 * v6 * v157 -
                    6 * u * v34 * v6 * v157 + 2 * u4 * v36 * v157 -
                    6 * u * v4 * v36 * v157 + 2 * u3 * v46 * v157 -
                    6 * u * v3 * v46 * v157 + 2 * u * v346 * v157 -
                    u146 * v357 + 2 * u46 * v1 * v357 + 2 * u16 * v4 * v357 -
                    6 * u6 * v1 * v4 * v357 + 2 * u6 * v14 * v357 +
                    2 * u14 * v6 * v357 - 6 * u4 * v1 * v6 * v357 -
                    6 * u1 * v4 * v6 * v357 + 24 * u * v1 * v4 * v6 * v357 -
                    6 * u * v14 * v6 * v357 + 2 * u4 * v16 * v357 -
                    6 * u * v4 * v16 * v357 + 2 * u1 * v46 * v357 -
                    6 * u * v1 * v46 * v357 + 2 * u * v146 * v357 -
                    u46 * v1357 + 2 * u6 * v4 * v1357 + 2 * u4 * v6 * v1357 -
                    6 * u * v4 * v6 * v1357 + 2 * u * v46 * v1357 -
                    u136 * v457 + 2 * u36 * v1 * v457 + 2 * u16 * v3 * v457 -
                    6 * u6 * v1 * v3 * v457 + 2 * u6 * v13 * v457 +
                    2 * u13 * v6 * v457 - 6 * u3 * v1 * v6 * v457 -
                    6 * u1 * v3 * v6 * v457 + 24 * u * v1 * v3 * v6 * v457 -
                    6 * u * v13 * v6 * v457 + 2 * u3 * v16 * v457 -
                    6 * u * v3 * v16 * v457 + 2 * u1 * v36 * v457 -
                    6 * u * v1 * v36 * v457 + 2 * u * v136 * v457 -
                    u36 * v1457 + 2 * u6 * v3 * v1457 + 2 * u3 * v6 * v1457 -
                    6 * u * v3 * v6 * v1457 + 2 * u * v36 * v1457 -
                    u16 * v3457 + 2 * u6 * v1 * v3457 + 2 * u1 * v6 * v3457 -
                    6 * u * v1 * v6 * v3457 + 2 * u * v16 * v3457 -
                    u6 * v13457 + 2 * u * v6 * v13457 - u1345 * v67 +
                    2 * u345 * v1 * v67 + 2 * u145 * v3 * v67 -
                    6 * u45 * v1 * v3 * v67 + 2 * u45 * v13 * v67 +
                    2 * u135 * v4 * v67 - 6 * u35 * v1 * v4 * v67 -
                    6 * u15 * v3 * v4 * v67 + 24 * u5 * v1 * v3 * v4 * v67 -
                    6 * u5 * v13 * v4 * v67 + 2 * u35 * v14 * v67 -
                    6 * u5 * v3 * v14 * v67 + 2 * u15 * v34 * v67 -
                    6 * u5 * v1 * v34 * v67 + 2 * u5 * v134 * v67 +
                    2 * u134 * v5 * v67 - 6 * u34 * v1 * v5 * v67 -
                    6 * u14 * v3 * v5 * v67 + 24 * u4 * v1 * v3 * v5 * v67 -
                    6 * u4 * v13 * v5 * v67 - 6 * u13 * v4 * v5 * v67 +
                    24 * u3 * v1 * v4 * v5 * v67 +
                    24 * u1 * v3 * v4 * v5 * v67 -
                    120 * u * v1 * v3 * v4 * v5 * v67 +
                    24 * u * v13 * v4 * v5 * v67 - 6 * u3 * v14 * v5 * v67 +
                    24 * u * v3 * v14 * v5 * v67 - 6 * u1 * v34 * v5 * v67 +
                    24 * u * v1 * v34 * v5 * v67 - 6 * u * v134 * v5 * v67 +
                    2 * u34 * v15 * v67 - 6 * u4 * v3 * v15 * v67 -
                    6 * u3 * v4 * v15 * v67 + 24 * u * v3 * v4 * v15 * v67 -
                    6 * u * v34 * v15 * v67 + 2 * u14 * v35 * v67 -
                    6 * u4 * v1 * v35 * v67 - 6 * u1 * v4 * v35 * v67 +
                    24 * u * v1 * v4 * v35 * v67 - 6 * u * v14 * v35 * v67 +
                    2 * u4 * v135 * v67 - 6 * u * v4 * v135 * v67 +
                    2 * u13 * v45 * v67 - 6 * u3 * v1 * v45 * v67 -
                    6 * u1 * v3 * v45 * v67 + 24 * u * v1 * v3 * v45 * v67 -
                    6 * u * v13 * v45 * v67 + 2 * u3 * v145 * v67 -
                    6 * u * v3 * v145 * v67 + 2 * u1 * v345 * v67 -
                    6 * u * v1 * v345 * v67 + 2 * u * v1345 * v67 -
                    u345 * v167 + 2 * u45 * v3 * v167 + 2 * u35 * v4 * v167 -
                    6 * u5 * v3 * v4 * v167 + 2 * u5 * v34 * v167 +
                    2 * u34 * v5 * v167 - 6 * u4 * v3 * v5 * v167 -
                    6 * u3 * v4 * v5 * v167 + 24 * u * v3 * v4 * v5 * v167 -
                    6 * u * v34 * v5 * v167 + 2 * u4 * v35 * v167 -
                    6 * u * v4 * v35 * v167 + 2 * u3 * v45 * v167 -
                    6 * u * v3 * v45 * v167 + 2 * u * v345 * v167 -
                    u145 * v367 + 2 * u45 * v1 * v367 + 2 * u15 * v4 * v367 -
                    6 * u5 * v1 * v4 * v367 + 2 * u5 * v14 * v367 +
                    2 * u14 * v5 * v367 - 6 * u4 * v1 * v5 * v367 -
                    6 * u1 * v4 * v5 * v367 + 24 * u * v1 * v4 * v5 * v367 -
                    6 * u * v14 * v5 * v367 + 2 * u4 * v15 * v367 -
                    6 * u * v4 * v15 * v367 + 2 * u1 * v45 * v367 -
                    6 * u * v1 * v45 * v367 + 2 * u * v145 * v367 -
                    u45 * v1367 + 2 * u5 * v4 * v1367 + 2 * u4 * v5 * v1367 -
                    6 * u * v4 * v5 * v1367 + 2 * u * v45 * v1367 -
                    u135 * v467 + 2 * u35 * v1 * v467 + 2 * u15 * v3 * v467 -
                    6 * u5 * v1 * v3 * v467 + 2 * u5 * v13 * v467 +
                    2 * u13 * v5 * v467 - 6 * u3 * v1 * v5 * v467 -
                    6 * u1 * v3 * v5 * v467 + 24 * u * v1 * v3 * v5 * v467 -
                    6 * u * v13 * v5 * v467 + 2 * u3 * v15 * v467 -
                    6 * u * v3 * v15 * v467 + 2 * u1 * v35 * v467 -
                    6 * u * v1 * v35 * v467 + 2 * u * v135 * v467 -
                    u35 * v1467 + 2 * u5 * v3 * v1467 + 2 * u3 * v5 * v1467 -
                    6 * u * v3 * v5 * v1467 + 2 * u * v35 * v1467 -
                    u15 * v3467 + 2 * u5 * v1 * v3467 + 2 * u1 * v5 * v3467 -
                    6 * u * v1 * v5 * v3467 + 2 * u * v15 * v3467 -
                    u5 * v13467 + 2 * u * v5 * v13467 - u134 * v567 +
                    2 * u34 * v1 * v567 + 2 * u14 * v3 * v567 -
                    6 * u4 * v1 * v3 * v567 + 2 * u4 * v13 * v567 +
                    2 * u13 * v4 * v567 - 6 * u3 * v1 * v4 * v567 -
                    6 * u1 * v3 * v4 * v567 + 24 * u * v1 * v3 * v4 * v567 -
                    6 * u * v13 * v4 * v567 + 2 * u3 * v14 * v567 -
                    6 * u * v3 * v14 * v567 + 2 * u1 * v34 * v567 -
                    6 * u * v1 * v34 * v567 + 2 * u * v134 * v567 -
                    u34 * v1567 + 2 * u4 * v3 * v1567 + 2 * u3 * v4 * v1567 -
                    6 * u * v3 * v4 * v1567 + 2 * u * v34 * v1567 -
                    u14 * v3567 + 2 * u4 * v1 * v3567 + 2 * u1 * v4 * v3567 -
                    6 * u * v1 * v4 * v3567 + 2 * u * v14 * v3567 -
                    u4 * v13567 + 2 * u * v4 * v13567 - u13 * v4567 +
                    2 * u3 * v1 * v4567 + 2 * u1 * v3 * v4567 -
                    6 * u * v1 * v3 * v4567 + 2 * u * v13 * v4567 -
                    u3 * v14567 + 2 * u * v3 * v14567 - u1 * v34567 +
                    2 * u * v1 * v34567 - u * v134567,
            .dual234567 =
                    u234567 - u34567 * v2 - u24567 * v3 + 2 * u4567 * v2 * v3 -
                    u4567 * v23 - u23567 * v4 + 2 * u3567 * v2 * v4 +
                    2 * u2567 * v3 * v4 - 6 * u567 * v2 * v3 * v4 +
                    2 * u567 * v23 * v4 - u3567 * v24 + 2 * u567 * v3 * v24 -
                    u2567 * v34 + 2 * u567 * v2 * v34 - u567 * v234 -
                    u23467 * v5 + 2 * u3467 * v2 * v5 + 2 * u2467 * v3 * v5 -
                    6 * u467 * v2 * v3 * v5 + 2 * u467 * v23 * v5 +
                    2 * u2367 * v4 * v5 - 6 * u367 * v2 * v4 * v5 -
                    6 * u267 * v3 * v4 * v5 + 24 * u67 * v2 * v3 * v4 * v5 -
                    6 * u67 * v23 * v4 * v5 + 2 * u367 * v24 * v5 -
                    6 * u67 * v3 * v24 * v5 + 2 * u267 * v34 * v5 -
                    6 * u67 * v2 * v34 * v5 + 2 * u67 * v234 * v5 -
                    u3467 * v25 + 2 * u467 * v3 * v25 + 2 * u367 * v4 * v25 -
                    6 * u67 * v3 * v4 * v25 + 2 * u67 * v34 * v25 -
                    u2467 * v35 + 2 * u467 * v2 * v35 + 2 * u267 * v4 * v35 -
                    6 * u67 * v2 * v4 * v35 + 2 * u67 * v24 * v35 -
                    u467 * v235 + 2 * u67 * v4 * v235 - u2367 * v45 +
                    2 * u367 * v2 * v45 + 2 * u267 * v3 * v45 -
                    6 * u67 * v2 * v3 * v45 + 2 * u67 * v23 * v45 -
                    u367 * v245 + 2 * u67 * v3 * v245 - u267 * v345 +
                    2 * u67 * v2 * v345 - u67 * v2345 - u23457 * v6 +
                    2 * u3457 * v2 * v6 + 2 * u2457 * v3 * v6 -
                    6 * u457 * v2 * v3 * v6 + 2 * u457 * v23 * v6 +
                    2 * u2357 * v4 * v6 - 6 * u357 * v2 * v4 * v6 -
                    6 * u257 * v3 * v4 * v6 + 24 * u57 * v2 * v3 * v4 * v6 -
                    6 * u57 * v23 * v4 * v6 + 2 * u357 * v24 * v6 -
                    6 * u57 * v3 * v24 * v6 + 2 * u257 * v34 * v6 -
                    6 * u57 * v2 * v34 * v6 + 2 * u57 * v234 * v6 +
                    2 * u2347 * v5 * v6 - 6 * u347 * v2 * v5 * v6 -
                    6 * u247 * v3 * v5 * v6 + 24 * u47 * v2 * v3 * v5 * v6 -
                    6 * u47 * v23 * v5 * v6 - 6 * u237 * v4 * v5 * v6 +
                    24 * u37 * v2 * v4 * v5 * v6 +
                    24 * u27 * v3 * v4 * v5 * v6 -
                    120 * u7 * v2 * v3 * v4 * v5 * v6 +
                    24 * u7 * v23 * v4 * v5 * v6 - 6 * u37 * v24 * v5 * v6 +
                    24 * u7 * v3 * v24 * v5 * v6 - 6 * u27 * v34 * v5 * v6 +
                    24 * u7 * v2 * v34 * v5 * v6 - 6 * u7 * v234 * v5 * v6 +
                    2 * u347 * v25 * v6 - 6 * u47 * v3 * v25 * v6 -
                    6 * u37 * v4 * v25 * v6 + 24 * u7 * v3 * v4 * v25 * v6 -
                    6 * u7 * v34 * v25 * v6 + 2 * u247 * v35 * v6 -
                    6 * u47 * v2 * v35 * v6 - 6 * u27 * v4 * v35 * v6 +
                    24 * u7 * v2 * v4 * v35 * v6 - 6 * u7 * v24 * v35 * v6 +
                    2 * u47 * v235 * v6 - 6 * u7 * v4 * v235 * v6 +
                    2 * u237 * v45 * v6 - 6 * u37 * v2 * v45 * v6 -
                    6 * u27 * v3 * v45 * v6 + 24 * u7 * v2 * v3 * v45 * v6 -
                    6 * u7 * v23 * v45 * v6 + 2 * u37 * v245 * v6 -
                    6 * u7 * v3 * v245 * v6 + 2 * u27 * v345 * v6 -
                    6 * u7 * v2 * v345 * v6 + 2 * u7 * v2345 * v6 -
                    u3457 * v26 + 2 * u457 * v3 * v26 + 2 * u357 * v4 * v26 -
                    6 * u57 * v3 * v4 * v26 + 2 * u57 * v34 * v26 +
                    2 * u347 * v5 * v26 - 6 * u47 * v3 * v5 * v26 -
                    6 * u37 * v4 * v5 * v26 + 24 * u7 * v3 * v4 * v5 * v26 -
                    6 * u7 * v34 * v5 * v26 + 2 * u47 * v35 * v26 -
                    6 * u7 * v4 * v35 * v26 + 2 * u37 * v45 * v26 -
                    6 * u7 * v3 * v45 * v26 + 2 * u7 * v345 * v26 -
                    u2457 * v36 + 2 * u457 * v2 * v36 + 2 * u257 * v4 * v36 -
                    6 * u57 * v2 * v4 * v36 + 2 * u57 * v24 * v36 +
                    2 * u247 * v5 * v36 - 6 * u47 * v2 * v5 * v36 -
                    6 * u27 * v4 * v5 * v36 + 24 * u7 * v2 * v4 * v5 * v36 -
                    6 * u7 * v24 * v5 * v36 + 2 * u47 * v25 * v36 -
                    6 * u7 * v4 * v25 * v36 + 2 * u27 * v45 * v36 -
                    6 * u7 * v2 * v45 * v36 + 2 * u7 * v245 * v36 -
                    u457 * v236 + 2 * u57 * v4 * v236 + 2 * u47 * v5 * v236 -
                    6 * u7 * v4 * v5 * v236 + 2 * u7 * v45 * v236 -
                    u2357 * v46 + 2 * u357 * v2 * v46 + 2 * u257 * v3 * v46 -
                    6 * u57 * v2 * v3 * v46 + 2 * u57 * v23 * v46 +
                    2 * u237 * v5 * v46 - 6 * u37 * v2 * v5 * v46 -
                    6 * u27 * v3 * v5 * v46 + 24 * u7 * v2 * v3 * v5 * v46 -
                    6 * u7 * v23 * v5 * v46 + 2 * u37 * v25 * v46 -
                    6 * u7 * v3 * v25 * v46 + 2 * u27 * v35 * v46 -
                    6 * u7 * v2 * v35 * v46 + 2 * u7 * v235 * v46 -
                    u357 * v246 + 2 * u57 * v3 * v246 + 2 * u37 * v5 * v246 -
                    6 * u7 * v3 * v5 * v246 + 2 * u7 * v35 * v246 -
                    u257 * v346 + 2 * u57 * v2 * v346 + 2 * u27 * v5 * v346 -
                    6 * u7 * v2 * v5 * v346 + 2 * u7 * v25 * v346 -
                    u57 * v2346 + 2 * u7 * v5 * v2346 - u2347 * v56 +
                    2 * u347 * v2 * v56 + 2 * u247 * v3 * v56 -
                    6 * u47 * v2 * v3 * v56 + 2 * u47 * v23 * v56 +
                    2 * u237 * v4 * v56 - 6 * u37 * v2 * v4 * v56 -
                    6 * u27 * v3 * v4 * v56 + 24 * u7 * v2 * v3 * v4 * v56 -
                    6 * u7 * v23 * v4 * v56 + 2 * u37 * v24 * v56 -
                    6 * u7 * v3 * v24 * v56 + 2 * u27 * v34 * v56 -
                    6 * u7 * v2 * v34 * v56 + 2 * u7 * v234 * v56 -
                    u347 * v256 + 2 * u47 * v3 * v256 + 2 * u37 * v4 * v256 -
                    6 * u7 * v3 * v4 * v256 + 2 * u7 * v34 * v256 -
                    u247 * v356 + 2 * u47 * v2 * v356 + 2 * u27 * v4 * v356 -
                    6 * u7 * v2 * v4 * v356 + 2 * u7 * v24 * v356 -
                    u47 * v2356 + 2 * u7 * v4 * v2356 - u237 * v456 +
                    2 * u37 * v2 * v456 + 2 * u27 * v3 * v456 -
                    6 * u7 * v2 * v3 * v456 + 2 * u7 * v23 * v456 -
                    u37 * v2456 + 2 * u7 * v3 * v2456 - u27 * v3456 +
                    2 * u7 * v2 * v3456 - u7 * v23456 - u23456 * v7 +
                    2 * u3456 * v2 * v7 + 2 * u2456 * v3 * v7 -
                    6 * u456 * v2 * v3 * v7 + 2 * u456 * v23 * v7 +
                    2 * u2356 * v4 * v7 - 6 * u356 * v2 * v4 * v7 -
                    6 * u256 * v3 * v4 * v7 + 24 * u56 * v2 * v3 * v4 * v7 -
                    6 * u56 * v23 * v4 * v7 + 2 * u356 * v24 * v7 -
                    6 * u56 * v3 * v24 * v7 + 2 * u256 * v34 * v7 -
                    6 * u56 * v2 * v34 * v7 + 2 * u56 * v234 * v7 +
                    2 * u2346 * v5 * v7 - 6 * u346 * v2 * v5 * v7 -
                    6 * u246 * v3 * v5 * v7 + 24 * u46 * v2 * v3 * v5 * v7 -
                    6 * u46 * v23 * v5 * v7 - 6 * u236 * v4 * v5 * v7 +
                    24 * u36 * v2 * v4 * v5 * v7 +
                    24 * u26 * v3 * v4 * v5 * v7 -
                    120 * u6 * v2 * v3 * v4 * v5 * v7 +
                    24 * u6 * v23 * v4 * v5 * v7 - 6 * u36 * v24 * v5 * v7 +
                    24 * u6 * v3 * v24 * v5 * v7 - 6 * u26 * v34 * v5 * v7 +
                    24 * u6 * v2 * v34 * v5 * v7 - 6 * u6 * v234 * v5 * v7 +
                    2 * u346 * v25 * v7 - 6 * u46 * v3 * v25 * v7 -
                    6 * u36 * v4 * v25 * v7 + 24 * u6 * v3 * v4 * v25 * v7 -
                    6 * u6 * v34 * v25 * v7 + 2 * u246 * v35 * v7 -
                    6 * u46 * v2 * v35 * v7 - 6 * u26 * v4 * v35 * v7 +
                    24 * u6 * v2 * v4 * v35 * v7 - 6 * u6 * v24 * v35 * v7 +
                    2 * u46 * v235 * v7 - 6 * u6 * v4 * v235 * v7 +
                    2 * u236 * v45 * v7 - 6 * u36 * v2 * v45 * v7 -
                    6 * u26 * v3 * v45 * v7 + 24 * u6 * v2 * v3 * v45 * v7 -
                    6 * u6 * v23 * v45 * v7 + 2 * u36 * v245 * v7 -
                    6 * u6 * v3 * v245 * v7 + 2 * u26 * v345 * v7 -
                    6 * u6 * v2 * v345 * v7 + 2 * u6 * v2345 * v7 +
                    2 * u2345 * v6 * v7 - 6 * u345 * v2 * v6 * v7 -
                    6 * u245 * v3 * v6 * v7 + 24 * u45 * v2 * v3 * v6 * v7 -
                    6 * u45 * v23 * v6 * v7 - 6 * u235 * v4 * v6 * v7 +
                    24 * u35 * v2 * v4 * v6 * v7 +
                    24 * u25 * v3 * v4 * v6 * v7 -
                    120 * u5 * v2 * v3 * v4 * v6 * v7 +
                    24 * u5 * v23 * v4 * v6 * v7 - 6 * u35 * v24 * v6 * v7 +
                    24 * u5 * v3 * v24 * v6 * v7 - 6 * u25 * v34 * v6 * v7 +
                    24 * u5 * v2 * v34 * v6 * v7 - 6 * u5 * v234 * v6 * v7 -
                    6 * u234 * v5 * v6 * v7 + 24 * u34 * v2 * v5 * v6 * v7 +
                    24 * u24 * v3 * v5 * v6 * v7 -
                    120 * u4 * v2 * v3 * v5 * v6 * v7 +
                    24 * u4 * v23 * v5 * v6 * v7 +
                    24 * u23 * v4 * v5 * v6 * v7 -
                    120 * u3 * v2 * v4 * v5 * v6 * v7 -
                    120 * u2 * v3 * v4 * v5 * v6 * v7 +
                    720 * u * v2 * v3 * v4 * v5 * v6 * v7 -
                    120 * u * v23 * v4 * v5 * v6 * v7 +
                    24 * u3 * v24 * v5 * v6 * v7 -
                    120 * u * v3 * v24 * v5 * v6 * v7 +
                    24 * u2 * v34 * v5 * v6 * v7 -
                    120 * u * v2 * v34 * v5 * v6 * v7 +
                    24 * u * v234 * v5 * v6 * v7 - 6 * u34 * v25 * v6 * v7 +
                    24 * u4 * v3 * v25 * v6 * v7 +
                    24 * u3 * v4 * v25 * v6 * v7 -
                    120 * u * v3 * v4 * v25 * v6 * v7 +
                    24 * u * v34 * v25 * v6 * v7 - 6 * u24 * v35 * v6 * v7 +
                    24 * u4 * v2 * v35 * v6 * v7 +
                    24 * u2 * v4 * v35 * v6 * v7 -
                    120 * u * v2 * v4 * v35 * v6 * v7 +
                    24 * u * v24 * v35 * v6 * v7 - 6 * u4 * v235 * v6 * v7 +
                    24 * u * v4 * v235 * v6 * v7 - 6 * u23 * v45 * v6 * v7 +
                    24 * u3 * v2 * v45 * v6 * v7 +
                    24 * u2 * v3 * v45 * v6 * v7 -
                    120 * u * v2 * v3 * v45 * v6 * v7 +
                    24 * u * v23 * v45 * v6 * v7 - 6 * u3 * v245 * v6 * v7 +
                    24 * u * v3 * v245 * v6 * v7 - 6 * u2 * v345 * v6 * v7 +
                    24 * u * v2 * v345 * v6 * v7 - 6 * u * v2345 * v6 * v7 +
                    2 * u345 * v26 * v7 - 6 * u45 * v3 * v26 * v7 -
                    6 * u35 * v4 * v26 * v7 + 24 * u5 * v3 * v4 * v26 * v7 -
                    6 * u5 * v34 * v26 * v7 - 6 * u34 * v5 * v26 * v7 +
                    24 * u4 * v3 * v5 * v26 * v7 +
                    24 * u3 * v4 * v5 * v26 * v7 -
                    120 * u * v3 * v4 * v5 * v26 * v7 +
                    24 * u * v34 * v5 * v26 * v7 - 6 * u4 * v35 * v26 * v7 +
                    24 * u * v4 * v35 * v26 * v7 - 6 * u3 * v45 * v26 * v7 +
                    24 * u * v3 * v45 * v26 * v7 - 6 * u * v345 * v26 * v7 +
                    2 * u245 * v36 * v7 - 6 * u45 * v2 * v36 * v7 -
                    6 * u25 * v4 * v36 * v7 + 24 * u5 * v2 * v4 * v36 * v7 -
                    6 * u5 * v24 * v36 * v7 - 6 * u24 * v5 * v36 * v7 +
                    24 * u4 * v2 * v5 * v36 * v7 +
                    24 * u2 * v4 * v5 * v36 * v7 -
                    120 * u * v2 * v4 * v5 * v36 * v7 +
                    24 * u * v24 * v5 * v36 * v7 - 6 * u4 * v25 * v36 * v7 +
                    24 * u * v4 * v25 * v36 * v7 - 6 * u2 * v45 * v36 * v7 +
                    24 * u * v2 * v45 * v36 * v7 - 6 * u * v245 * v36 * v7 +
                    2 * u45 * v236 * v7 - 6 * u5 * v4 * v236 * v7 -
                    6 * u4 * v5 * v236 * v7 + 24 * u * v4 * v5 * v236 * v7 -
                    6 * u * v45 * v236 * v7 + 2 * u235 * v46 * v7 -
                    6 * u35 * v2 * v46 * v7 - 6 * u25 * v3 * v46 * v7 +
                    24 * u5 * v2 * v3 * v46 * v7 - 6 * u5 * v23 * v46 * v7 -
                    6 * u23 * v5 * v46 * v7 + 24 * u3 * v2 * v5 * v46 * v7 +
                    24 * u2 * v3 * v5 * v46 * v7 -
                    120 * u * v2 * v3 * v5 * v46 * v7 +
                    24 * u * v23 * v5 * v46 * v7 - 6 * u3 * v25 * v46 * v7 +
                    24 * u * v3 * v25 * v46 * v7 - 6 * u2 * v35 * v46 * v7 +
                    24 * u * v2 * v35 * v46 * v7 - 6 * u * v235 * v46 * v7 +
                    2 * u35 * v246 * v7 - 6 * u5 * v3 * v246 * v7 -
                    6 * u3 * v5 * v246 * v7 + 24 * u * v3 * v5 * v246 * v7 -
                    6 * u * v35 * v246 * v7 + 2 * u25 * v346 * v7 -
                    6 * u5 * v2 * v346 * v7 - 6 * u2 * v5 * v346 * v7 +
                    24 * u * v2 * v5 * v346 * v7 - 6 * u * v25 * v346 * v7 +
                    2 * u5 * v2346 * v7 - 6 * u * v5 * v2346 * v7 +
                    2 * u234 * v56 * v7 - 6 * u34 * v2 * v56 * v7 -
                    6 * u24 * v3 * v56 * v7 + 24 * u4 * v2 * v3 * v56 * v7 -
                    6 * u4 * v23 * v56 * v7 - 6 * u23 * v4 * v56 * v7 +
                    24 * u3 * v2 * v4 * v56 * v7 +
                    24 * u2 * v3 * v4 * v56 * v7 -
                    120 * u * v2 * v3 * v4 * v56 * v7 +
                    24 * u * v23 * v4 * v56 * v7 - 6 * u3 * v24 * v56 * v7 +
                    24 * u * v3 * v24 * v56 * v7 - 6 * u2 * v34 * v56 * v7 +
                    24 * u * v2 * v34 * v56 * v7 - 6 * u * v234 * v56 * v7 +
                    2 * u34 * v256 * v7 - 6 * u4 * v3 * v256 * v7 -
                    6 * u3 * v4 * v256 * v7 + 24 * u * v3 * v4 * v256 * v7 -
                    6 * u * v34 * v256 * v7 + 2 * u24 * v356 * v7 -
                    6 * u4 * v2 * v356 * v7 - 6 * u2 * v4 * v356 * v7 +
                    24 * u * v2 * v4 * v356 * v7 - 6 * u * v24 * v356 * v7 +
                    2 * u4 * v2356 * v7 - 6 * u * v4 * v2356 * v7 +
                    2 * u23 * v456 * v7 - 6 * u3 * v2 * v456 * v7 -
                    6 * u2 * v3 * v456 * v7 + 24 * u * v2 * v3 * v456 * v7 -
                    6 * u * v23 * v456 * v7 + 2 * u3 * v2456 * v7 -
                    6 * u * v3 * v2456 * v7 + 2 * u2 * v3456 * v7 -
                    6 * u * v2 * v3456 * v7 + 2 * u * v23456 * v7 -
                    u3456 * v27 + 2 * u456 * v3 * v27 + 2 * u356 * v4 * v27 -
                    6 * u56 * v3 * v4 * v27 + 2 * u56 * v34 * v27 +
                    2 * u346 * v5 * v27 - 6 * u46 * v3 * v5 * v27 -
                    6 * u36 * v4 * v5 * v27 + 24 * u6 * v3 * v4 * v5 * v27 -
                    6 * u6 * v34 * v5 * v27 + 2 * u46 * v35 * v27 -
                    6 * u6 * v4 * v35 * v27 + 2 * u36 * v45 * v27 -
                    6 * u6 * v3 * v45 * v27 + 2 * u6 * v345 * v27 +
                    2 * u345 * v6 * v27 - 6 * u45 * v3 * v6 * v27 -
                    6 * u35 * v4 * v6 * v27 + 24 * u5 * v3 * v4 * v6 * v27 -
                    6 * u5 * v34 * v6 * v27 - 6 * u34 * v5 * v6 * v27 +
                    24 * u4 * v3 * v5 * v6 * v27 +
                    24 * u3 * v4 * v5 * v6 * v27 -
                    120 * u * v3 * v4 * v5 * v6 * v27 +
                    24 * u * v34 * v5 * v6 * v27 - 6 * u4 * v35 * v6 * v27 +
                    24 * u * v4 * v35 * v6 * v27 - 6 * u3 * v45 * v6 * v27 +
                    24 * u * v3 * v45 * v6 * v27 - 6 * u * v345 * v6 * v27 +
                    2 * u45 * v36 * v27 - 6 * u5 * v4 * v36 * v27 -
                    6 * u4 * v5 * v36 * v27 + 24 * u * v4 * v5 * v36 * v27 -
                    6 * u * v45 * v36 * v27 + 2 * u35 * v46 * v27 -
                    6 * u5 * v3 * v46 * v27 - 6 * u3 * v5 * v46 * v27 +
                    24 * u * v3 * v5 * v46 * v27 - 6 * u * v35 * v46 * v27 +
                    2 * u5 * v346 * v27 - 6 * u * v5 * v346 * v27 +
                    2 * u34 * v56 * v27 - 6 * u4 * v3 * v56 * v27 -
                    6 * u3 * v4 * v56 * v27 + 24 * u * v3 * v4 * v56 * v27 -
                    6 * u * v34 * v56 * v27 + 2 * u4 * v356 * v27 -
                    6 * u * v4 * v356 * v27 + 2 * u3 * v456 * v27 -
                    6 * u * v3 * v456 * v27 + 2 * u * v3456 * v27 -
                    u2456 * v37 + 2 * u456 * v2 * v37 + 2 * u256 * v4 * v37 -
                    6 * u56 * v2 * v4 * v37 + 2 * u56 * v24 * v37 +
                    2 * u246 * v5 * v37 - 6 * u46 * v2 * v5 * v37 -
                    6 * u26 * v4 * v5 * v37 + 24 * u6 * v2 * v4 * v5 * v37 -
                    6 * u6 * v24 * v5 * v37 + 2 * u46 * v25 * v37 -
                    6 * u6 * v4 * v25 * v37 + 2 * u26 * v45 * v37 -
                    6 * u6 * v2 * v45 * v37 + 2 * u6 * v245 * v37 +
                    2 * u245 * v6 * v37 - 6 * u45 * v2 * v6 * v37 -
                    6 * u25 * v4 * v6 * v37 + 24 * u5 * v2 * v4 * v6 * v37 -
                    6 * u5 * v24 * v6 * v37 - 6 * u24 * v5 * v6 * v37 +
                    24 * u4 * v2 * v5 * v6 * v37 +
                    24 * u2 * v4 * v5 * v6 * v37 -
                    120 * u * v2 * v4 * v5 * v6 * v37 +
                    24 * u * v24 * v5 * v6 * v37 - 6 * u4 * v25 * v6 * v37 +
                    24 * u * v4 * v25 * v6 * v37 - 6 * u2 * v45 * v6 * v37 +
                    24 * u * v2 * v45 * v6 * v37 - 6 * u * v245 * v6 * v37 +
                    2 * u45 * v26 * v37 - 6 * u5 * v4 * v26 * v37 -
                    6 * u4 * v5 * v26 * v37 + 24 * u * v4 * v5 * v26 * v37 -
                    6 * u * v45 * v26 * v37 + 2 * u25 * v46 * v37 -
                    6 * u5 * v2 * v46 * v37 - 6 * u2 * v5 * v46 * v37 +
                    24 * u * v2 * v5 * v46 * v37 - 6 * u * v25 * v46 * v37 +
                    2 * u5 * v246 * v37 - 6 * u * v5 * v246 * v37 +
                    2 * u24 * v56 * v37 - 6 * u4 * v2 * v56 * v37 -
                    6 * u2 * v4 * v56 * v37 + 24 * u * v2 * v4 * v56 * v37 -
                    6 * u * v24 * v56 * v37 + 2 * u4 * v256 * v37 -
                    6 * u * v4 * v256 * v37 + 2 * u2 * v456 * v37 -
                    6 * u * v2 * v456 * v37 + 2 * u * v2456 * v37 -
                    u456 * v237 + 2 * u56 * v4 * v237 + 2 * u46 * v5 * v237 -
                    6 * u6 * v4 * v5 * v237 + 2 * u6 * v45 * v237 +
                    2 * u45 * v6 * v237 - 6 * u5 * v4 * v6 * v237 -
                    6 * u4 * v5 * v6 * v237 + 24 * u * v4 * v5 * v6 * v237 -
                    6 * u * v45 * v6 * v237 + 2 * u5 * v46 * v237 -
                    6 * u * v5 * v46 * v237 + 2 * u4 * v56 * v237 -
                    6 * u * v4 * v56 * v237 + 2 * u * v456 * v237 -
                    u2356 * v47 + 2 * u356 * v2 * v47 + 2 * u256 * v3 * v47 -
                    6 * u56 * v2 * v3 * v47 + 2 * u56 * v23 * v47 +
                    2 * u236 * v5 * v47 - 6 * u36 * v2 * v5 * v47 -
                    6 * u26 * v3 * v5 * v47 + 24 * u6 * v2 * v3 * v5 * v47 -
                    6 * u6 * v23 * v5 * v47 + 2 * u36 * v25 * v47 -
                    6 * u6 * v3 * v25 * v47 + 2 * u26 * v35 * v47 -
                    6 * u6 * v2 * v35 * v47 + 2 * u6 * v235 * v47 +
                    2 * u235 * v6 * v47 - 6 * u35 * v2 * v6 * v47 -
                    6 * u25 * v3 * v6 * v47 + 24 * u5 * v2 * v3 * v6 * v47 -
                    6 * u5 * v23 * v6 * v47 - 6 * u23 * v5 * v6 * v47 +
                    24 * u3 * v2 * v5 * v6 * v47 +
                    24 * u2 * v3 * v5 * v6 * v47 -
                    120 * u * v2 * v3 * v5 * v6 * v47 +
                    24 * u * v23 * v5 * v6 * v47 - 6 * u3 * v25 * v6 * v47 +
                    24 * u * v3 * v25 * v6 * v47 - 6 * u2 * v35 * v6 * v47 +
                    24 * u * v2 * v35 * v6 * v47 - 6 * u * v235 * v6 * v47 +
                    2 * u35 * v26 * v47 - 6 * u5 * v3 * v26 * v47 -
                    6 * u3 * v5 * v26 * v47 + 24 * u * v3 * v5 * v26 * v47 -
                    6 * u * v35 * v26 * v47 + 2 * u25 * v36 * v47 -
                    6 * u5 * v2 * v36 * v47 - 6 * u2 * v5 * v36 * v47 +
                    24 * u * v2 * v5 * v36 * v47 - 6 * u * v25 * v36 * v47 +
                    2 * u5 * v236 * v47 - 6 * u * v5 * v236 * v47 +
                    2 * u23 * v56 * v47 - 6 * u3 * v2 * v56 * v47 -
                    6 * u2 * v3 * v56 * v47 + 24 * u * v2 * v3 * v56 * v47 -
                    6 * u * v23 * v56 * v47 + 2 * u3 * v256 * v47 -
                    6 * u * v3 * v256 * v47 + 2 * u2 * v356 * v47 -
                    6 * u * v2 * v356 * v47 + 2 * u * v2356 * v47 -
                    u356 * v247 + 2 * u56 * v3 * v247 + 2 * u36 * v5 * v247 -
                    6 * u6 * v3 * v5 * v247 + 2 * u6 * v35 * v247 +
                    2 * u35 * v6 * v247 - 6 * u5 * v3 * v6 * v247 -
                    6 * u3 * v5 * v6 * v247 + 24 * u * v3 * v5 * v6 * v247 -
                    6 * u * v35 * v6 * v247 + 2 * u5 * v36 * v247 -
                    6 * u * v5 * v36 * v247 + 2 * u3 * v56 * v247 -
                    6 * u * v3 * v56 * v247 + 2 * u * v356 * v247 -
                    u256 * v347 + 2 * u56 * v2 * v347 + 2 * u26 * v5 * v347 -
                    6 * u6 * v2 * v5 * v347 + 2 * u6 * v25 * v347 +
                    2 * u25 * v6 * v347 - 6 * u5 * v2 * v6 * v347 -
                    6 * u2 * v5 * v6 * v347 + 24 * u * v2 * v5 * v6 * v347 -
                    6 * u * v25 * v6 * v347 + 2 * u5 * v26 * v347 -
                    6 * u * v5 * v26 * v347 + 2 * u2 * v56 * v347 -
                    6 * u * v2 * v56 * v347 + 2 * u * v256 * v347 -
                    u56 * v2347 + 2 * u6 * v5 * v2347 + 2 * u5 * v6 * v2347 -
                    6 * u * v5 * v6 * v2347 + 2 * u * v56 * v2347 -
                    u2346 * v57 + 2 * u346 * v2 * v57 + 2 * u246 * v3 * v57 -
                    6 * u46 * v2 * v3 * v57 + 2 * u46 * v23 * v57 +
                    2 * u236 * v4 * v57 - 6 * u36 * v2 * v4 * v57 -
                    6 * u26 * v3 * v4 * v57 + 24 * u6 * v2 * v3 * v4 * v57 -
                    6 * u6 * v23 * v4 * v57 + 2 * u36 * v24 * v57 -
                    6 * u6 * v3 * v24 * v57 + 2 * u26 * v34 * v57 -
                    6 * u6 * v2 * v34 * v57 + 2 * u6 * v234 * v57 +
                    2 * u234 * v6 * v57 - 6 * u34 * v2 * v6 * v57 -
                    6 * u24 * v3 * v6 * v57 + 24 * u4 * v2 * v3 * v6 * v57 -
                    6 * u4 * v23 * v6 * v57 - 6 * u23 * v4 * v6 * v57 +
                    24 * u3 * v2 * v4 * v6 * v57 +
                    24 * u2 * v3 * v4 * v6 * v57 -
                    120 * u * v2 * v3 * v4 * v6 * v57 +
                    24 * u * v23 * v4 * v6 * v57 - 6 * u3 * v24 * v6 * v57 +
                    24 * u * v3 * v24 * v6 * v57 - 6 * u2 * v34 * v6 * v57 +
                    24 * u * v2 * v34 * v6 * v57 - 6 * u * v234 * v6 * v57 +
                    2 * u34 * v26 * v57 - 6 * u4 * v3 * v26 * v57 -
                    6 * u3 * v4 * v26 * v57 + 24 * u * v3 * v4 * v26 * v57 -
                    6 * u * v34 * v26 * v57 + 2 * u24 * v36 * v57 -
                    6 * u4 * v2 * v36 * v57 - 6 * u2 * v4 * v36 * v57 +
                    24 * u * v2 * v4 * v36 * v57 - 6 * u * v24 * v36 * v57 +
                    2 * u4 * v236 * v57 - 6 * u * v4 * v236 * v57 +
                    2 * u23 * v46 * v57 - 6 * u3 * v2 * v46 * v57 -
                    6 * u2 * v3 * v46 * v57 + 24 * u * v2 * v3 * v46 * v57 -
                    6 * u * v23 * v46 * v57 + 2 * u3 * v246 * v57 -
                    6 * u * v3 * v246 * v57 + 2 * u2 * v346 * v57 -
                    6 * u * v2 * v346 * v57 + 2 * u * v2346 * v57 -
                    u346 * v257 + 2 * u46 * v3 * v257 + 2 * u36 * v4 * v257 -
                    6 * u6 * v3 * v4 * v257 + 2 * u6 * v34 * v257 +
                    2 * u34 * v6 * v257 - 6 * u4 * v3 * v6 * v257 -
                    6 * u3 * v4 * v6 * v257 + 24 * u * v3 * v4 * v6 * v257 -
                    6 * u * v34 * v6 * v257 + 2 * u4 * v36 * v257 -
                    6 * u * v4 * v36 * v257 + 2 * u3 * v46 * v257 -
                    6 * u * v3 * v46 * v257 + 2 * u * v346 * v257 -
                    u246 * v357 + 2 * u46 * v2 * v357 + 2 * u26 * v4 * v357 -
                    6 * u6 * v2 * v4 * v357 + 2 * u6 * v24 * v357 +
                    2 * u24 * v6 * v357 - 6 * u4 * v2 * v6 * v357 -
                    6 * u2 * v4 * v6 * v357 + 24 * u * v2 * v4 * v6 * v357 -
                    6 * u * v24 * v6 * v357 + 2 * u4 * v26 * v357 -
                    6 * u * v4 * v26 * v357 + 2 * u2 * v46 * v357 -
                    6 * u * v2 * v46 * v357 + 2 * u * v246 * v357 -
                    u46 * v2357 + 2 * u6 * v4 * v2357 + 2 * u4 * v6 * v2357 -
                    6 * u * v4 * v6 * v2357 + 2 * u * v46 * v2357 -
                    u236 * v457 + 2 * u36 * v2 * v457 + 2 * u26 * v3 * v457 -
                    6 * u6 * v2 * v3 * v457 + 2 * u6 * v23 * v457 +
                    2 * u23 * v6 * v457 - 6 * u3 * v2 * v6 * v457 -
                    6 * u2 * v3 * v6 * v457 + 24 * u * v2 * v3 * v6 * v457 -
                    6 * u * v23 * v6 * v457 + 2 * u3 * v26 * v457 -
                    6 * u * v3 * v26 * v457 + 2 * u2 * v36 * v457 -
                    6 * u * v2 * v36 * v457 + 2 * u * v236 * v457 -
                    u36 * v2457 + 2 * u6 * v3 * v2457 + 2 * u3 * v6 * v2457 -
                    6 * u * v3 * v6 * v2457 + 2 * u * v36 * v2457 -
                    u26 * v3457 + 2 * u6 * v2 * v3457 + 2 * u2 * v6 * v3457 -
                    6 * u * v2 * v6 * v3457 + 2 * u * v26 * v3457 -
                    u6 * v23457 + 2 * u * v6 * v23457 - u2345 * v67 +
                    2 * u345 * v2 * v67 + 2 * u245 * v3 * v67 -
                    6 * u45 * v2 * v3 * v67 + 2 * u45 * v23 * v67 +
                    2 * u235 * v4 * v67 - 6 * u35 * v2 * v4 * v67 -
                    6 * u25 * v3 * v4 * v67 + 24 * u5 * v2 * v3 * v4 * v67 -
                    6 * u5 * v23 * v4 * v67 + 2 * u35 * v24 * v67 -
                    6 * u5 * v3 * v24 * v67 + 2 * u25 * v34 * v67 -
                    6 * u5 * v2 * v34 * v67 + 2 * u5 * v234 * v67 +
                    2 * u234 * v5 * v67 - 6 * u34 * v2 * v5 * v67 -
                    6 * u24 * v3 * v5 * v67 + 24 * u4 * v2 * v3 * v5 * v67 -
                    6 * u4 * v23 * v5 * v67 - 6 * u23 * v4 * v5 * v67 +
                    24 * u3 * v2 * v4 * v5 * v67 +
                    24 * u2 * v3 * v4 * v5 * v67 -
                    120 * u * v2 * v3 * v4 * v5 * v67 +
                    24 * u * v23 * v4 * v5 * v67 - 6 * u3 * v24 * v5 * v67 +
                    24 * u * v3 * v24 * v5 * v67 - 6 * u2 * v34 * v5 * v67 +
                    24 * u * v2 * v34 * v5 * v67 - 6 * u * v234 * v5 * v67 +
                    2 * u34 * v25 * v67 - 6 * u4 * v3 * v25 * v67 -
                    6 * u3 * v4 * v25 * v67 + 24 * u * v3 * v4 * v25 * v67 -
                    6 * u * v34 * v25 * v67 + 2 * u24 * v35 * v67 -
                    6 * u4 * v2 * v35 * v67 - 6 * u2 * v4 * v35 * v67 +
                    24 * u * v2 * v4 * v35 * v67 - 6 * u * v24 * v35 * v67 +
                    2 * u4 * v235 * v67 - 6 * u * v4 * v235 * v67 +
                    2 * u23 * v45 * v67 - 6 * u3 * v2 * v45 * v67 -
                    6 * u2 * v3 * v45 * v67 + 24 * u * v2 * v3 * v45 * v67 -
                    6 * u * v23 * v45 * v67 + 2 * u3 * v245 * v67 -
                    6 * u * v3 * v245 * v67 + 2 * u2 * v345 * v67 -
                    6 * u * v2 * v345 * v67 + 2 * u * v2345 * v67 -
                    u345 * v267 + 2 * u45 * v3 * v267 + 2 * u35 * v4 * v267 -
                    6 * u5 * v3 * v4 * v267 + 2 * u5 * v34 * v267 +
                    2 * u34 * v5 * v267 - 6 * u4 * v3 * v5 * v267 -
                    6 * u3 * v4 * v5 * v267 + 24 * u * v3 * v4 * v5 * v267 -
                    6 * u * v34 * v5 * v267 + 2 * u4 * v35 * v267 -
                    6 * u * v4 * v35 * v267 + 2 * u3 * v45 * v267 -
                    6 * u * v3 * v45 * v267 + 2 * u * v345 * v267 -
                    u245 * v367 + 2 * u45 * v2 * v367 + 2 * u25 * v4 * v367 -
                    6 * u5 * v2 * v4 * v367 + 2 * u5 * v24 * v367 +
                    2 * u24 * v5 * v367 - 6 * u4 * v2 * v5 * v367 -
                    6 * u2 * v4 * v5 * v367 + 24 * u * v2 * v4 * v5 * v367 -
                    6 * u * v24 * v5 * v367 + 2 * u4 * v25 * v367 -
                    6 * u * v4 * v25 * v367 + 2 * u2 * v45 * v367 -
                    6 * u * v2 * v45 * v367 + 2 * u * v245 * v367 -
                    u45 * v2367 + 2 * u5 * v4 * v2367 + 2 * u4 * v5 * v2367 -
                    6 * u * v4 * v5 * v2367 + 2 * u * v45 * v2367 -
                    u235 * v467 + 2 * u35 * v2 * v467 + 2 * u25 * v3 * v467 -
                    6 * u5 * v2 * v3 * v467 + 2 * u5 * v23 * v467 +
                    2 * u23 * v5 * v467 - 6 * u3 * v2 * v5 * v467 -
                    6 * u2 * v3 * v5 * v467 + 24 * u * v2 * v3 * v5 * v467 -
                    6 * u * v23 * v5 * v467 + 2 * u3 * v25 * v467 -
                    6 * u * v3 * v25 * v467 + 2 * u2 * v35 * v467 -
                    6 * u * v2 * v35 * v467 + 2 * u * v235 * v467 -
                    u35 * v2467 + 2 * u5 * v3 * v2467 + 2 * u3 * v5 * v2467 -
                    6 * u * v3 * v5 * v2467 + 2 * u * v35 * v2467 -
                    u25 * v3467 + 2 * u5 * v2 * v3467 + 2 * u2 * v5 * v3467 -
                    6 * u * v2 * v5 * v3467 + 2 * u * v25 * v3467 -
                    u5 * v23467 + 2 * u * v5 * v23467 - u234 * v567 +
                    2 * u34 * v2 * v567 + 2 * u24 * v3 * v567 -
                    6 * u4 * v2 * v3 * v567 + 2 * u4 * v23 * v567 +
                    2 * u23 * v4 * v567 - 6 * u3 * v2 * v4 * v567 -
                    6 * u2 * v3 * v4 * v567 + 24 * u * v2 * v3 * v4 * v567 -
                    6 * u * v23 * v4 * v567 + 2 * u3 * v24 * v567 -
                    6 * u * v3 * v24 * v567 + 2 * u2 * v34 * v567 -
                    6 * u * v2 * v34 * v567 + 2 * u * v234 * v567 -
                    u34 * v2567 + 2 * u4 * v3 * v2567 + 2 * u3 * v4 * v2567 -
                    6 * u * v3 * v4 * v2567 + 2 * u * v34 * v2567 -
                    u24 * v3567 + 2 * u4 * v2 * v3567 + 2 * u2 * v4 * v3567 -
                    6 * u * v2 * v4 * v3567 + 2 * u * v24 * v3567 -
                    u4 * v23567 + 2 * u * v4 * v23567 - u23 * v4567 +
                    2 * u3 * v2 * v4567 + 2 * u2 * v3 * v4567 -
                    6 * u * v2 * v3 * v4567 + 2 * u * v23 * v4567 -
                    u3 * v24567 + 2 * u * v3 * v24567 - u2 * v34567 +
                    2 * u * v2 * v34567 - u * v234567,
            .dual1234567 =
                    u1234567 - u234567 * v1 - u134567 * v2 +
                    2 * u34567 * v1 * v2 - u34567 * v12 - u124567 * v3 +
                    2 * u24567 * v1 * v3 + 2 * u14567 * v2 * v3 -
                    6 * u4567 * v1 * v2 * v3 + 2 * u4567 * v12 * v3 -
                    u24567 * v13 + 2 * u4567 * v2 * v13 - u14567 * v23 +
                    2 * u4567 * v1 * v23 - u4567 * v123 - u123567 * v4 +
                    2 * u23567 * v1 * v4 + 2 * u13567 * v2 * v4 -
                    6 * u3567 * v1 * v2 * v4 + 2 * u3567 * v12 * v4 +
                    2 * u12567 * v3 * v4 - 6 * u2567 * v1 * v3 * v4 -
                    6 * u1567 * v2 * v3 * v4 + 24 * u567 * v1 * v2 * v3 * v4 -
                    6 * u567 * v12 * v3 * v4 + 2 * u2567 * v13 * v4 -
                    6 * u567 * v2 * v13 * v4 + 2 * u1567 * v23 * v4 -
                    6 * u567 * v1 * v23 * v4 + 2 * u567 * v123 * v4 -
                    u23567 * v14 + 2 * u3567 * v2 * v14 + 2 * u2567 * v3 * v14 -
                    6 * u567 * v2 * v3 * v14 + 2 * u567 * v23 * v14 -
                    u13567 * v24 + 2 * u3567 * v1 * v24 + 2 * u1567 * v3 * v24 -
                    6 * u567 * v1 * v3 * v24 + 2 * u567 * v13 * v24 -
                    u3567 * v124 + 2 * u567 * v3 * v124 - u12567 * v34 +
                    2 * u2567 * v1 * v34 + 2 * u1567 * v2 * v34 -
                    6 * u567 * v1 * v2 * v34 + 2 * u567 * v12 * v34 -
                    u2567 * v134 + 2 * u567 * v2 * v134 - u1567 * v234 +
                    2 * u567 * v1 * v234 - u567 * v1234 - u123467 * v5 +
                    2 * u23467 * v1 * v5 + 2 * u13467 * v2 * v5 -
                    6 * u3467 * v1 * v2 * v5 + 2 * u3467 * v12 * v5 +
                    2 * u12467 * v3 * v5 - 6 * u2467 * v1 * v3 * v5 -
                    6 * u1467 * v2 * v3 * v5 + 24 * u467 * v1 * v2 * v3 * v5 -
                    6 * u467 * v12 * v3 * v5 + 2 * u2467 * v13 * v5 -
                    6 * u467 * v2 * v13 * v5 + 2 * u1467 * v23 * v5 -
                    6 * u467 * v1 * v23 * v5 + 2 * u467 * v123 * v5 +
                    2 * u12367 * v4 * v5 - 6 * u2367 * v1 * v4 * v5 -
                    6 * u1367 * v2 * v4 * v5 + 24 * u367 * v1 * v2 * v4 * v5 -
                    6 * u367 * v12 * v4 * v5 - 6 * u1267 * v3 * v4 * v5 +
                    24 * u267 * v1 * v3 * v4 * v5 +
                    24 * u167 * v2 * v3 * v4 * v5 -
                    120 * u67 * v1 * v2 * v3 * v4 * v5 +
                    24 * u67 * v12 * v3 * v4 * v5 - 6 * u267 * v13 * v4 * v5 +
                    24 * u67 * v2 * v13 * v4 * v5 - 6 * u167 * v23 * v4 * v5 +
                    24 * u67 * v1 * v23 * v4 * v5 - 6 * u67 * v123 * v4 * v5 +
                    2 * u2367 * v14 * v5 - 6 * u367 * v2 * v14 * v5 -
                    6 * u267 * v3 * v14 * v5 + 24 * u67 * v2 * v3 * v14 * v5 -
                    6 * u67 * v23 * v14 * v5 + 2 * u1367 * v24 * v5 -
                    6 * u367 * v1 * v24 * v5 - 6 * u167 * v3 * v24 * v5 +
                    24 * u67 * v1 * v3 * v24 * v5 - 6 * u67 * v13 * v24 * v5 +
                    2 * u367 * v124 * v5 - 6 * u67 * v3 * v124 * v5 +
                    2 * u1267 * v34 * v5 - 6 * u267 * v1 * v34 * v5 -
                    6 * u167 * v2 * v34 * v5 + 24 * u67 * v1 * v2 * v34 * v5 -
                    6 * u67 * v12 * v34 * v5 + 2 * u267 * v134 * v5 -
                    6 * u67 * v2 * v134 * v5 + 2 * u167 * v234 * v5 -
                    6 * u67 * v1 * v234 * v5 + 2 * u67 * v1234 * v5 -
                    u23467 * v15 + 2 * u3467 * v2 * v15 + 2 * u2467 * v3 * v15 -
                    6 * u467 * v2 * v3 * v15 + 2 * u467 * v23 * v15 +
                    2 * u2367 * v4 * v15 - 6 * u367 * v2 * v4 * v15 -
                    6 * u267 * v3 * v4 * v15 + 24 * u67 * v2 * v3 * v4 * v15 -
                    6 * u67 * v23 * v4 * v15 + 2 * u367 * v24 * v15 -
                    6 * u67 * v3 * v24 * v15 + 2 * u267 * v34 * v15 -
                    6 * u67 * v2 * v34 * v15 + 2 * u67 * v234 * v15 -
                    u13467 * v25 + 2 * u3467 * v1 * v25 + 2 * u1467 * v3 * v25 -
                    6 * u467 * v1 * v3 * v25 + 2 * u467 * v13 * v25 +
                    2 * u1367 * v4 * v25 - 6 * u367 * v1 * v4 * v25 -
                    6 * u167 * v3 * v4 * v25 + 24 * u67 * v1 * v3 * v4 * v25 -
                    6 * u67 * v13 * v4 * v25 + 2 * u367 * v14 * v25 -
                    6 * u67 * v3 * v14 * v25 + 2 * u167 * v34 * v25 -
                    6 * u67 * v1 * v34 * v25 + 2 * u67 * v134 * v25 -
                    u3467 * v125 + 2 * u467 * v3 * v125 + 2 * u367 * v4 * v125 -
                    6 * u67 * v3 * v4 * v125 + 2 * u67 * v34 * v125 -
                    u12467 * v35 + 2 * u2467 * v1 * v35 + 2 * u1467 * v2 * v35 -
                    6 * u467 * v1 * v2 * v35 + 2 * u467 * v12 * v35 +
                    2 * u1267 * v4 * v35 - 6 * u267 * v1 * v4 * v35 -
                    6 * u167 * v2 * v4 * v35 + 24 * u67 * v1 * v2 * v4 * v35 -
                    6 * u67 * v12 * v4 * v35 + 2 * u267 * v14 * v35 -
                    6 * u67 * v2 * v14 * v35 + 2 * u167 * v24 * v35 -
                    6 * u67 * v1 * v24 * v35 + 2 * u67 * v124 * v35 -
                    u2467 * v135 + 2 * u467 * v2 * v135 + 2 * u267 * v4 * v135 -
                    6 * u67 * v2 * v4 * v135 + 2 * u67 * v24 * v135 -
                    u1467 * v235 + 2 * u467 * v1 * v235 + 2 * u167 * v4 * v235 -
                    6 * u67 * v1 * v4 * v235 + 2 * u67 * v14 * v235 -
                    u467 * v1235 + 2 * u67 * v4 * v1235 - u12367 * v45 +
                    2 * u2367 * v1 * v45 + 2 * u1367 * v2 * v45 -
                    6 * u367 * v1 * v2 * v45 + 2 * u367 * v12 * v45 +
                    2 * u1267 * v3 * v45 - 6 * u267 * v1 * v3 * v45 -
                    6 * u167 * v2 * v3 * v45 + 24 * u67 * v1 * v2 * v3 * v45 -
                    6 * u67 * v12 * v3 * v45 + 2 * u267 * v13 * v45 -
                    6 * u67 * v2 * v13 * v45 + 2 * u167 * v23 * v45 -
                    6 * u67 * v1 * v23 * v45 + 2 * u67 * v123 * v45 -
                    u2367 * v145 + 2 * u367 * v2 * v145 + 2 * u267 * v3 * v145 -
                    6 * u67 * v2 * v3 * v145 + 2 * u67 * v23 * v145 -
                    u1367 * v245 + 2 * u367 * v1 * v245 + 2 * u167 * v3 * v245 -
                    6 * u67 * v1 * v3 * v245 + 2 * u67 * v13 * v245 -
                    u367 * v1245 + 2 * u67 * v3 * v1245 - u1267 * v345 +
                    2 * u267 * v1 * v345 + 2 * u167 * v2 * v345 -
                    6 * u67 * v1 * v2 * v345 + 2 * u67 * v12 * v345 -
                    u267 * v1345 + 2 * u67 * v2 * v1345 - u167 * v2345 +
                    2 * u67 * v1 * v2345 - u67 * v12345 - u123457 * v6 +
                    2 * u23457 * v1 * v6 + 2 * u13457 * v2 * v6 -
                    6 * u3457 * v1 * v2 * v6 + 2 * u3457 * v12 * v6 +
                    2 * u12457 * v3 * v6 - 6 * u2457 * v1 * v3 * v6 -
                    6 * u1457 * v2 * v3 * v6 + 24 * u457 * v1 * v2 * v3 * v6 -
                    6 * u457 * v12 * v3 * v6 + 2 * u2457 * v13 * v6 -
                    6 * u457 * v2 * v13 * v6 + 2 * u1457 * v23 * v6 -
                    6 * u457 * v1 * v23 * v6 + 2 * u457 * v123 * v6 +
                    2 * u12357 * v4 * v6 - 6 * u2357 * v1 * v4 * v6 -
                    6 * u1357 * v2 * v4 * v6 + 24 * u357 * v1 * v2 * v4 * v6 -
                    6 * u357 * v12 * v4 * v6 - 6 * u1257 * v3 * v4 * v6 +
                    24 * u257 * v1 * v3 * v4 * v6 +
                    24 * u157 * v2 * v3 * v4 * v6 -
                    120 * u57 * v1 * v2 * v3 * v4 * v6 +
                    24 * u57 * v12 * v3 * v4 * v6 - 6 * u257 * v13 * v4 * v6 +
                    24 * u57 * v2 * v13 * v4 * v6 - 6 * u157 * v23 * v4 * v6 +
                    24 * u57 * v1 * v23 * v4 * v6 - 6 * u57 * v123 * v4 * v6 +
                    2 * u2357 * v14 * v6 - 6 * u357 * v2 * v14 * v6 -
                    6 * u257 * v3 * v14 * v6 + 24 * u57 * v2 * v3 * v14 * v6 -
                    6 * u57 * v23 * v14 * v6 + 2 * u1357 * v24 * v6 -
                    6 * u357 * v1 * v24 * v6 - 6 * u157 * v3 * v24 * v6 +
                    24 * u57 * v1 * v3 * v24 * v6 - 6 * u57 * v13 * v24 * v6 +
                    2 * u357 * v124 * v6 - 6 * u57 * v3 * v124 * v6 +
                    2 * u1257 * v34 * v6 - 6 * u257 * v1 * v34 * v6 -
                    6 * u157 * v2 * v34 * v6 + 24 * u57 * v1 * v2 * v34 * v6 -
                    6 * u57 * v12 * v34 * v6 + 2 * u257 * v134 * v6 -
                    6 * u57 * v2 * v134 * v6 + 2 * u157 * v234 * v6 -
                    6 * u57 * v1 * v234 * v6 + 2 * u57 * v1234 * v6 +
                    2 * u12347 * v5 * v6 - 6 * u2347 * v1 * v5 * v6 -
                    6 * u1347 * v2 * v5 * v6 + 24 * u347 * v1 * v2 * v5 * v6 -
                    6 * u347 * v12 * v5 * v6 - 6 * u1247 * v3 * v5 * v6 +
                    24 * u247 * v1 * v3 * v5 * v6 +
                    24 * u147 * v2 * v3 * v5 * v6 -
                    120 * u47 * v1 * v2 * v3 * v5 * v6 +
                    24 * u47 * v12 * v3 * v5 * v6 - 6 * u247 * v13 * v5 * v6 +
                    24 * u47 * v2 * v13 * v5 * v6 - 6 * u147 * v23 * v5 * v6 +
                    24 * u47 * v1 * v23 * v5 * v6 - 6 * u47 * v123 * v5 * v6 -
                    6 * u1237 * v4 * v5 * v6 + 24 * u237 * v1 * v4 * v5 * v6 +
                    24 * u137 * v2 * v4 * v5 * v6 -
                    120 * u37 * v1 * v2 * v4 * v5 * v6 +
                    24 * u37 * v12 * v4 * v5 * v6 +
                    24 * u127 * v3 * v4 * v5 * v6 -
                    120 * u27 * v1 * v3 * v4 * v5 * v6 -
                    120 * u17 * v2 * v3 * v4 * v5 * v6 +
                    720 * u7 * v1 * v2 * v3 * v4 * v5 * v6 -
                    120 * u7 * v12 * v3 * v4 * v5 * v6 +
                    24 * u27 * v13 * v4 * v5 * v6 -
                    120 * u7 * v2 * v13 * v4 * v5 * v6 +
                    24 * u17 * v23 * v4 * v5 * v6 -
                    120 * u7 * v1 * v23 * v4 * v5 * v6 +
                    24 * u7 * v123 * v4 * v5 * v6 - 6 * u237 * v14 * v5 * v6 +
                    24 * u37 * v2 * v14 * v5 * v6 +
                    24 * u27 * v3 * v14 * v5 * v6 -
                    120 * u7 * v2 * v3 * v14 * v5 * v6 +
                    24 * u7 * v23 * v14 * v5 * v6 - 6 * u137 * v24 * v5 * v6 +
                    24 * u37 * v1 * v24 * v5 * v6 +
                    24 * u17 * v3 * v24 * v5 * v6 -
                    120 * u7 * v1 * v3 * v24 * v5 * v6 +
                    24 * u7 * v13 * v24 * v5 * v6 - 6 * u37 * v124 * v5 * v6 +
                    24 * u7 * v3 * v124 * v5 * v6 - 6 * u127 * v34 * v5 * v6 +
                    24 * u27 * v1 * v34 * v5 * v6 +
                    24 * u17 * v2 * v34 * v5 * v6 -
                    120 * u7 * v1 * v2 * v34 * v5 * v6 +
                    24 * u7 * v12 * v34 * v5 * v6 - 6 * u27 * v134 * v5 * v6 +
                    24 * u7 * v2 * v134 * v5 * v6 - 6 * u17 * v234 * v5 * v6 +
                    24 * u7 * v1 * v234 * v5 * v6 - 6 * u7 * v1234 * v5 * v6 +
                    2 * u2347 * v15 * v6 - 6 * u347 * v2 * v15 * v6 -
                    6 * u247 * v3 * v15 * v6 + 24 * u47 * v2 * v3 * v15 * v6 -
                    6 * u47 * v23 * v15 * v6 - 6 * u237 * v4 * v15 * v6 +
                    24 * u37 * v2 * v4 * v15 * v6 +
                    24 * u27 * v3 * v4 * v15 * v6 -
                    120 * u7 * v2 * v3 * v4 * v15 * v6 +
                    24 * u7 * v23 * v4 * v15 * v6 - 6 * u37 * v24 * v15 * v6 +
                    24 * u7 * v3 * v24 * v15 * v6 - 6 * u27 * v34 * v15 * v6 +
                    24 * u7 * v2 * v34 * v15 * v6 - 6 * u7 * v234 * v15 * v6 +
                    2 * u1347 * v25 * v6 - 6 * u347 * v1 * v25 * v6 -
                    6 * u147 * v3 * v25 * v6 + 24 * u47 * v1 * v3 * v25 * v6 -
                    6 * u47 * v13 * v25 * v6 - 6 * u137 * v4 * v25 * v6 +
                    24 * u37 * v1 * v4 * v25 * v6 +
                    24 * u17 * v3 * v4 * v25 * v6 -
                    120 * u7 * v1 * v3 * v4 * v25 * v6 +
                    24 * u7 * v13 * v4 * v25 * v6 - 6 * u37 * v14 * v25 * v6 +
                    24 * u7 * v3 * v14 * v25 * v6 - 6 * u17 * v34 * v25 * v6 +
                    24 * u7 * v1 * v34 * v25 * v6 - 6 * u7 * v134 * v25 * v6 +
                    2 * u347 * v125 * v6 - 6 * u47 * v3 * v125 * v6 -
                    6 * u37 * v4 * v125 * v6 + 24 * u7 * v3 * v4 * v125 * v6 -
                    6 * u7 * v34 * v125 * v6 + 2 * u1247 * v35 * v6 -
                    6 * u247 * v1 * v35 * v6 - 6 * u147 * v2 * v35 * v6 +
                    24 * u47 * v1 * v2 * v35 * v6 - 6 * u47 * v12 * v35 * v6 -
                    6 * u127 * v4 * v35 * v6 + 24 * u27 * v1 * v4 * v35 * v6 +
                    24 * u17 * v2 * v4 * v35 * v6 -
                    120 * u7 * v1 * v2 * v4 * v35 * v6 +
                    24 * u7 * v12 * v4 * v35 * v6 - 6 * u27 * v14 * v35 * v6 +
                    24 * u7 * v2 * v14 * v35 * v6 - 6 * u17 * v24 * v35 * v6 +
                    24 * u7 * v1 * v24 * v35 * v6 - 6 * u7 * v124 * v35 * v6 +
                    2 * u247 * v135 * v6 - 6 * u47 * v2 * v135 * v6 -
                    6 * u27 * v4 * v135 * v6 + 24 * u7 * v2 * v4 * v135 * v6 -
                    6 * u7 * v24 * v135 * v6 + 2 * u147 * v235 * v6 -
                    6 * u47 * v1 * v235 * v6 - 6 * u17 * v4 * v235 * v6 +
                    24 * u7 * v1 * v4 * v235 * v6 - 6 * u7 * v14 * v235 * v6 +
                    2 * u47 * v1235 * v6 - 6 * u7 * v4 * v1235 * v6 +
                    2 * u1237 * v45 * v6 - 6 * u237 * v1 * v45 * v6 -
                    6 * u137 * v2 * v45 * v6 + 24 * u37 * v1 * v2 * v45 * v6 -
                    6 * u37 * v12 * v45 * v6 - 6 * u127 * v3 * v45 * v6 +
                    24 * u27 * v1 * v3 * v45 * v6 +
                    24 * u17 * v2 * v3 * v45 * v6 -
                    120 * u7 * v1 * v2 * v3 * v45 * v6 +
                    24 * u7 * v12 * v3 * v45 * v6 - 6 * u27 * v13 * v45 * v6 +
                    24 * u7 * v2 * v13 * v45 * v6 - 6 * u17 * v23 * v45 * v6 +
                    24 * u7 * v1 * v23 * v45 * v6 - 6 * u7 * v123 * v45 * v6 +
                    2 * u237 * v145 * v6 - 6 * u37 * v2 * v145 * v6 -
                    6 * u27 * v3 * v145 * v6 + 24 * u7 * v2 * v3 * v145 * v6 -
                    6 * u7 * v23 * v145 * v6 + 2 * u137 * v245 * v6 -
                    6 * u37 * v1 * v245 * v6 - 6 * u17 * v3 * v245 * v6 +
                    24 * u7 * v1 * v3 * v245 * v6 - 6 * u7 * v13 * v245 * v6 +
                    2 * u37 * v1245 * v6 - 6 * u7 * v3 * v1245 * v6 +
                    2 * u127 * v345 * v6 - 6 * u27 * v1 * v345 * v6 -
                    6 * u17 * v2 * v345 * v6 + 24 * u7 * v1 * v2 * v345 * v6 -
                    6 * u7 * v12 * v345 * v6 + 2 * u27 * v1345 * v6 -
                    6 * u7 * v2 * v1345 * v6 + 2 * u17 * v2345 * v6 -
                    6 * u7 * v1 * v2345 * v6 + 2 * u7 * v12345 * v6 -
                    u23457 * v16 + 2 * u3457 * v2 * v16 + 2 * u2457 * v3 * v16 -
                    6 * u457 * v2 * v3 * v16 + 2 * u457 * v23 * v16 +
                    2 * u2357 * v4 * v16 - 6 * u357 * v2 * v4 * v16 -
                    6 * u257 * v3 * v4 * v16 + 24 * u57 * v2 * v3 * v4 * v16 -
                    6 * u57 * v23 * v4 * v16 + 2 * u357 * v24 * v16 -
                    6 * u57 * v3 * v24 * v16 + 2 * u257 * v34 * v16 -
                    6 * u57 * v2 * v34 * v16 + 2 * u57 * v234 * v16 +
                    2 * u2347 * v5 * v16 - 6 * u347 * v2 * v5 * v16 -
                    6 * u247 * v3 * v5 * v16 + 24 * u47 * v2 * v3 * v5 * v16 -
                    6 * u47 * v23 * v5 * v16 - 6 * u237 * v4 * v5 * v16 +
                    24 * u37 * v2 * v4 * v5 * v16 +
                    24 * u27 * v3 * v4 * v5 * v16 -
                    120 * u7 * v2 * v3 * v4 * v5 * v16 +
                    24 * u7 * v23 * v4 * v5 * v16 - 6 * u37 * v24 * v5 * v16 +
                    24 * u7 * v3 * v24 * v5 * v16 - 6 * u27 * v34 * v5 * v16 +
                    24 * u7 * v2 * v34 * v5 * v16 - 6 * u7 * v234 * v5 * v16 +
                    2 * u347 * v25 * v16 - 6 * u47 * v3 * v25 * v16 -
                    6 * u37 * v4 * v25 * v16 + 24 * u7 * v3 * v4 * v25 * v16 -
                    6 * u7 * v34 * v25 * v16 + 2 * u247 * v35 * v16 -
                    6 * u47 * v2 * v35 * v16 - 6 * u27 * v4 * v35 * v16 +
                    24 * u7 * v2 * v4 * v35 * v16 - 6 * u7 * v24 * v35 * v16 +
                    2 * u47 * v235 * v16 - 6 * u7 * v4 * v235 * v16 +
                    2 * u237 * v45 * v16 - 6 * u37 * v2 * v45 * v16 -
                    6 * u27 * v3 * v45 * v16 + 24 * u7 * v2 * v3 * v45 * v16 -
                    6 * u7 * v23 * v45 * v16 + 2 * u37 * v245 * v16 -
                    6 * u7 * v3 * v245 * v16 + 2 * u27 * v345 * v16 -
                    6 * u7 * v2 * v345 * v16 + 2 * u7 * v2345 * v16 -
                    u13457 * v26 + 2 * u3457 * v1 * v26 + 2 * u1457 * v3 * v26 -
                    6 * u457 * v1 * v3 * v26 + 2 * u457 * v13 * v26 +
                    2 * u1357 * v4 * v26 - 6 * u357 * v1 * v4 * v26 -
                    6 * u157 * v3 * v4 * v26 + 24 * u57 * v1 * v3 * v4 * v26 -
                    6 * u57 * v13 * v4 * v26 + 2 * u357 * v14 * v26 -
                    6 * u57 * v3 * v14 * v26 + 2 * u157 * v34 * v26 -
                    6 * u57 * v1 * v34 * v26 + 2 * u57 * v134 * v26 +
                    2 * u1347 * v5 * v26 - 6 * u347 * v1 * v5 * v26 -
                    6 * u147 * v3 * v5 * v26 + 24 * u47 * v1 * v3 * v5 * v26 -
                    6 * u47 * v13 * v5 * v26 - 6 * u137 * v4 * v5 * v26 +
                    24 * u37 * v1 * v4 * v5 * v26 +
                    24 * u17 * v3 * v4 * v5 * v26 -
                    120 * u7 * v1 * v3 * v4 * v5 * v26 +
                    24 * u7 * v13 * v4 * v5 * v26 - 6 * u37 * v14 * v5 * v26 +
                    24 * u7 * v3 * v14 * v5 * v26 - 6 * u17 * v34 * v5 * v26 +
                    24 * u7 * v1 * v34 * v5 * v26 - 6 * u7 * v134 * v5 * v26 +
                    2 * u347 * v15 * v26 - 6 * u47 * v3 * v15 * v26 -
                    6 * u37 * v4 * v15 * v26 + 24 * u7 * v3 * v4 * v15 * v26 -
                    6 * u7 * v34 * v15 * v26 + 2 * u147 * v35 * v26 -
                    6 * u47 * v1 * v35 * v26 - 6 * u17 * v4 * v35 * v26 +
                    24 * u7 * v1 * v4 * v35 * v26 - 6 * u7 * v14 * v35 * v26 +
                    2 * u47 * v135 * v26 - 6 * u7 * v4 * v135 * v26 +
                    2 * u137 * v45 * v26 - 6 * u37 * v1 * v45 * v26 -
                    6 * u17 * v3 * v45 * v26 + 24 * u7 * v1 * v3 * v45 * v26 -
                    6 * u7 * v13 * v45 * v26 + 2 * u37 * v145 * v26 -
                    6 * u7 * v3 * v145 * v26 + 2 * u17 * v345 * v26 -
                    6 * u7 * v1 * v345 * v26 + 2 * u7 * v1345 * v26 -
                    u3457 * v126 + 2 * u457 * v3 * v126 + 2 * u357 * v4 * v126 -
                    6 * u57 * v3 * v4 * v126 + 2 * u57 * v34 * v126 +
                    2 * u347 * v5 * v126 - 6 * u47 * v3 * v5 * v126 -
                    6 * u37 * v4 * v5 * v126 + 24 * u7 * v3 * v4 * v5 * v126 -
                    6 * u7 * v34 * v5 * v126 + 2 * u47 * v35 * v126 -
                    6 * u7 * v4 * v35 * v126 + 2 * u37 * v45 * v126 -
                    6 * u7 * v3 * v45 * v126 + 2 * u7 * v345 * v126 -
                    u12457 * v36 + 2 * u2457 * v1 * v36 + 2 * u1457 * v2 * v36 -
                    6 * u457 * v1 * v2 * v36 + 2 * u457 * v12 * v36 +
                    2 * u1257 * v4 * v36 - 6 * u257 * v1 * v4 * v36 -
                    6 * u157 * v2 * v4 * v36 + 24 * u57 * v1 * v2 * v4 * v36 -
                    6 * u57 * v12 * v4 * v36 + 2 * u257 * v14 * v36 -
                    6 * u57 * v2 * v14 * v36 + 2 * u157 * v24 * v36 -
                    6 * u57 * v1 * v24 * v36 + 2 * u57 * v124 * v36 +
                    2 * u1247 * v5 * v36 - 6 * u247 * v1 * v5 * v36 -
                    6 * u147 * v2 * v5 * v36 + 24 * u47 * v1 * v2 * v5 * v36 -
                    6 * u47 * v12 * v5 * v36 - 6 * u127 * v4 * v5 * v36 +
                    24 * u27 * v1 * v4 * v5 * v36 +
                    24 * u17 * v2 * v4 * v5 * v36 -
                    120 * u7 * v1 * v2 * v4 * v5 * v36 +
                    24 * u7 * v12 * v4 * v5 * v36 - 6 * u27 * v14 * v5 * v36 +
                    24 * u7 * v2 * v14 * v5 * v36 - 6 * u17 * v24 * v5 * v36 +
                    24 * u7 * v1 * v24 * v5 * v36 - 6 * u7 * v124 * v5 * v36 +
                    2 * u247 * v15 * v36 - 6 * u47 * v2 * v15 * v36 -
                    6 * u27 * v4 * v15 * v36 + 24 * u7 * v2 * v4 * v15 * v36 -
                    6 * u7 * v24 * v15 * v36 + 2 * u147 * v25 * v36 -
                    6 * u47 * v1 * v25 * v36 - 6 * u17 * v4 * v25 * v36 +
                    24 * u7 * v1 * v4 * v25 * v36 - 6 * u7 * v14 * v25 * v36 +
                    2 * u47 * v125 * v36 - 6 * u7 * v4 * v125 * v36 +
                    2 * u127 * v45 * v36 - 6 * u27 * v1 * v45 * v36 -
                    6 * u17 * v2 * v45 * v36 + 24 * u7 * v1 * v2 * v45 * v36 -
                    6 * u7 * v12 * v45 * v36 + 2 * u27 * v145 * v36 -
                    6 * u7 * v2 * v145 * v36 + 2 * u17 * v245 * v36 -
                    6 * u7 * v1 * v245 * v36 + 2 * u7 * v1245 * v36 -
                    u2457 * v136 + 2 * u457 * v2 * v136 + 2 * u257 * v4 * v136 -
                    6 * u57 * v2 * v4 * v136 + 2 * u57 * v24 * v136 +
                    2 * u247 * v5 * v136 - 6 * u47 * v2 * v5 * v136 -
                    6 * u27 * v4 * v5 * v136 + 24 * u7 * v2 * v4 * v5 * v136 -
                    6 * u7 * v24 * v5 * v136 + 2 * u47 * v25 * v136 -
                    6 * u7 * v4 * v25 * v136 + 2 * u27 * v45 * v136 -
                    6 * u7 * v2 * v45 * v136 + 2 * u7 * v245 * v136 -
                    u1457 * v236 + 2 * u457 * v1 * v236 + 2 * u157 * v4 * v236 -
                    6 * u57 * v1 * v4 * v236 + 2 * u57 * v14 * v236 +
                    2 * u147 * v5 * v236 - 6 * u47 * v1 * v5 * v236 -
                    6 * u17 * v4 * v5 * v236 + 24 * u7 * v1 * v4 * v5 * v236 -
                    6 * u7 * v14 * v5 * v236 + 2 * u47 * v15 * v236 -
                    6 * u7 * v4 * v15 * v236 + 2 * u17 * v45 * v236 -
                    6 * u7 * v1 * v45 * v236 + 2 * u7 * v145 * v236 -
                    u457 * v1236 + 2 * u57 * v4 * v1236 + 2 * u47 * v5 * v1236 -
                    6 * u7 * v4 * v5 * v1236 + 2 * u7 * v45 * v1236 -
                    u12357 * v46 + 2 * u2357 * v1 * v46 + 2 * u1357 * v2 * v46 -
                    6 * u357 * v1 * v2 * v46 + 2 * u357 * v12 * v46 +
                    2 * u1257 * v3 * v46 - 6 * u257 * v1 * v3 * v46 -
                    6 * u157 * v2 * v3 * v46 + 24 * u57 * v1 * v2 * v3 * v46 -
                    6 * u57 * v12 * v3 * v46 + 2 * u257 * v13 * v46 -
                    6 * u57 * v2 * v13 * v46 + 2 * u157 * v23 * v46 -
                    6 * u57 * v1 * v23 * v46 + 2 * u57 * v123 * v46 +
                    2 * u1237 * v5 * v46 - 6 * u237 * v1 * v5 * v46 -
                    6 * u137 * v2 * v5 * v46 + 24 * u37 * v1 * v2 * v5 * v46 -
                    6 * u37 * v12 * v5 * v46 - 6 * u127 * v3 * v5 * v46 +
                    24 * u27 * v1 * v3 * v5 * v46 +
                    24 * u17 * v2 * v3 * v5 * v46 -
                    120 * u7 * v1 * v2 * v3 * v5 * v46 +
                    24 * u7 * v12 * v3 * v5 * v46 - 6 * u27 * v13 * v5 * v46 +
                    24 * u7 * v2 * v13 * v5 * v46 - 6 * u17 * v23 * v5 * v46 +
                    24 * u7 * v1 * v23 * v5 * v46 - 6 * u7 * v123 * v5 * v46 +
                    2 * u237 * v15 * v46 - 6 * u37 * v2 * v15 * v46 -
                    6 * u27 * v3 * v15 * v46 + 24 * u7 * v2 * v3 * v15 * v46 -
                    6 * u7 * v23 * v15 * v46 + 2 * u137 * v25 * v46 -
                    6 * u37 * v1 * v25 * v46 - 6 * u17 * v3 * v25 * v46 +
                    24 * u7 * v1 * v3 * v25 * v46 - 6 * u7 * v13 * v25 * v46 +
                    2 * u37 * v125 * v46 - 6 * u7 * v3 * v125 * v46 +
                    2 * u127 * v35 * v46 - 6 * u27 * v1 * v35 * v46 -
                    6 * u17 * v2 * v35 * v46 + 24 * u7 * v1 * v2 * v35 * v46 -
                    6 * u7 * v12 * v35 * v46 + 2 * u27 * v135 * v46 -
                    6 * u7 * v2 * v135 * v46 + 2 * u17 * v235 * v46 -
                    6 * u7 * v1 * v235 * v46 + 2 * u7 * v1235 * v46 -
                    u2357 * v146 + 2 * u357 * v2 * v146 + 2 * u257 * v3 * v146 -
                    6 * u57 * v2 * v3 * v146 + 2 * u57 * v23 * v146 +
                    2 * u237 * v5 * v146 - 6 * u37 * v2 * v5 * v146 -
                    6 * u27 * v3 * v5 * v146 + 24 * u7 * v2 * v3 * v5 * v146 -
                    6 * u7 * v23 * v5 * v146 + 2 * u37 * v25 * v146 -
                    6 * u7 * v3 * v25 * v146 + 2 * u27 * v35 * v146 -
                    6 * u7 * v2 * v35 * v146 + 2 * u7 * v235 * v146 -
                    u1357 * v246 + 2 * u357 * v1 * v246 + 2 * u157 * v3 * v246 -
                    6 * u57 * v1 * v3 * v246 + 2 * u57 * v13 * v246 +
                    2 * u137 * v5 * v246 - 6 * u37 * v1 * v5 * v246 -
                    6 * u17 * v3 * v5 * v246 + 24 * u7 * v1 * v3 * v5 * v246 -
                    6 * u7 * v13 * v5 * v246 + 2 * u37 * v15 * v246 -
                    6 * u7 * v3 * v15 * v246 + 2 * u17 * v35 * v246 -
                    6 * u7 * v1 * v35 * v246 + 2 * u7 * v135 * v246 -
                    u357 * v1246 + 2 * u57 * v3 * v1246 + 2 * u37 * v5 * v1246 -
                    6 * u7 * v3 * v5 * v1246 + 2 * u7 * v35 * v1246 -
                    u1257 * v346 + 2 * u257 * v1 * v346 + 2 * u157 * v2 * v346 -
                    6 * u57 * v1 * v2 * v346 + 2 * u57 * v12 * v346 +
                    2 * u127 * v5 * v346 - 6 * u27 * v1 * v5 * v346 -
                    6 * u17 * v2 * v5 * v346 + 24 * u7 * v1 * v2 * v5 * v346 -
                    6 * u7 * v12 * v5 * v346 + 2 * u27 * v15 * v346 -
                    6 * u7 * v2 * v15 * v346 + 2 * u17 * v25 * v346 -
                    6 * u7 * v1 * v25 * v346 + 2 * u7 * v125 * v346 -
                    u257 * v1346 + 2 * u57 * v2 * v1346 + 2 * u27 * v5 * v1346 -
                    6 * u7 * v2 * v5 * v1346 + 2 * u7 * v25 * v1346 -
                    u157 * v2346 + 2 * u57 * v1 * v2346 + 2 * u17 * v5 * v2346 -
                    6 * u7 * v1 * v5 * v2346 + 2 * u7 * v15 * v2346 -
                    u57 * v12346 + 2 * u7 * v5 * v12346 - u12347 * v56 +
                    2 * u2347 * v1 * v56 + 2 * u1347 * v2 * v56 -
                    6 * u347 * v1 * v2 * v56 + 2 * u347 * v12 * v56 +
                    2 * u1247 * v3 * v56 - 6 * u247 * v1 * v3 * v56 -
                    6 * u147 * v2 * v3 * v56 + 24 * u47 * v1 * v2 * v3 * v56 -
                    6 * u47 * v12 * v3 * v56 + 2 * u247 * v13 * v56 -
                    6 * u47 * v2 * v13 * v56 + 2 * u147 * v23 * v56 -
                    6 * u47 * v1 * v23 * v56 + 2 * u47 * v123 * v56 +
                    2 * u1237 * v4 * v56 - 6 * u237 * v1 * v4 * v56 -
                    6 * u137 * v2 * v4 * v56 + 24 * u37 * v1 * v2 * v4 * v56 -
                    6 * u37 * v12 * v4 * v56 - 6 * u127 * v3 * v4 * v56 +
                    24 * u27 * v1 * v3 * v4 * v56 +
                    24 * u17 * v2 * v3 * v4 * v56 -
                    120 * u7 * v1 * v2 * v3 * v4 * v56 +
                    24 * u7 * v12 * v3 * v4 * v56 - 6 * u27 * v13 * v4 * v56 +
                    24 * u7 * v2 * v13 * v4 * v56 - 6 * u17 * v23 * v4 * v56 +
                    24 * u7 * v1 * v23 * v4 * v56 - 6 * u7 * v123 * v4 * v56 +
                    2 * u237 * v14 * v56 - 6 * u37 * v2 * v14 * v56 -
                    6 * u27 * v3 * v14 * v56 + 24 * u7 * v2 * v3 * v14 * v56 -
                    6 * u7 * v23 * v14 * v56 + 2 * u137 * v24 * v56 -
                    6 * u37 * v1 * v24 * v56 - 6 * u17 * v3 * v24 * v56 +
                    24 * u7 * v1 * v3 * v24 * v56 - 6 * u7 * v13 * v24 * v56 +
                    2 * u37 * v124 * v56 - 6 * u7 * v3 * v124 * v56 +
                    2 * u127 * v34 * v56 - 6 * u27 * v1 * v34 * v56 -
                    6 * u17 * v2 * v34 * v56 + 24 * u7 * v1 * v2 * v34 * v56 -
                    6 * u7 * v12 * v34 * v56 + 2 * u27 * v134 * v56 -
                    6 * u7 * v2 * v134 * v56 + 2 * u17 * v234 * v56 -
                    6 * u7 * v1 * v234 * v56 + 2 * u7 * v1234 * v56 -
                    u2347 * v156 + 2 * u347 * v2 * v156 + 2 * u247 * v3 * v156 -
                    6 * u47 * v2 * v3 * v156 + 2 * u47 * v23 * v156 +
                    2 * u237 * v4 * v156 - 6 * u37 * v2 * v4 * v156 -
                    6 * u27 * v3 * v4 * v156 + 24 * u7 * v2 * v3 * v4 * v156 -
                    6 * u7 * v23 * v4 * v156 + 2 * u37 * v24 * v156 -
                    6 * u7 * v3 * v24 * v156 + 2 * u27 * v34 * v156 -
                    6 * u7 * v2 * v34 * v156 + 2 * u7 * v234 * v156 -
                    u1347 * v256 + 2 * u347 * v1 * v256 + 2 * u147 * v3 * v256 -
                    6 * u47 * v1 * v3 * v256 + 2 * u47 * v13 * v256 +
                    2 * u137 * v4 * v256 - 6 * u37 * v1 * v4 * v256 -
                    6 * u17 * v3 * v4 * v256 + 24 * u7 * v1 * v3 * v4 * v256 -
                    6 * u7 * v13 * v4 * v256 + 2 * u37 * v14 * v256 -
                    6 * u7 * v3 * v14 * v256 + 2 * u17 * v34 * v256 -
                    6 * u7 * v1 * v34 * v256 + 2 * u7 * v134 * v256 -
                    u347 * v1256 + 2 * u47 * v3 * v1256 + 2 * u37 * v4 * v1256 -
                    6 * u7 * v3 * v4 * v1256 + 2 * u7 * v34 * v1256 -
                    u1247 * v356 + 2 * u247 * v1 * v356 + 2 * u147 * v2 * v356 -
                    6 * u47 * v1 * v2 * v356 + 2 * u47 * v12 * v356 +
                    2 * u127 * v4 * v356 - 6 * u27 * v1 * v4 * v356 -
                    6 * u17 * v2 * v4 * v356 + 24 * u7 * v1 * v2 * v4 * v356 -
                    6 * u7 * v12 * v4 * v356 + 2 * u27 * v14 * v356 -
                    6 * u7 * v2 * v14 * v356 + 2 * u17 * v24 * v356 -
                    6 * u7 * v1 * v24 * v356 + 2 * u7 * v124 * v356 -
                    u247 * v1356 + 2 * u47 * v2 * v1356 + 2 * u27 * v4 * v1356 -
                    6 * u7 * v2 * v4 * v1356 + 2 * u7 * v24 * v1356 -
                    u147 * v2356 + 2 * u47 * v1 * v2356 + 2 * u17 * v4 * v2356 -
                    6 * u7 * v1 * v4 * v2356 + 2 * u7 * v14 * v2356 -
                    u47 * v12356 + 2 * u7 * v4 * v12356 - u1237 * v456 +
                    2 * u237 * v1 * v456 + 2 * u137 * v2 * v456 -
                    6 * u37 * v1 * v2 * v456 + 2 * u37 * v12 * v456 +
                    2 * u127 * v3 * v456 - 6 * u27 * v1 * v3 * v456 -
                    6 * u17 * v2 * v3 * v456 + 24 * u7 * v1 * v2 * v3 * v456 -
                    6 * u7 * v12 * v3 * v456 + 2 * u27 * v13 * v456 -
                    6 * u7 * v2 * v13 * v456 + 2 * u17 * v23 * v456 -
                    6 * u7 * v1 * v23 * v456 + 2 * u7 * v123 * v456 -
                    u237 * v1456 + 2 * u37 * v2 * v1456 + 2 * u27 * v3 * v1456 -
                    6 * u7 * v2 * v3 * v1456 + 2 * u7 * v23 * v1456 -
                    u137 * v2456 + 2 * u37 * v1 * v2456 + 2 * u17 * v3 * v2456 -
                    6 * u7 * v1 * v3 * v2456 + 2 * u7 * v13 * v2456 -
                    u37 * v12456 + 2 * u7 * v3 * v12456 - u127 * v3456 +
                    2 * u27 * v1 * v3456 + 2 * u17 * v2 * v3456 -
                    6 * u7 * v1 * v2 * v3456 + 2 * u7 * v12 * v3456 -
                    u27 * v13456 + 2 * u7 * v2 * v13456 - u17 * v23456 +
                    2 * u7 * v1 * v23456 - u7 * v123456 - u123456 * v7 +
                    2 * u23456 * v1 * v7 + 2 * u13456 * v2 * v7 -
                    6 * u3456 * v1 * v2 * v7 + 2 * u3456 * v12 * v7 +
                    2 * u12456 * v3 * v7 - 6 * u2456 * v1 * v3 * v7 -
                    6 * u1456 * v2 * v3 * v7 + 24 * u456 * v1 * v2 * v3 * v7 -
                    6 * u456 * v12 * v3 * v7 + 2 * u2456 * v13 * v7 -
                    6 * u456 * v2 * v13 * v7 + 2 * u1456 * v23 * v7 -
                    6 * u456 * v1 * v23 * v7 + 2 * u456 * v123 * v7 +
                    2 * u12356 * v4 * v7 - 6 * u2356 * v1 * v4 * v7 -
                    6 * u1356 * v2 * v4 * v7 + 24 * u356 * v1 * v2 * v4 * v7 -
                    6 * u356 * v12 * v4 * v7 - 6 * u1256 * v3 * v4 * v7 +
                    24 * u256 * v1 * v3 * v4 * v7 +
                    24 * u156 * v2 * v3 * v4 * v7 -
                    120 * u56 * v1 * v2 * v3 * v4 * v7 +
                    24 * u56 * v12 * v3 * v4 * v7 - 6 * u256 * v13 * v4 * v7 +
                    24 * u56 * v2 * v13 * v4 * v7 - 6 * u156 * v23 * v4 * v7 +
                    24 * u56 * v1 * v23 * v4 * v7 - 6 * u56 * v123 * v4 * v7 +
                    2 * u2356 * v14 * v7 - 6 * u356 * v2 * v14 * v7 -
                    6 * u256 * v3 * v14 * v7 + 24 * u56 * v2 * v3 * v14 * v7 -
                    6 * u56 * v23 * v14 * v7 + 2 * u1356 * v24 * v7 -
                    6 * u356 * v1 * v24 * v7 - 6 * u156 * v3 * v24 * v7 +
                    24 * u56 * v1 * v3 * v24 * v7 - 6 * u56 * v13 * v24 * v7 +
                    2 * u356 * v124 * v7 - 6 * u56 * v3 * v124 * v7 +
                    2 * u1256 * v34 * v7 - 6 * u256 * v1 * v34 * v7 -
                    6 * u156 * v2 * v34 * v7 + 24 * u56 * v1 * v2 * v34 * v7 -
                    6 * u56 * v12 * v34 * v7 + 2 * u256 * v134 * v7 -
                    6 * u56 * v2 * v134 * v7 + 2 * u156 * v234 * v7 -
                    6 * u56 * v1 * v234 * v7 + 2 * u56 * v1234 * v7 +
                    2 * u12346 * v5 * v7 - 6 * u2346 * v1 * v5 * v7 -
                    6 * u1346 * v2 * v5 * v7 + 24 * u346 * v1 * v2 * v5 * v7 -
                    6 * u346 * v12 * v5 * v7 - 6 * u1246 * v3 * v5 * v7 +
                    24 * u246 * v1 * v3 * v5 * v7 +
                    24 * u146 * v2 * v3 * v5 * v7 -
                    120 * u46 * v1 * v2 * v3 * v5 * v7 +
                    24 * u46 * v12 * v3 * v5 * v7 - 6 * u246 * v13 * v5 * v7 +
                    24 * u46 * v2 * v13 * v5 * v7 - 6 * u146 * v23 * v5 * v7 +
                    24 * u46 * v1 * v23 * v5 * v7 - 6 * u46 * v123 * v5 * v7 -
                    6 * u1236 * v4 * v5 * v7 + 24 * u236 * v1 * v4 * v5 * v7 +
                    24 * u136 * v2 * v4 * v5 * v7 -
                    120 * u36 * v1 * v2 * v4 * v5 * v7 +
                    24 * u36 * v12 * v4 * v5 * v7 +
                    24 * u126 * v3 * v4 * v5 * v7 -
                    120 * u26 * v1 * v3 * v4 * v5 * v7 -
                    120 * u16 * v2 * v3 * v4 * v5 * v7 +
                    720 * u6 * v1 * v2 * v3 * v4 * v5 * v7 -
                    120 * u6 * v12 * v3 * v4 * v5 * v7 +
                    24 * u26 * v13 * v4 * v5 * v7 -
                    120 * u6 * v2 * v13 * v4 * v5 * v7 +
                    24 * u16 * v23 * v4 * v5 * v7 -
                    120 * u6 * v1 * v23 * v4 * v5 * v7 +
                    24 * u6 * v123 * v4 * v5 * v7 - 6 * u236 * v14 * v5 * v7 +
                    24 * u36 * v2 * v14 * v5 * v7 +
                    24 * u26 * v3 * v14 * v5 * v7 -
                    120 * u6 * v2 * v3 * v14 * v5 * v7 +
                    24 * u6 * v23 * v14 * v5 * v7 - 6 * u136 * v24 * v5 * v7 +
                    24 * u36 * v1 * v24 * v5 * v7 +
                    24 * u16 * v3 * v24 * v5 * v7 -
                    120 * u6 * v1 * v3 * v24 * v5 * v7 +
                    24 * u6 * v13 * v24 * v5 * v7 - 6 * u36 * v124 * v5 * v7 +
                    24 * u6 * v3 * v124 * v5 * v7 - 6 * u126 * v34 * v5 * v7 +
                    24 * u26 * v1 * v34 * v5 * v7 +
                    24 * u16 * v2 * v34 * v5 * v7 -
                    120 * u6 * v1 * v2 * v34 * v5 * v7 +
                    24 * u6 * v12 * v34 * v5 * v7 - 6 * u26 * v134 * v5 * v7 +
                    24 * u6 * v2 * v134 * v5 * v7 - 6 * u16 * v234 * v5 * v7 +
                    24 * u6 * v1 * v234 * v5 * v7 - 6 * u6 * v1234 * v5 * v7 +
                    2 * u2346 * v15 * v7 - 6 * u346 * v2 * v15 * v7 -
                    6 * u246 * v3 * v15 * v7 + 24 * u46 * v2 * v3 * v15 * v7 -
                    6 * u46 * v23 * v15 * v7 - 6 * u236 * v4 * v15 * v7 +
                    24 * u36 * v2 * v4 * v15 * v7 +
                    24 * u26 * v3 * v4 * v15 * v7 -
                    120 * u6 * v2 * v3 * v4 * v15 * v7 +
                    24 * u6 * v23 * v4 * v15 * v7 - 6 * u36 * v24 * v15 * v7 +
                    24 * u6 * v3 * v24 * v15 * v7 - 6 * u26 * v34 * v15 * v7 +
                    24 * u6 * v2 * v34 * v15 * v7 - 6 * u6 * v234 * v15 * v7 +
                    2 * u1346 * v25 * v7 - 6 * u346 * v1 * v25 * v7 -
                    6 * u146 * v3 * v25 * v7 + 24 * u46 * v1 * v3 * v25 * v7 -
                    6 * u46 * v13 * v25 * v7 - 6 * u136 * v4 * v25 * v7 +
                    24 * u36 * v1 * v4 * v25 * v7 +
                    24 * u16 * v3 * v4 * v25 * v7 -
                    120 * u6 * v1 * v3 * v4 * v25 * v7 +
                    24 * u6 * v13 * v4 * v25 * v7 - 6 * u36 * v14 * v25 * v7 +
                    24 * u6 * v3 * v14 * v25 * v7 - 6 * u16 * v34 * v25 * v7 +
                    24 * u6 * v1 * v34 * v25 * v7 - 6 * u6 * v134 * v25 * v7 +
                    2 * u346 * v125 * v7 - 6 * u46 * v3 * v125 * v7 -
                    6 * u36 * v4 * v125 * v7 + 24 * u6 * v3 * v4 * v125 * v7 -
                    6 * u6 * v34 * v125 * v7 + 2 * u1246 * v35 * v7 -
                    6 * u246 * v1 * v35 * v7 - 6 * u146 * v2 * v35 * v7 +
                    24 * u46 * v1 * v2 * v35 * v7 - 6 * u46 * v12 * v35 * v7 -
                    6 * u126 * v4 * v35 * v7 + 24 * u26 * v1 * v4 * v35 * v7 +
                    24 * u16 * v2 * v4 * v35 * v7 -
                    120 * u6 * v1 * v2 * v4 * v35 * v7 +
                    24 * u6 * v12 * v4 * v35 * v7 - 6 * u26 * v14 * v35 * v7 +
                    24 * u6 * v2 * v14 * v35 * v7 - 6 * u16 * v24 * v35 * v7 +
                    24 * u6 * v1 * v24 * v35 * v7 - 6 * u6 * v124 * v35 * v7 +
                    2 * u246 * v135 * v7 - 6 * u46 * v2 * v135 * v7 -
                    6 * u26 * v4 * v135 * v7 + 24 * u6 * v2 * v4 * v135 * v7 -
                    6 * u6 * v24 * v135 * v7 + 2 * u146 * v235 * v7 -
                    6 * u46 * v1 * v235 * v7 - 6 * u16 * v4 * v235 * v7 +
                    24 * u6 * v1 * v4 * v235 * v7 - 6 * u6 * v14 * v235 * v7 +
                    2 * u46 * v1235 * v7 - 6 * u6 * v4 * v1235 * v7 +
                    2 * u1236 * v45 * v7 - 6 * u236 * v1 * v45 * v7 -
                    6 * u136 * v2 * v45 * v7 + 24 * u36 * v1 * v2 * v45 * v7 -
                    6 * u36 * v12 * v45 * v7 - 6 * u126 * v3 * v45 * v7 +
                    24 * u26 * v1 * v3 * v45 * v7 +
                    24 * u16 * v2 * v3 * v45 * v7 -
                    120 * u6 * v1 * v2 * v3 * v45 * v7 +
                    24 * u6 * v12 * v3 * v45 * v7 - 6 * u26 * v13 * v45 * v7 +
                    24 * u6 * v2 * v13 * v45 * v7 - 6 * u16 * v23 * v45 * v7 +
                    24 * u6 * v1 * v23 * v45 * v7 - 6 * u6 * v123 * v45 * v7 +
                    2 * u236 * v145 * v7 - 6 * u36 * v2 * v145 * v7 -
                    6 * u26 * v3 * v145 * v7 + 24 * u6 * v2 * v3 * v145 * v7 -
                    6 * u6 * v23 * v145 * v7 + 2 * u136 * v245 * v7 -
                    6 * u36 * v1 * v245 * v7 - 6 * u16 * v3 * v245 * v7 +
                    24 * u6 * v1 * v3 * v245 * v7 - 6 * u6 * v13 * v245 * v7 +
                    2 * u36 * v1245 * v7 - 6 * u6 * v3 * v1245 * v7 +
                    2 * u126 * v345 * v7 - 6 * u26 * v1 * v345 * v7 -
                    6 * u16 * v2 * v345 * v7 + 24 * u6 * v1 * v2 * v345 * v7 -
                    6 * u6 * v12 * v345 * v7 + 2 * u26 * v1345 * v7 -
                    6 * u6 * v2 * v1345 * v7 + 2 * u16 * v2345 * v7 -
                    6 * u6 * v1 * v2345 * v7 + 2 * u6 * v12345 * v7 +
                    2 * u12345 * v6 * v7 - 6 * u2345 * v1 * v6 * v7 -
                    6 * u1345 * v2 * v6 * v7 + 24 * u345 * v1 * v2 * v6 * v7 -
                    6 * u345 * v12 * v6 * v7 - 6 * u1245 * v3 * v6 * v7 +
                    24 * u245 * v1 * v3 * v6 * v7 +
                    24 * u145 * v2 * v3 * v6 * v7 -
                    120 * u45 * v1 * v2 * v3 * v6 * v7 +
                    24 * u45 * v12 * v3 * v6 * v7 - 6 * u245 * v13 * v6 * v7 +
                    24 * u45 * v2 * v13 * v6 * v7 - 6 * u145 * v23 * v6 * v7 +
                    24 * u45 * v1 * v23 * v6 * v7 - 6 * u45 * v123 * v6 * v7 -
                    6 * u1235 * v4 * v6 * v7 + 24 * u235 * v1 * v4 * v6 * v7 +
                    24 * u135 * v2 * v4 * v6 * v7 -
                    120 * u35 * v1 * v2 * v4 * v6 * v7 +
                    24 * u35 * v12 * v4 * v6 * v7 +
                    24 * u125 * v3 * v4 * v6 * v7 -
                    120 * u25 * v1 * v3 * v4 * v6 * v7 -
                    120 * u15 * v2 * v3 * v4 * v6 * v7 +
                    720 * u5 * v1 * v2 * v3 * v4 * v6 * v7 -
                    120 * u5 * v12 * v3 * v4 * v6 * v7 +
                    24 * u25 * v13 * v4 * v6 * v7 -
                    120 * u5 * v2 * v13 * v4 * v6 * v7 +
                    24 * u15 * v23 * v4 * v6 * v7 -
                    120 * u5 * v1 * v23 * v4 * v6 * v7 +
                    24 * u5 * v123 * v4 * v6 * v7 - 6 * u235 * v14 * v6 * v7 +
                    24 * u35 * v2 * v14 * v6 * v7 +
                    24 * u25 * v3 * v14 * v6 * v7 -
                    120 * u5 * v2 * v3 * v14 * v6 * v7 +
                    24 * u5 * v23 * v14 * v6 * v7 - 6 * u135 * v24 * v6 * v7 +
                    24 * u35 * v1 * v24 * v6 * v7 +
                    24 * u15 * v3 * v24 * v6 * v7 -
                    120 * u5 * v1 * v3 * v24 * v6 * v7 +
                    24 * u5 * v13 * v24 * v6 * v7 - 6 * u35 * v124 * v6 * v7 +
                    24 * u5 * v3 * v124 * v6 * v7 - 6 * u125 * v34 * v6 * v7 +
                    24 * u25 * v1 * v34 * v6 * v7 +
                    24 * u15 * v2 * v34 * v6 * v7 -
                    120 * u5 * v1 * v2 * v34 * v6 * v7 +
                    24 * u5 * v12 * v34 * v6 * v7 - 6 * u25 * v134 * v6 * v7 +
                    24 * u5 * v2 * v134 * v6 * v7 - 6 * u15 * v234 * v6 * v7 +
                    24 * u5 * v1 * v234 * v6 * v7 - 6 * u5 * v1234 * v6 * v7 -
                    6 * u1234 * v5 * v6 * v7 + 24 * u234 * v1 * v5 * v6 * v7 +
                    24 * u134 * v2 * v5 * v6 * v7 -
                    120 * u34 * v1 * v2 * v5 * v6 * v7 +
                    24 * u34 * v12 * v5 * v6 * v7 +
                    24 * u124 * v3 * v5 * v6 * v7 -
                    120 * u24 * v1 * v3 * v5 * v6 * v7 -
                    120 * u14 * v2 * v3 * v5 * v6 * v7 +
                    720 * u4 * v1 * v2 * v3 * v5 * v6 * v7 -
                    120 * u4 * v12 * v3 * v5 * v6 * v7 +
                    24 * u24 * v13 * v5 * v6 * v7 -
                    120 * u4 * v2 * v13 * v5 * v6 * v7 +
                    24 * u14 * v23 * v5 * v6 * v7 -
                    120 * u4 * v1 * v23 * v5 * v6 * v7 +
                    24 * u4 * v123 * v5 * v6 * v7 +
                    24 * u123 * v4 * v5 * v6 * v7 -
                    120 * u23 * v1 * v4 * v5 * v6 * v7 -
                    120 * u13 * v2 * v4 * v5 * v6 * v7 +
                    720 * u3 * v1 * v2 * v4 * v5 * v6 * v7 -
                    120 * u3 * v12 * v4 * v5 * v6 * v7 -
                    120 * u12 * v3 * v4 * v5 * v6 * v7 +
                    720 * u2 * v1 * v3 * v4 * v5 * v6 * v7 +
                    720 * u1 * v2 * v3 * v4 * v5 * v6 * v7 -
                    5040 * u * v1 * v2 * v3 * v4 * v5 * v6 * v7 +
                    720 * u * v12 * v3 * v4 * v5 * v6 * v7 -
                    120 * u2 * v13 * v4 * v5 * v6 * v7 +
                    720 * u * v2 * v13 * v4 * v5 * v6 * v7 -
                    120 * u1 * v23 * v4 * v5 * v6 * v7 +
                    720 * u * v1 * v23 * v4 * v5 * v6 * v7 -
                    120 * u * v123 * v4 * v5 * v6 * v7 +
                    24 * u23 * v14 * v5 * v6 * v7 -
                    120 * u3 * v2 * v14 * v5 * v6 * v7 -
                    120 * u2 * v3 * v14 * v5 * v6 * v7 +
                    720 * u * v2 * v3 * v14 * v5 * v6 * v7 -
                    120 * u * v23 * v14 * v5 * v6 * v7 +
                    24 * u13 * v24 * v5 * v6 * v7 -
                    120 * u3 * v1 * v24 * v5 * v6 * v7 -
                    120 * u1 * v3 * v24 * v5 * v6 * v7 +
                    720 * u * v1 * v3 * v24 * v5 * v6 * v7 -
                    120 * u * v13 * v24 * v5 * v6 * v7 +
                    24 * u3 * v124 * v5 * v6 * v7 -
                    120 * u * v3 * v124 * v5 * v6 * v7 +
                    24 * u12 * v34 * v5 * v6 * v7 -
                    120 * u2 * v1 * v34 * v5 * v6 * v7 -
                    120 * u1 * v2 * v34 * v5 * v6 * v7 +
                    720 * u * v1 * v2 * v34 * v5 * v6 * v7 -
                    120 * u * v12 * v34 * v5 * v6 * v7 +
                    24 * u2 * v134 * v5 * v6 * v7 -
                    120 * u * v2 * v134 * v5 * v6 * v7 +
                    24 * u1 * v234 * v5 * v6 * v7 -
                    120 * u * v1 * v234 * v5 * v6 * v7 +
                    24 * u * v1234 * v5 * v6 * v7 - 6 * u234 * v15 * v6 * v7 +
                    24 * u34 * v2 * v15 * v6 * v7 +
                    24 * u24 * v3 * v15 * v6 * v7 -
                    120 * u4 * v2 * v3 * v15 * v6 * v7 +
                    24 * u4 * v23 * v15 * v6 * v7 +
                    24 * u23 * v4 * v15 * v6 * v7 -
                    120 * u3 * v2 * v4 * v15 * v6 * v7 -
                    120 * u2 * v3 * v4 * v15 * v6 * v7 +
                    720 * u * v2 * v3 * v4 * v15 * v6 * v7 -
                    120 * u * v23 * v4 * v15 * v6 * v7 +
                    24 * u3 * v24 * v15 * v6 * v7 -
                    120 * u * v3 * v24 * v15 * v6 * v7 +
                    24 * u2 * v34 * v15 * v6 * v7 -
                    120 * u * v2 * v34 * v15 * v6 * v7 +
                    24 * u * v234 * v15 * v6 * v7 - 6 * u134 * v25 * v6 * v7 +
                    24 * u34 * v1 * v25 * v6 * v7 +
                    24 * u14 * v3 * v25 * v6 * v7 -
                    120 * u4 * v1 * v3 * v25 * v6 * v7 +
                    24 * u4 * v13 * v25 * v6 * v7 +
                    24 * u13 * v4 * v25 * v6 * v7 -
                    120 * u3 * v1 * v4 * v25 * v6 * v7 -
                    120 * u1 * v3 * v4 * v25 * v6 * v7 +
                    720 * u * v1 * v3 * v4 * v25 * v6 * v7 -
                    120 * u * v13 * v4 * v25 * v6 * v7 +
                    24 * u3 * v14 * v25 * v6 * v7 -
                    120 * u * v3 * v14 * v25 * v6 * v7 +
                    24 * u1 * v34 * v25 * v6 * v7 -
                    120 * u * v1 * v34 * v25 * v6 * v7 +
                    24 * u * v134 * v25 * v6 * v7 - 6 * u34 * v125 * v6 * v7 +
                    24 * u4 * v3 * v125 * v6 * v7 +
                    24 * u3 * v4 * v125 * v6 * v7 -
                    120 * u * v3 * v4 * v125 * v6 * v7 +
                    24 * u * v34 * v125 * v6 * v7 - 6 * u124 * v35 * v6 * v7 +
                    24 * u24 * v1 * v35 * v6 * v7 +
                    24 * u14 * v2 * v35 * v6 * v7 -
                    120 * u4 * v1 * v2 * v35 * v6 * v7 +
                    24 * u4 * v12 * v35 * v6 * v7 +
                    24 * u12 * v4 * v35 * v6 * v7 -
                    120 * u2 * v1 * v4 * v35 * v6 * v7 -
                    120 * u1 * v2 * v4 * v35 * v6 * v7 +
                    720 * u * v1 * v2 * v4 * v35 * v6 * v7 -
                    120 * u * v12 * v4 * v35 * v6 * v7 +
                    24 * u2 * v14 * v35 * v6 * v7 -
                    120 * u * v2 * v14 * v35 * v6 * v7 +
                    24 * u1 * v24 * v35 * v6 * v7 -
                    120 * u * v1 * v24 * v35 * v6 * v7 +
                    24 * u * v124 * v35 * v6 * v7 - 6 * u24 * v135 * v6 * v7 +
                    24 * u4 * v2 * v135 * v6 * v7 +
                    24 * u2 * v4 * v135 * v6 * v7 -
                    120 * u * v2 * v4 * v135 * v6 * v7 +
                    24 * u * v24 * v135 * v6 * v7 - 6 * u14 * v235 * v6 * v7 +
                    24 * u4 * v1 * v235 * v6 * v7 +
                    24 * u1 * v4 * v235 * v6 * v7 -
                    120 * u * v1 * v4 * v235 * v6 * v7 +
                    24 * u * v14 * v235 * v6 * v7 - 6 * u4 * v1235 * v6 * v7 +
                    24 * u * v4 * v1235 * v6 * v7 - 6 * u123 * v45 * v6 * v7 +
                    24 * u23 * v1 * v45 * v6 * v7 +
                    24 * u13 * v2 * v45 * v6 * v7 -
                    120 * u3 * v1 * v2 * v45 * v6 * v7 +
                    24 * u3 * v12 * v45 * v6 * v7 +
                    24 * u12 * v3 * v45 * v6 * v7 -
                    120 * u2 * v1 * v3 * v45 * v6 * v7 -
                    120 * u1 * v2 * v3 * v45 * v6 * v7 +
                    720 * u * v1 * v2 * v3 * v45 * v6 * v7 -
                    120 * u * v12 * v3 * v45 * v6 * v7 +
                    24 * u2 * v13 * v45 * v6 * v7 -
                    120 * u * v2 * v13 * v45 * v6 * v7 +
                    24 * u1 * v23 * v45 * v6 * v7 -
                    120 * u * v1 * v23 * v45 * v6 * v7 +
                    24 * u * v123 * v45 * v6 * v7 - 6 * u23 * v145 * v6 * v7 +
                    24 * u3 * v2 * v145 * v6 * v7 +
                    24 * u2 * v3 * v145 * v6 * v7 -
                    120 * u * v2 * v3 * v145 * v6 * v7 +
                    24 * u * v23 * v145 * v6 * v7 - 6 * u13 * v245 * v6 * v7 +
                    24 * u3 * v1 * v245 * v6 * v7 +
                    24 * u1 * v3 * v245 * v6 * v7 -
                    120 * u * v1 * v3 * v245 * v6 * v7 +
                    24 * u * v13 * v245 * v6 * v7 - 6 * u3 * v1245 * v6 * v7 +
                    24 * u * v3 * v1245 * v6 * v7 - 6 * u12 * v345 * v6 * v7 +
                    24 * u2 * v1 * v345 * v6 * v7 +
                    24 * u1 * v2 * v345 * v6 * v7 -
                    120 * u * v1 * v2 * v345 * v6 * v7 +
                    24 * u * v12 * v345 * v6 * v7 - 6 * u2 * v1345 * v6 * v7 +
                    24 * u * v2 * v1345 * v6 * v7 - 6 * u1 * v2345 * v6 * v7 +
                    24 * u * v1 * v2345 * v6 * v7 - 6 * u * v12345 * v6 * v7 +
                    2 * u2345 * v16 * v7 - 6 * u345 * v2 * v16 * v7 -
                    6 * u245 * v3 * v16 * v7 + 24 * u45 * v2 * v3 * v16 * v7 -
                    6 * u45 * v23 * v16 * v7 - 6 * u235 * v4 * v16 * v7 +
                    24 * u35 * v2 * v4 * v16 * v7 +
                    24 * u25 * v3 * v4 * v16 * v7 -
                    120 * u5 * v2 * v3 * v4 * v16 * v7 +
                    24 * u5 * v23 * v4 * v16 * v7 - 6 * u35 * v24 * v16 * v7 +
                    24 * u5 * v3 * v24 * v16 * v7 - 6 * u25 * v34 * v16 * v7 +
                    24 * u5 * v2 * v34 * v16 * v7 - 6 * u5 * v234 * v16 * v7 -
                    6 * u234 * v5 * v16 * v7 + 24 * u34 * v2 * v5 * v16 * v7 +
                    24 * u24 * v3 * v5 * v16 * v7 -
                    120 * u4 * v2 * v3 * v5 * v16 * v7 +
                    24 * u4 * v23 * v5 * v16 * v7 +
                    24 * u23 * v4 * v5 * v16 * v7 -
                    120 * u3 * v2 * v4 * v5 * v16 * v7 -
                    120 * u2 * v3 * v4 * v5 * v16 * v7 +
                    720 * u * v2 * v3 * v4 * v5 * v16 * v7 -
                    120 * u * v23 * v4 * v5 * v16 * v7 +
                    24 * u3 * v24 * v5 * v16 * v7 -
                    120 * u * v3 * v24 * v5 * v16 * v7 +
                    24 * u2 * v34 * v5 * v16 * v7 -
                    120 * u * v2 * v34 * v5 * v16 * v7 +
                    24 * u * v234 * v5 * v16 * v7 - 6 * u34 * v25 * v16 * v7 +
                    24 * u4 * v3 * v25 * v16 * v7 +
                    24 * u3 * v4 * v25 * v16 * v7 -
                    120 * u * v3 * v4 * v25 * v16 * v7 +
                    24 * u * v34 * v25 * v16 * v7 - 6 * u24 * v35 * v16 * v7 +
                    24 * u4 * v2 * v35 * v16 * v7 +
                    24 * u2 * v4 * v35 * v16 * v7 -
                    120 * u * v2 * v4 * v35 * v16 * v7 +
                    24 * u * v24 * v35 * v16 * v7 - 6 * u4 * v235 * v16 * v7 +
                    24 * u * v4 * v235 * v16 * v7 - 6 * u23 * v45 * v16 * v7 +
                    24 * u3 * v2 * v45 * v16 * v7 +
                    24 * u2 * v3 * v45 * v16 * v7 -
                    120 * u * v2 * v3 * v45 * v16 * v7 +
                    24 * u * v23 * v45 * v16 * v7 - 6 * u3 * v245 * v16 * v7 +
                    24 * u * v3 * v245 * v16 * v7 - 6 * u2 * v345 * v16 * v7 +
                    24 * u * v2 * v345 * v16 * v7 - 6 * u * v2345 * v16 * v7 +
                    2 * u1345 * v26 * v7 - 6 * u345 * v1 * v26 * v7 -
                    6 * u145 * v3 * v26 * v7 + 24 * u45 * v1 * v3 * v26 * v7 -
                    6 * u45 * v13 * v26 * v7 - 6 * u135 * v4 * v26 * v7 +
                    24 * u35 * v1 * v4 * v26 * v7 +
                    24 * u15 * v3 * v4 * v26 * v7 -
                    120 * u5 * v1 * v3 * v4 * v26 * v7 +
                    24 * u5 * v13 * v4 * v26 * v7 - 6 * u35 * v14 * v26 * v7 +
                    24 * u5 * v3 * v14 * v26 * v7 - 6 * u15 * v34 * v26 * v7 +
                    24 * u5 * v1 * v34 * v26 * v7 - 6 * u5 * v134 * v26 * v7 -
                    6 * u134 * v5 * v26 * v7 + 24 * u34 * v1 * v5 * v26 * v7 +
                    24 * u14 * v3 * v5 * v26 * v7 -
                    120 * u4 * v1 * v3 * v5 * v26 * v7 +
                    24 * u4 * v13 * v5 * v26 * v7 +
                    24 * u13 * v4 * v5 * v26 * v7 -
                    120 * u3 * v1 * v4 * v5 * v26 * v7 -
                    120 * u1 * v3 * v4 * v5 * v26 * v7 +
                    720 * u * v1 * v3 * v4 * v5 * v26 * v7 -
                    120 * u * v13 * v4 * v5 * v26 * v7 +
                    24 * u3 * v14 * v5 * v26 * v7 -
                    120 * u * v3 * v14 * v5 * v26 * v7 +
                    24 * u1 * v34 * v5 * v26 * v7 -
                    120 * u * v1 * v34 * v5 * v26 * v7 +
                    24 * u * v134 * v5 * v26 * v7 - 6 * u34 * v15 * v26 * v7 +
                    24 * u4 * v3 * v15 * v26 * v7 +
                    24 * u3 * v4 * v15 * v26 * v7 -
                    120 * u * v3 * v4 * v15 * v26 * v7 +
                    24 * u * v34 * v15 * v26 * v7 - 6 * u14 * v35 * v26 * v7 +
                    24 * u4 * v1 * v35 * v26 * v7 +
                    24 * u1 * v4 * v35 * v26 * v7 -
                    120 * u * v1 * v4 * v35 * v26 * v7 +
                    24 * u * v14 * v35 * v26 * v7 - 6 * u4 * v135 * v26 * v7 +
                    24 * u * v4 * v135 * v26 * v7 - 6 * u13 * v45 * v26 * v7 +
                    24 * u3 * v1 * v45 * v26 * v7 +
                    24 * u1 * v3 * v45 * v26 * v7 -
                    120 * u * v1 * v3 * v45 * v26 * v7 +
                    24 * u * v13 * v45 * v26 * v7 - 6 * u3 * v145 * v26 * v7 +
                    24 * u * v3 * v145 * v26 * v7 - 6 * u1 * v345 * v26 * v7 +
                    24 * u * v1 * v345 * v26 * v7 - 6 * u * v1345 * v26 * v7 +
                    2 * u345 * v126 * v7 - 6 * u45 * v3 * v126 * v7 -
                    6 * u35 * v4 * v126 * v7 + 24 * u5 * v3 * v4 * v126 * v7 -
                    6 * u5 * v34 * v126 * v7 - 6 * u34 * v5 * v126 * v7 +
                    24 * u4 * v3 * v5 * v126 * v7 +
                    24 * u3 * v4 * v5 * v126 * v7 -
                    120 * u * v3 * v4 * v5 * v126 * v7 +
                    24 * u * v34 * v5 * v126 * v7 - 6 * u4 * v35 * v126 * v7 +
                    24 * u * v4 * v35 * v126 * v7 - 6 * u3 * v45 * v126 * v7 +
                    24 * u * v3 * v45 * v126 * v7 - 6 * u * v345 * v126 * v7 +
                    2 * u1245 * v36 * v7 - 6 * u245 * v1 * v36 * v7 -
                    6 * u145 * v2 * v36 * v7 + 24 * u45 * v1 * v2 * v36 * v7 -
                    6 * u45 * v12 * v36 * v7 - 6 * u125 * v4 * v36 * v7 +
                    24 * u25 * v1 * v4 * v36 * v7 +
                    24 * u15 * v2 * v4 * v36 * v7 -
                    120 * u5 * v1 * v2 * v4 * v36 * v7 +
                    24 * u5 * v12 * v4 * v36 * v7 - 6 * u25 * v14 * v36 * v7 +
                    24 * u5 * v2 * v14 * v36 * v7 - 6 * u15 * v24 * v36 * v7 +
                    24 * u5 * v1 * v24 * v36 * v7 - 6 * u5 * v124 * v36 * v7 -
                    6 * u124 * v5 * v36 * v7 + 24 * u24 * v1 * v5 * v36 * v7 +
                    24 * u14 * v2 * v5 * v36 * v7 -
                    120 * u4 * v1 * v2 * v5 * v36 * v7 +
                    24 * u4 * v12 * v5 * v36 * v7 +
                    24 * u12 * v4 * v5 * v36 * v7 -
                    120 * u2 * v1 * v4 * v5 * v36 * v7 -
                    120 * u1 * v2 * v4 * v5 * v36 * v7 +
                    720 * u * v1 * v2 * v4 * v5 * v36 * v7 -
                    120 * u * v12 * v4 * v5 * v36 * v7 +
                    24 * u2 * v14 * v5 * v36 * v7 -
                    120 * u * v2 * v14 * v5 * v36 * v7 +
                    24 * u1 * v24 * v5 * v36 * v7 -
                    120 * u * v1 * v24 * v5 * v36 * v7 +
                    24 * u * v124 * v5 * v36 * v7 - 6 * u24 * v15 * v36 * v7 +
                    24 * u4 * v2 * v15 * v36 * v7 +
                    24 * u2 * v4 * v15 * v36 * v7 -
                    120 * u * v2 * v4 * v15 * v36 * v7 +
                    24 * u * v24 * v15 * v36 * v7 - 6 * u14 * v25 * v36 * v7 +
                    24 * u4 * v1 * v25 * v36 * v7 +
                    24 * u1 * v4 * v25 * v36 * v7 -
                    120 * u * v1 * v4 * v25 * v36 * v7 +
                    24 * u * v14 * v25 * v36 * v7 - 6 * u4 * v125 * v36 * v7 +
                    24 * u * v4 * v125 * v36 * v7 - 6 * u12 * v45 * v36 * v7 +
                    24 * u2 * v1 * v45 * v36 * v7 +
                    24 * u1 * v2 * v45 * v36 * v7 -
                    120 * u * v1 * v2 * v45 * v36 * v7 +
                    24 * u * v12 * v45 * v36 * v7 - 6 * u2 * v145 * v36 * v7 +
                    24 * u * v2 * v145 * v36 * v7 - 6 * u1 * v245 * v36 * v7 +
                    24 * u * v1 * v245 * v36 * v7 - 6 * u * v1245 * v36 * v7 +
                    2 * u245 * v136 * v7 - 6 * u45 * v2 * v136 * v7 -
                    6 * u25 * v4 * v136 * v7 + 24 * u5 * v2 * v4 * v136 * v7 -
                    6 * u5 * v24 * v136 * v7 - 6 * u24 * v5 * v136 * v7 +
                    24 * u4 * v2 * v5 * v136 * v7 +
                    24 * u2 * v4 * v5 * v136 * v7 -
                    120 * u * v2 * v4 * v5 * v136 * v7 +
                    24 * u * v24 * v5 * v136 * v7 - 6 * u4 * v25 * v136 * v7 +
                    24 * u * v4 * v25 * v136 * v7 - 6 * u2 * v45 * v136 * v7 +
                    24 * u * v2 * v45 * v136 * v7 - 6 * u * v245 * v136 * v7 +
                    2 * u145 * v236 * v7 - 6 * u45 * v1 * v236 * v7 -
                    6 * u15 * v4 * v236 * v7 + 24 * u5 * v1 * v4 * v236 * v7 -
                    6 * u5 * v14 * v236 * v7 - 6 * u14 * v5 * v236 * v7 +
                    24 * u4 * v1 * v5 * v236 * v7 +
                    24 * u1 * v4 * v5 * v236 * v7 -
                    120 * u * v1 * v4 * v5 * v236 * v7 +
                    24 * u * v14 * v5 * v236 * v7 - 6 * u4 * v15 * v236 * v7 +
                    24 * u * v4 * v15 * v236 * v7 - 6 * u1 * v45 * v236 * v7 +
                    24 * u * v1 * v45 * v236 * v7 - 6 * u * v145 * v236 * v7 +
                    2 * u45 * v1236 * v7 - 6 * u5 * v4 * v1236 * v7 -
                    6 * u4 * v5 * v1236 * v7 + 24 * u * v4 * v5 * v1236 * v7 -
                    6 * u * v45 * v1236 * v7 + 2 * u1235 * v46 * v7 -
                    6 * u235 * v1 * v46 * v7 - 6 * u135 * v2 * v46 * v7 +
                    24 * u35 * v1 * v2 * v46 * v7 - 6 * u35 * v12 * v46 * v7 -
                    6 * u125 * v3 * v46 * v7 + 24 * u25 * v1 * v3 * v46 * v7 +
                    24 * u15 * v2 * v3 * v46 * v7 -
                    120 * u5 * v1 * v2 * v3 * v46 * v7 +
                    24 * u5 * v12 * v3 * v46 * v7 - 6 * u25 * v13 * v46 * v7 +
                    24 * u5 * v2 * v13 * v46 * v7 - 6 * u15 * v23 * v46 * v7 +
                    24 * u5 * v1 * v23 * v46 * v7 - 6 * u5 * v123 * v46 * v7 -
                    6 * u123 * v5 * v46 * v7 + 24 * u23 * v1 * v5 * v46 * v7 +
                    24 * u13 * v2 * v5 * v46 * v7 -
                    120 * u3 * v1 * v2 * v5 * v46 * v7 +
                    24 * u3 * v12 * v5 * v46 * v7 +
                    24 * u12 * v3 * v5 * v46 * v7 -
                    120 * u2 * v1 * v3 * v5 * v46 * v7 -
                    120 * u1 * v2 * v3 * v5 * v46 * v7 +
                    720 * u * v1 * v2 * v3 * v5 * v46 * v7 -
                    120 * u * v12 * v3 * v5 * v46 * v7 +
                    24 * u2 * v13 * v5 * v46 * v7 -
                    120 * u * v2 * v13 * v5 * v46 * v7 +
                    24 * u1 * v23 * v5 * v46 * v7 -
                    120 * u * v1 * v23 * v5 * v46 * v7 +
                    24 * u * v123 * v5 * v46 * v7 - 6 * u23 * v15 * v46 * v7 +
                    24 * u3 * v2 * v15 * v46 * v7 +
                    24 * u2 * v3 * v15 * v46 * v7 -
                    120 * u * v2 * v3 * v15 * v46 * v7 +
                    24 * u * v23 * v15 * v46 * v7 - 6 * u13 * v25 * v46 * v7 +
                    24 * u3 * v1 * v25 * v46 * v7 +
                    24 * u1 * v3 * v25 * v46 * v7 -
                    120 * u * v1 * v3 * v25 * v46 * v7 +
                    24 * u * v13 * v25 * v46 * v7 - 6 * u3 * v125 * v46 * v7 +
                    24 * u * v3 * v125 * v46 * v7 - 6 * u12 * v35 * v46 * v7 +
                    24 * u2 * v1 * v35 * v46 * v7 +
                    24 * u1 * v2 * v35 * v46 * v7 -
                    120 * u * v1 * v2 * v35 * v46 * v7 +
                    24 * u * v12 * v35 * v46 * v7 - 6 * u2 * v135 * v46 * v7 +
                    24 * u * v2 * v135 * v46 * v7 - 6 * u1 * v235 * v46 * v7 +
                    24 * u * v1 * v235 * v46 * v7 - 6 * u * v1235 * v46 * v7 +
                    2 * u235 * v146 * v7 - 6 * u35 * v2 * v146 * v7 -
                    6 * u25 * v3 * v146 * v7 + 24 * u5 * v2 * v3 * v146 * v7 -
                    6 * u5 * v23 * v146 * v7 - 6 * u23 * v5 * v146 * v7 +
                    24 * u3 * v2 * v5 * v146 * v7 +
                    24 * u2 * v3 * v5 * v146 * v7 -
                    120 * u * v2 * v3 * v5 * v146 * v7 +
                    24 * u * v23 * v5 * v146 * v7 - 6 * u3 * v25 * v146 * v7 +
                    24 * u * v3 * v25 * v146 * v7 - 6 * u2 * v35 * v146 * v7 +
                    24 * u * v2 * v35 * v146 * v7 - 6 * u * v235 * v146 * v7 +
                    2 * u135 * v246 * v7 - 6 * u35 * v1 * v246 * v7 -
                    6 * u15 * v3 * v246 * v7 + 24 * u5 * v1 * v3 * v246 * v7 -
                    6 * u5 * v13 * v246 * v7 - 6 * u13 * v5 * v246 * v7 +
                    24 * u3 * v1 * v5 * v246 * v7 +
                    24 * u1 * v3 * v5 * v246 * v7 -
                    120 * u * v1 * v3 * v5 * v246 * v7 +
                    24 * u * v13 * v5 * v246 * v7 - 6 * u3 * v15 * v246 * v7 +
                    24 * u * v3 * v15 * v246 * v7 - 6 * u1 * v35 * v246 * v7 +
                    24 * u * v1 * v35 * v246 * v7 - 6 * u * v135 * v246 * v7 +
                    2 * u35 * v1246 * v7 - 6 * u5 * v3 * v1246 * v7 -
                    6 * u3 * v5 * v1246 * v7 + 24 * u * v3 * v5 * v1246 * v7 -
                    6 * u * v35 * v1246 * v7 + 2 * u125 * v346 * v7 -
                    6 * u25 * v1 * v346 * v7 - 6 * u15 * v2 * v346 * v7 +
                    24 * u5 * v1 * v2 * v346 * v7 - 6 * u5 * v12 * v346 * v7 -
                    6 * u12 * v5 * v346 * v7 + 24 * u2 * v1 * v5 * v346 * v7 +
                    24 * u1 * v2 * v5 * v346 * v7 -
                    120 * u * v1 * v2 * v5 * v346 * v7 +
                    24 * u * v12 * v5 * v346 * v7 - 6 * u2 * v15 * v346 * v7 +
                    24 * u * v2 * v15 * v346 * v7 - 6 * u1 * v25 * v346 * v7 +
                    24 * u * v1 * v25 * v346 * v7 - 6 * u * v125 * v346 * v7 +
                    2 * u25 * v1346 * v7 - 6 * u5 * v2 * v1346 * v7 -
                    6 * u2 * v5 * v1346 * v7 + 24 * u * v2 * v5 * v1346 * v7 -
                    6 * u * v25 * v1346 * v7 + 2 * u15 * v2346 * v7 -
                    6 * u5 * v1 * v2346 * v7 - 6 * u1 * v5 * v2346 * v7 +
                    24 * u * v1 * v5 * v2346 * v7 - 6 * u * v15 * v2346 * v7 +
                    2 * u5 * v12346 * v7 - 6 * u * v5 * v12346 * v7 +
                    2 * u1234 * v56 * v7 - 6 * u234 * v1 * v56 * v7 -
                    6 * u134 * v2 * v56 * v7 + 24 * u34 * v1 * v2 * v56 * v7 -
                    6 * u34 * v12 * v56 * v7 - 6 * u124 * v3 * v56 * v7 +
                    24 * u24 * v1 * v3 * v56 * v7 +
                    24 * u14 * v2 * v3 * v56 * v7 -
                    120 * u4 * v1 * v2 * v3 * v56 * v7 +
                    24 * u4 * v12 * v3 * v56 * v7 - 6 * u24 * v13 * v56 * v7 +
                    24 * u4 * v2 * v13 * v56 * v7 - 6 * u14 * v23 * v56 * v7 +
                    24 * u4 * v1 * v23 * v56 * v7 - 6 * u4 * v123 * v56 * v7 -
                    6 * u123 * v4 * v56 * v7 + 24 * u23 * v1 * v4 * v56 * v7 +
                    24 * u13 * v2 * v4 * v56 * v7 -
                    120 * u3 * v1 * v2 * v4 * v56 * v7 +
                    24 * u3 * v12 * v4 * v56 * v7 +
                    24 * u12 * v3 * v4 * v56 * v7 -
                    120 * u2 * v1 * v3 * v4 * v56 * v7 -
                    120 * u1 * v2 * v3 * v4 * v56 * v7 +
                    720 * u * v1 * v2 * v3 * v4 * v56 * v7 -
                    120 * u * v12 * v3 * v4 * v56 * v7 +
                    24 * u2 * v13 * v4 * v56 * v7 -
                    120 * u * v2 * v13 * v4 * v56 * v7 +
                    24 * u1 * v23 * v4 * v56 * v7 -
                    120 * u * v1 * v23 * v4 * v56 * v7 +
                    24 * u * v123 * v4 * v56 * v7 - 6 * u23 * v14 * v56 * v7 +
                    24 * u3 * v2 * v14 * v56 * v7 +
                    24 * u2 * v3 * v14 * v56 * v7 -
                    120 * u * v2 * v3 * v14 * v56 * v7 +
                    24 * u * v23 * v14 * v56 * v7 - 6 * u13 * v24 * v56 * v7 +
                    24 * u3 * v1 * v24 * v56 * v7 +
                    24 * u1 * v3 * v24 * v56 * v7 -
                    120 * u * v1 * v3 * v24 * v56 * v7 +
                    24 * u * v13 * v24 * v56 * v7 - 6 * u3 * v124 * v56 * v7 +
                    24 * u * v3 * v124 * v56 * v7 - 6 * u12 * v34 * v56 * v7 +
                    24 * u2 * v1 * v34 * v56 * v7 +
                    24 * u1 * v2 * v34 * v56 * v7 -
                    120 * u * v1 * v2 * v34 * v56 * v7 +
                    24 * u * v12 * v34 * v56 * v7 - 6 * u2 * v134 * v56 * v7 +
                    24 * u * v2 * v134 * v56 * v7 - 6 * u1 * v234 * v56 * v7 +
                    24 * u * v1 * v234 * v56 * v7 - 6 * u * v1234 * v56 * v7 +
                    2 * u234 * v156 * v7 - 6 * u34 * v2 * v156 * v7 -
                    6 * u24 * v3 * v156 * v7 + 24 * u4 * v2 * v3 * v156 * v7 -
                    6 * u4 * v23 * v156 * v7 - 6 * u23 * v4 * v156 * v7 +
                    24 * u3 * v2 * v4 * v156 * v7 +
                    24 * u2 * v3 * v4 * v156 * v7 -
                    120 * u * v2 * v3 * v4 * v156 * v7 +
                    24 * u * v23 * v4 * v156 * v7 - 6 * u3 * v24 * v156 * v7 +
                    24 * u * v3 * v24 * v156 * v7 - 6 * u2 * v34 * v156 * v7 +
                    24 * u * v2 * v34 * v156 * v7 - 6 * u * v234 * v156 * v7 +
                    2 * u134 * v256 * v7 - 6 * u34 * v1 * v256 * v7 -
                    6 * u14 * v3 * v256 * v7 + 24 * u4 * v1 * v3 * v256 * v7 -
                    6 * u4 * v13 * v256 * v7 - 6 * u13 * v4 * v256 * v7 +
                    24 * u3 * v1 * v4 * v256 * v7 +
                    24 * u1 * v3 * v4 * v256 * v7 -
                    120 * u * v1 * v3 * v4 * v256 * v7 +
                    24 * u * v13 * v4 * v256 * v7 - 6 * u3 * v14 * v256 * v7 +
                    24 * u * v3 * v14 * v256 * v7 - 6 * u1 * v34 * v256 * v7 +
                    24 * u * v1 * v34 * v256 * v7 - 6 * u * v134 * v256 * v7 +
                    2 * u34 * v1256 * v7 - 6 * u4 * v3 * v1256 * v7 -
                    6 * u3 * v4 * v1256 * v7 + 24 * u * v3 * v4 * v1256 * v7 -
                    6 * u * v34 * v1256 * v7 + 2 * u124 * v356 * v7 -
                    6 * u24 * v1 * v356 * v7 - 6 * u14 * v2 * v356 * v7 +
                    24 * u4 * v1 * v2 * v356 * v7 - 6 * u4 * v12 * v356 * v7 -
                    6 * u12 * v4 * v356 * v7 + 24 * u2 * v1 * v4 * v356 * v7 +
                    24 * u1 * v2 * v4 * v356 * v7 -
                    120 * u * v1 * v2 * v4 * v356 * v7 +
                    24 * u * v12 * v4 * v356 * v7 - 6 * u2 * v14 * v356 * v7 +
                    24 * u * v2 * v14 * v356 * v7 - 6 * u1 * v24 * v356 * v7 +
                    24 * u * v1 * v24 * v356 * v7 - 6 * u * v124 * v356 * v7 +
                    2 * u24 * v1356 * v7 - 6 * u4 * v2 * v1356 * v7 -
                    6 * u2 * v4 * v1356 * v7 + 24 * u * v2 * v4 * v1356 * v7 -
                    6 * u * v24 * v1356 * v7 + 2 * u14 * v2356 * v7 -
                    6 * u4 * v1 * v2356 * v7 - 6 * u1 * v4 * v2356 * v7 +
                    24 * u * v1 * v4 * v2356 * v7 - 6 * u * v14 * v2356 * v7 +
                    2 * u4 * v12356 * v7 - 6 * u * v4 * v12356 * v7 +
                    2 * u123 * v456 * v7 - 6 * u23 * v1 * v456 * v7 -
                    6 * u13 * v2 * v456 * v7 + 24 * u3 * v1 * v2 * v456 * v7 -
                    6 * u3 * v12 * v456 * v7 - 6 * u12 * v3 * v456 * v7 +
                    24 * u2 * v1 * v3 * v456 * v7 +
                    24 * u1 * v2 * v3 * v456 * v7 -
                    120 * u * v1 * v2 * v3 * v456 * v7 +
                    24 * u * v12 * v3 * v456 * v7 - 6 * u2 * v13 * v456 * v7 +
                    24 * u * v2 * v13 * v456 * v7 - 6 * u1 * v23 * v456 * v7 +
                    24 * u * v1 * v23 * v456 * v7 - 6 * u * v123 * v456 * v7 +
                    2 * u23 * v1456 * v7 - 6 * u3 * v2 * v1456 * v7 -
                    6 * u2 * v3 * v1456 * v7 + 24 * u * v2 * v3 * v1456 * v7 -
                    6 * u * v23 * v1456 * v7 + 2 * u13 * v2456 * v7 -
                    6 * u3 * v1 * v2456 * v7 - 6 * u1 * v3 * v2456 * v7 +
                    24 * u * v1 * v3 * v2456 * v7 - 6 * u * v13 * v2456 * v7 +
                    2 * u3 * v12456 * v7 - 6 * u * v3 * v12456 * v7 +
                    2 * u12 * v3456 * v7 - 6 * u2 * v1 * v3456 * v7 -
                    6 * u1 * v2 * v3456 * v7 + 24 * u * v1 * v2 * v3456 * v7 -
                    6 * u * v12 * v3456 * v7 + 2 * u2 * v13456 * v7 -
                    6 * u * v2 * v13456 * v7 + 2 * u1 * v23456 * v7 -
                    6 * u * v1 * v23456 * v7 + 2 * u * v123456 * v7 -
                    u23456 * v17 + 2 * u3456 * v2 * v17 + 2 * u2456 * v3 * v17 -
                    6 * u456 * v2 * v3 * v17 + 2 * u456 * v23 * v17 +
                    2 * u2356 * v4 * v17 - 6 * u356 * v2 * v4 * v17 -
                    6 * u256 * v3 * v4 * v17 + 24 * u56 * v2 * v3 * v4 * v17 -
                    6 * u56 * v23 * v4 * v17 + 2 * u356 * v24 * v17 -
                    6 * u56 * v3 * v24 * v17 + 2 * u256 * v34 * v17 -
                    6 * u56 * v2 * v34 * v17 + 2 * u56 * v234 * v17 +
                    2 * u2346 * v5 * v17 - 6 * u346 * v2 * v5 * v17 -
                    6 * u246 * v3 * v5 * v17 + 24 * u46 * v2 * v3 * v5 * v17 -
                    6 * u46 * v23 * v5 * v17 - 6 * u236 * v4 * v5 * v17 +
                    24 * u36 * v2 * v4 * v5 * v17 +
                    24 * u26 * v3 * v4 * v5 * v17 -
                    120 * u6 * v2 * v3 * v4 * v5 * v17 +
                    24 * u6 * v23 * v4 * v5 * v17 - 6 * u36 * v24 * v5 * v17 +
                    24 * u6 * v3 * v24 * v5 * v17 - 6 * u26 * v34 * v5 * v17 +
                    24 * u6 * v2 * v34 * v5 * v17 - 6 * u6 * v234 * v5 * v17 +
                    2 * u346 * v25 * v17 - 6 * u46 * v3 * v25 * v17 -
                    6 * u36 * v4 * v25 * v17 + 24 * u6 * v3 * v4 * v25 * v17 -
                    6 * u6 * v34 * v25 * v17 + 2 * u246 * v35 * v17 -
                    6 * u46 * v2 * v35 * v17 - 6 * u26 * v4 * v35 * v17 +
                    24 * u6 * v2 * v4 * v35 * v17 - 6 * u6 * v24 * v35 * v17 +
                    2 * u46 * v235 * v17 - 6 * u6 * v4 * v235 * v17 +
                    2 * u236 * v45 * v17 - 6 * u36 * v2 * v45 * v17 -
                    6 * u26 * v3 * v45 * v17 + 24 * u6 * v2 * v3 * v45 * v17 -
                    6 * u6 * v23 * v45 * v17 + 2 * u36 * v245 * v17 -
                    6 * u6 * v3 * v245 * v17 + 2 * u26 * v345 * v17 -
                    6 * u6 * v2 * v345 * v17 + 2 * u6 * v2345 * v17 +
                    2 * u2345 * v6 * v17 - 6 * u345 * v2 * v6 * v17 -
                    6 * u245 * v3 * v6 * v17 + 24 * u45 * v2 * v3 * v6 * v17 -
                    6 * u45 * v23 * v6 * v17 - 6 * u235 * v4 * v6 * v17 +
                    24 * u35 * v2 * v4 * v6 * v17 +
                    24 * u25 * v3 * v4 * v6 * v17 -
                    120 * u5 * v2 * v3 * v4 * v6 * v17 +
                    24 * u5 * v23 * v4 * v6 * v17 - 6 * u35 * v24 * v6 * v17 +
                    24 * u5 * v3 * v24 * v6 * v17 - 6 * u25 * v34 * v6 * v17 +
                    24 * u5 * v2 * v34 * v6 * v17 - 6 * u5 * v234 * v6 * v17 -
                    6 * u234 * v5 * v6 * v17 + 24 * u34 * v2 * v5 * v6 * v17 +
                    24 * u24 * v3 * v5 * v6 * v17 -
                    120 * u4 * v2 * v3 * v5 * v6 * v17 +
                    24 * u4 * v23 * v5 * v6 * v17 +
                    24 * u23 * v4 * v5 * v6 * v17 -
                    120 * u3 * v2 * v4 * v5 * v6 * v17 -
                    120 * u2 * v3 * v4 * v5 * v6 * v17 +
                    720 * u * v2 * v3 * v4 * v5 * v6 * v17 -
                    120 * u * v23 * v4 * v5 * v6 * v17 +
                    24 * u3 * v24 * v5 * v6 * v17 -
                    120 * u * v3 * v24 * v5 * v6 * v17 +
                    24 * u2 * v34 * v5 * v6 * v17 -
                    120 * u * v2 * v34 * v5 * v6 * v17 +
                    24 * u * v234 * v5 * v6 * v17 - 6 * u34 * v25 * v6 * v17 +
                    24 * u4 * v3 * v25 * v6 * v17 +
                    24 * u3 * v4 * v25 * v6 * v17 -
                    120 * u * v3 * v4 * v25 * v6 * v17 +
                    24 * u * v34 * v25 * v6 * v17 - 6 * u24 * v35 * v6 * v17 +
                    24 * u4 * v2 * v35 * v6 * v17 +
                    24 * u2 * v4 * v35 * v6 * v17 -
                    120 * u * v2 * v4 * v35 * v6 * v17 +
                    24 * u * v24 * v35 * v6 * v17 - 6 * u4 * v235 * v6 * v17 +
                    24 * u * v4 * v235 * v6 * v17 - 6 * u23 * v45 * v6 * v17 +
                    24 * u3 * v2 * v45 * v6 * v17 +
                    24 * u2 * v3 * v45 * v6 * v17 -
                    120 * u * v2 * v3 * v45 * v6 * v17 +
                    24 * u * v23 * v45 * v6 * v17 - 6 * u3 * v245 * v6 * v17 +
                    24 * u * v3 * v245 * v6 * v17 - 6 * u2 * v345 * v6 * v17 +
                    24 * u * v2 * v345 * v6 * v17 - 6 * u * v2345 * v6 * v17 +
                    2 * u345 * v26 * v17 - 6 * u45 * v3 * v26 * v17 -
                    6 * u35 * v4 * v26 * v17 + 24 * u5 * v3 * v4 * v26 * v17 -
                    6 * u5 * v34 * v26 * v17 - 6 * u34 * v5 * v26 * v17 +
                    24 * u4 * v3 * v5 * v26 * v17 +
                    24 * u3 * v4 * v5 * v26 * v17 -
                    120 * u * v3 * v4 * v5 * v26 * v17 +
                    24 * u * v34 * v5 * v26 * v17 - 6 * u4 * v35 * v26 * v17 +
                    24 * u * v4 * v35 * v26 * v17 - 6 * u3 * v45 * v26 * v17 +
                    24 * u * v3 * v45 * v26 * v17 - 6 * u * v345 * v26 * v17 +
                    2 * u245 * v36 * v17 - 6 * u45 * v2 * v36 * v17 -
                    6 * u25 * v4 * v36 * v17 + 24 * u5 * v2 * v4 * v36 * v17 -
                    6 * u5 * v24 * v36 * v17 - 6 * u24 * v5 * v36 * v17 +
                    24 * u4 * v2 * v5 * v36 * v17 +
                    24 * u2 * v4 * v5 * v36 * v17 -
                    120 * u * v2 * v4 * v5 * v36 * v17 +
                    24 * u * v24 * v5 * v36 * v17 - 6 * u4 * v25 * v36 * v17 +
                    24 * u * v4 * v25 * v36 * v17 - 6 * u2 * v45 * v36 * v17 +
                    24 * u * v2 * v45 * v36 * v17 - 6 * u * v245 * v36 * v17 +
                    2 * u45 * v236 * v17 - 6 * u5 * v4 * v236 * v17 -
                    6 * u4 * v5 * v236 * v17 + 24 * u * v4 * v5 * v236 * v17 -
                    6 * u * v45 * v236 * v17 + 2 * u235 * v46 * v17 -
                    6 * u35 * v2 * v46 * v17 - 6 * u25 * v3 * v46 * v17 +
                    24 * u5 * v2 * v3 * v46 * v17 - 6 * u5 * v23 * v46 * v17 -
                    6 * u23 * v5 * v46 * v17 + 24 * u3 * v2 * v5 * v46 * v17 +
                    24 * u2 * v3 * v5 * v46 * v17 -
                    120 * u * v2 * v3 * v5 * v46 * v17 +
                    24 * u * v23 * v5 * v46 * v17 - 6 * u3 * v25 * v46 * v17 +
                    24 * u * v3 * v25 * v46 * v17 - 6 * u2 * v35 * v46 * v17 +
                    24 * u * v2 * v35 * v46 * v17 - 6 * u * v235 * v46 * v17 +
                    2 * u35 * v246 * v17 - 6 * u5 * v3 * v246 * v17 -
                    6 * u3 * v5 * v246 * v17 + 24 * u * v3 * v5 * v246 * v17 -
                    6 * u * v35 * v246 * v17 + 2 * u25 * v346 * v17 -
                    6 * u5 * v2 * v346 * v17 - 6 * u2 * v5 * v346 * v17 +
                    24 * u * v2 * v5 * v346 * v17 - 6 * u * v25 * v346 * v17 +
                    2 * u5 * v2346 * v17 - 6 * u * v5 * v2346 * v17 +
                    2 * u234 * v56 * v17 - 6 * u34 * v2 * v56 * v17 -
                    6 * u24 * v3 * v56 * v17 + 24 * u4 * v2 * v3 * v56 * v17 -
                    6 * u4 * v23 * v56 * v17 - 6 * u23 * v4 * v56 * v17 +
                    24 * u3 * v2 * v4 * v56 * v17 +
                    24 * u2 * v3 * v4 * v56 * v17 -
                    120 * u * v2 * v3 * v4 * v56 * v17 +
                    24 * u * v23 * v4 * v56 * v17 - 6 * u3 * v24 * v56 * v17 +
                    24 * u * v3 * v24 * v56 * v17 - 6 * u2 * v34 * v56 * v17 +
                    24 * u * v2 * v34 * v56 * v17 - 6 * u * v234 * v56 * v17 +
                    2 * u34 * v256 * v17 - 6 * u4 * v3 * v256 * v17 -
                    6 * u3 * v4 * v256 * v17 + 24 * u * v3 * v4 * v256 * v17 -
                    6 * u * v34 * v256 * v17 + 2 * u24 * v356 * v17 -
                    6 * u4 * v2 * v356 * v17 - 6 * u2 * v4 * v356 * v17 +
                    24 * u * v2 * v4 * v356 * v17 - 6 * u * v24 * v356 * v17 +
                    2 * u4 * v2356 * v17 - 6 * u * v4 * v2356 * v17 +
                    2 * u23 * v456 * v17 - 6 * u3 * v2 * v456 * v17 -
                    6 * u2 * v3 * v456 * v17 + 24 * u * v2 * v3 * v456 * v17 -
                    6 * u * v23 * v456 * v17 + 2 * u3 * v2456 * v17 -
                    6 * u * v3 * v2456 * v17 + 2 * u2 * v3456 * v17 -
                    6 * u * v2 * v3456 * v17 + 2 * u * v23456 * v17 -
                    u13456 * v27 + 2 * u3456 * v1 * v27 + 2 * u1456 * v3 * v27 -
                    6 * u456 * v1 * v3 * v27 + 2 * u456 * v13 * v27 +
                    2 * u1356 * v4 * v27 - 6 * u356 * v1 * v4 * v27 -
                    6 * u156 * v3 * v4 * v27 + 24 * u56 * v1 * v3 * v4 * v27 -
                    6 * u56 * v13 * v4 * v27 + 2 * u356 * v14 * v27 -
                    6 * u56 * v3 * v14 * v27 + 2 * u156 * v34 * v27 -
                    6 * u56 * v1 * v34 * v27 + 2 * u56 * v134 * v27 +
                    2 * u1346 * v5 * v27 - 6 * u346 * v1 * v5 * v27 -
                    6 * u146 * v3 * v5 * v27 + 24 * u46 * v1 * v3 * v5 * v27 -
                    6 * u46 * v13 * v5 * v27 - 6 * u136 * v4 * v5 * v27 +
                    24 * u36 * v1 * v4 * v5 * v27 +
                    24 * u16 * v3 * v4 * v5 * v27 -
                    120 * u6 * v1 * v3 * v4 * v5 * v27 +
                    24 * u6 * v13 * v4 * v5 * v27 - 6 * u36 * v14 * v5 * v27 +
                    24 * u6 * v3 * v14 * v5 * v27 - 6 * u16 * v34 * v5 * v27 +
                    24 * u6 * v1 * v34 * v5 * v27 - 6 * u6 * v134 * v5 * v27 +
                    2 * u346 * v15 * v27 - 6 * u46 * v3 * v15 * v27 -
                    6 * u36 * v4 * v15 * v27 + 24 * u6 * v3 * v4 * v15 * v27 -
                    6 * u6 * v34 * v15 * v27 + 2 * u146 * v35 * v27 -
                    6 * u46 * v1 * v35 * v27 - 6 * u16 * v4 * v35 * v27 +
                    24 * u6 * v1 * v4 * v35 * v27 - 6 * u6 * v14 * v35 * v27 +
                    2 * u46 * v135 * v27 - 6 * u6 * v4 * v135 * v27 +
                    2 * u136 * v45 * v27 - 6 * u36 * v1 * v45 * v27 -
                    6 * u16 * v3 * v45 * v27 + 24 * u6 * v1 * v3 * v45 * v27 -
                    6 * u6 * v13 * v45 * v27 + 2 * u36 * v145 * v27 -
                    6 * u6 * v3 * v145 * v27 + 2 * u16 * v345 * v27 -
                    6 * u6 * v1 * v345 * v27 + 2 * u6 * v1345 * v27 +
                    2 * u1345 * v6 * v27 - 6 * u345 * v1 * v6 * v27 -
                    6 * u145 * v3 * v6 * v27 + 24 * u45 * v1 * v3 * v6 * v27 -
                    6 * u45 * v13 * v6 * v27 - 6 * u135 * v4 * v6 * v27 +
                    24 * u35 * v1 * v4 * v6 * v27 +
                    24 * u15 * v3 * v4 * v6 * v27 -
                    120 * u5 * v1 * v3 * v4 * v6 * v27 +
                    24 * u5 * v13 * v4 * v6 * v27 - 6 * u35 * v14 * v6 * v27 +
                    24 * u5 * v3 * v14 * v6 * v27 - 6 * u15 * v34 * v6 * v27 +
                    24 * u5 * v1 * v34 * v6 * v27 - 6 * u5 * v134 * v6 * v27 -
                    6 * u134 * v5 * v6 * v27 + 24 * u34 * v1 * v5 * v6 * v27 +
                    24 * u14 * v3 * v5 * v6 * v27 -
                    120 * u4 * v1 * v3 * v5 * v6 * v27 +
                    24 * u4 * v13 * v5 * v6 * v27 +
                    24 * u13 * v4 * v5 * v6 * v27 -
                    120 * u3 * v1 * v4 * v5 * v6 * v27 -
                    120 * u1 * v3 * v4 * v5 * v6 * v27 +
                    720 * u * v1 * v3 * v4 * v5 * v6 * v27 -
                    120 * u * v13 * v4 * v5 * v6 * v27 +
                    24 * u3 * v14 * v5 * v6 * v27 -
                    120 * u * v3 * v14 * v5 * v6 * v27 +
                    24 * u1 * v34 * v5 * v6 * v27 -
                    120 * u * v1 * v34 * v5 * v6 * v27 +
                    24 * u * v134 * v5 * v6 * v27 - 6 * u34 * v15 * v6 * v27 +
                    24 * u4 * v3 * v15 * v6 * v27 +
                    24 * u3 * v4 * v15 * v6 * v27 -
                    120 * u * v3 * v4 * v15 * v6 * v27 +
                    24 * u * v34 * v15 * v6 * v27 - 6 * u14 * v35 * v6 * v27 +
                    24 * u4 * v1 * v35 * v6 * v27 +
                    24 * u1 * v4 * v35 * v6 * v27 -
                    120 * u * v1 * v4 * v35 * v6 * v27 +
                    24 * u * v14 * v35 * v6 * v27 - 6 * u4 * v135 * v6 * v27 +
                    24 * u * v4 * v135 * v6 * v27 - 6 * u13 * v45 * v6 * v27 +
                    24 * u3 * v1 * v45 * v6 * v27 +
                    24 * u1 * v3 * v45 * v6 * v27 -
                    120 * u * v1 * v3 * v45 * v6 * v27 +
                    24 * u * v13 * v45 * v6 * v27 - 6 * u3 * v145 * v6 * v27 +
                    24 * u * v3 * v145 * v6 * v27 - 6 * u1 * v345 * v6 * v27 +
                    24 * u * v1 * v345 * v6 * v27 - 6 * u * v1345 * v6 * v27 +
                    2 * u345 * v16 * v27 - 6 * u45 * v3 * v16 * v27 -
                    6 * u35 * v4 * v16 * v27 + 24 * u5 * v3 * v4 * v16 * v27 -
                    6 * u5 * v34 * v16 * v27 - 6 * u34 * v5 * v16 * v27 +
                    24 * u4 * v3 * v5 * v16 * v27 +
                    24 * u3 * v4 * v5 * v16 * v27 -
                    120 * u * v3 * v4 * v5 * v16 * v27 +
                    24 * u * v34 * v5 * v16 * v27 - 6 * u4 * v35 * v16 * v27 +
                    24 * u * v4 * v35 * v16 * v27 - 6 * u3 * v45 * v16 * v27 +
                    24 * u * v3 * v45 * v16 * v27 - 6 * u * v345 * v16 * v27 +
                    2 * u145 * v36 * v27 - 6 * u45 * v1 * v36 * v27 -
                    6 * u15 * v4 * v36 * v27 + 24 * u5 * v1 * v4 * v36 * v27 -
                    6 * u5 * v14 * v36 * v27 - 6 * u14 * v5 * v36 * v27 +
                    24 * u4 * v1 * v5 * v36 * v27 +
                    24 * u1 * v4 * v5 * v36 * v27 -
                    120 * u * v1 * v4 * v5 * v36 * v27 +
                    24 * u * v14 * v5 * v36 * v27 - 6 * u4 * v15 * v36 * v27 +
                    24 * u * v4 * v15 * v36 * v27 - 6 * u1 * v45 * v36 * v27 +
                    24 * u * v1 * v45 * v36 * v27 - 6 * u * v145 * v36 * v27 +
                    2 * u45 * v136 * v27 - 6 * u5 * v4 * v136 * v27 -
                    6 * u4 * v5 * v136 * v27 + 24 * u * v4 * v5 * v136 * v27 -
                    6 * u * v45 * v136 * v27 + 2 * u135 * v46 * v27 -
                    6 * u35 * v1 * v46 * v27 - 6 * u15 * v3 * v46 * v27 +
                    24 * u5 * v1 * v3 * v46 * v27 - 6 * u5 * v13 * v46 * v27 -
                    6 * u13 * v5 * v46 * v27 + 24 * u3 * v1 * v5 * v46 * v27 +
                    24 * u1 * v3 * v5 * v46 * v27 -
                    120 * u * v1 * v3 * v5 * v46 * v27 +
                    24 * u * v13 * v5 * v46 * v27 - 6 * u3 * v15 * v46 * v27 +
                    24 * u * v3 * v15 * v46 * v27 - 6 * u1 * v35 * v46 * v27 +
                    24 * u * v1 * v35 * v46 * v27 - 6 * u * v135 * v46 * v27 +
                    2 * u35 * v146 * v27 - 6 * u5 * v3 * v146 * v27 -
                    6 * u3 * v5 * v146 * v27 + 24 * u * v3 * v5 * v146 * v27 -
                    6 * u * v35 * v146 * v27 + 2 * u15 * v346 * v27 -
                    6 * u5 * v1 * v346 * v27 - 6 * u1 * v5 * v346 * v27 +
                    24 * u * v1 * v5 * v346 * v27 - 6 * u * v15 * v346 * v27 +
                    2 * u5 * v1346 * v27 - 6 * u * v5 * v1346 * v27 +
                    2 * u134 * v56 * v27 - 6 * u34 * v1 * v56 * v27 -
                    6 * u14 * v3 * v56 * v27 + 24 * u4 * v1 * v3 * v56 * v27 -
                    6 * u4 * v13 * v56 * v27 - 6 * u13 * v4 * v56 * v27 +
                    24 * u3 * v1 * v4 * v56 * v27 +
                    24 * u1 * v3 * v4 * v56 * v27 -
                    120 * u * v1 * v3 * v4 * v56 * v27 +
                    24 * u * v13 * v4 * v56 * v27 - 6 * u3 * v14 * v56 * v27 +
                    24 * u * v3 * v14 * v56 * v27 - 6 * u1 * v34 * v56 * v27 +
                    24 * u * v1 * v34 * v56 * v27 - 6 * u * v134 * v56 * v27 +
                    2 * u34 * v156 * v27 - 6 * u4 * v3 * v156 * v27 -
                    6 * u3 * v4 * v156 * v27 + 24 * u * v3 * v4 * v156 * v27 -
                    6 * u * v34 * v156 * v27 + 2 * u14 * v356 * v27 -
                    6 * u4 * v1 * v356 * v27 - 6 * u1 * v4 * v356 * v27 +
                    24 * u * v1 * v4 * v356 * v27 - 6 * u * v14 * v356 * v27 +
                    2 * u4 * v1356 * v27 - 6 * u * v4 * v1356 * v27 +
                    2 * u13 * v456 * v27 - 6 * u3 * v1 * v456 * v27 -
                    6 * u1 * v3 * v456 * v27 + 24 * u * v1 * v3 * v456 * v27 -
                    6 * u * v13 * v456 * v27 + 2 * u3 * v1456 * v27 -
                    6 * u * v3 * v1456 * v27 + 2 * u1 * v3456 * v27 -
                    6 * u * v1 * v3456 * v27 + 2 * u * v13456 * v27 -
                    u3456 * v127 + 2 * u456 * v3 * v127 + 2 * u356 * v4 * v127 -
                    6 * u56 * v3 * v4 * v127 + 2 * u56 * v34 * v127 +
                    2 * u346 * v5 * v127 - 6 * u46 * v3 * v5 * v127 -
                    6 * u36 * v4 * v5 * v127 + 24 * u6 * v3 * v4 * v5 * v127 -
                    6 * u6 * v34 * v5 * v127 + 2 * u46 * v35 * v127 -
                    6 * u6 * v4 * v35 * v127 + 2 * u36 * v45 * v127 -
                    6 * u6 * v3 * v45 * v127 + 2 * u6 * v345 * v127 +
                    2 * u345 * v6 * v127 - 6 * u45 * v3 * v6 * v127 -
                    6 * u35 * v4 * v6 * v127 + 24 * u5 * v3 * v4 * v6 * v127 -
                    6 * u5 * v34 * v6 * v127 - 6 * u34 * v5 * v6 * v127 +
                    24 * u4 * v3 * v5 * v6 * v127 +
                    24 * u3 * v4 * v5 * v6 * v127 -
                    120 * u * v3 * v4 * v5 * v6 * v127 +
                    24 * u * v34 * v5 * v6 * v127 - 6 * u4 * v35 * v6 * v127 +
                    24 * u * v4 * v35 * v6 * v127 - 6 * u3 * v45 * v6 * v127 +
                    24 * u * v3 * v45 * v6 * v127 - 6 * u * v345 * v6 * v127 +
                    2 * u45 * v36 * v127 - 6 * u5 * v4 * v36 * v127 -
                    6 * u4 * v5 * v36 * v127 + 24 * u * v4 * v5 * v36 * v127 -
                    6 * u * v45 * v36 * v127 + 2 * u35 * v46 * v127 -
                    6 * u5 * v3 * v46 * v127 - 6 * u3 * v5 * v46 * v127 +
                    24 * u * v3 * v5 * v46 * v127 - 6 * u * v35 * v46 * v127 +
                    2 * u5 * v346 * v127 - 6 * u * v5 * v346 * v127 +
                    2 * u34 * v56 * v127 - 6 * u4 * v3 * v56 * v127 -
                    6 * u3 * v4 * v56 * v127 + 24 * u * v3 * v4 * v56 * v127 -
                    6 * u * v34 * v56 * v127 + 2 * u4 * v356 * v127 -
                    6 * u * v4 * v356 * v127 + 2 * u3 * v456 * v127 -
                    6 * u * v3 * v456 * v127 + 2 * u * v3456 * v127 -
                    u12456 * v37 + 2 * u2456 * v1 * v37 + 2 * u1456 * v2 * v37 -
                    6 * u456 * v1 * v2 * v37 + 2 * u456 * v12 * v37 +
                    2 * u1256 * v4 * v37 - 6 * u256 * v1 * v4 * v37 -
                    6 * u156 * v2 * v4 * v37 + 24 * u56 * v1 * v2 * v4 * v37 -
                    6 * u56 * v12 * v4 * v37 + 2 * u256 * v14 * v37 -
                    6 * u56 * v2 * v14 * v37 + 2 * u156 * v24 * v37 -
                    6 * u56 * v1 * v24 * v37 + 2 * u56 * v124 * v37 +
                    2 * u1246 * v5 * v37 - 6 * u246 * v1 * v5 * v37 -
                    6 * u146 * v2 * v5 * v37 + 24 * u46 * v1 * v2 * v5 * v37 -
                    6 * u46 * v12 * v5 * v37 - 6 * u126 * v4 * v5 * v37 +
                    24 * u26 * v1 * v4 * v5 * v37 +
                    24 * u16 * v2 * v4 * v5 * v37 -
                    120 * u6 * v1 * v2 * v4 * v5 * v37 +
                    24 * u6 * v12 * v4 * v5 * v37 - 6 * u26 * v14 * v5 * v37 +
                    24 * u6 * v2 * v14 * v5 * v37 - 6 * u16 * v24 * v5 * v37 +
                    24 * u6 * v1 * v24 * v5 * v37 - 6 * u6 * v124 * v5 * v37 +
                    2 * u246 * v15 * v37 - 6 * u46 * v2 * v15 * v37 -
                    6 * u26 * v4 * v15 * v37 + 24 * u6 * v2 * v4 * v15 * v37 -
                    6 * u6 * v24 * v15 * v37 + 2 * u146 * v25 * v37 -
                    6 * u46 * v1 * v25 * v37 - 6 * u16 * v4 * v25 * v37 +
                    24 * u6 * v1 * v4 * v25 * v37 - 6 * u6 * v14 * v25 * v37 +
                    2 * u46 * v125 * v37 - 6 * u6 * v4 * v125 * v37 +
                    2 * u126 * v45 * v37 - 6 * u26 * v1 * v45 * v37 -
                    6 * u16 * v2 * v45 * v37 + 24 * u6 * v1 * v2 * v45 * v37 -
                    6 * u6 * v12 * v45 * v37 + 2 * u26 * v145 * v37 -
                    6 * u6 * v2 * v145 * v37 + 2 * u16 * v245 * v37 -
                    6 * u6 * v1 * v245 * v37 + 2 * u6 * v1245 * v37 +
                    2 * u1245 * v6 * v37 - 6 * u245 * v1 * v6 * v37 -
                    6 * u145 * v2 * v6 * v37 + 24 * u45 * v1 * v2 * v6 * v37 -
                    6 * u45 * v12 * v6 * v37 - 6 * u125 * v4 * v6 * v37 +
                    24 * u25 * v1 * v4 * v6 * v37 +
                    24 * u15 * v2 * v4 * v6 * v37 -
                    120 * u5 * v1 * v2 * v4 * v6 * v37 +
                    24 * u5 * v12 * v4 * v6 * v37 - 6 * u25 * v14 * v6 * v37 +
                    24 * u5 * v2 * v14 * v6 * v37 - 6 * u15 * v24 * v6 * v37 +
                    24 * u5 * v1 * v24 * v6 * v37 - 6 * u5 * v124 * v6 * v37 -
                    6 * u124 * v5 * v6 * v37 + 24 * u24 * v1 * v5 * v6 * v37 +
                    24 * u14 * v2 * v5 * v6 * v37 -
                    120 * u4 * v1 * v2 * v5 * v6 * v37 +
                    24 * u4 * v12 * v5 * v6 * v37 +
                    24 * u12 * v4 * v5 * v6 * v37 -
                    120 * u2 * v1 * v4 * v5 * v6 * v37 -
                    120 * u1 * v2 * v4 * v5 * v6 * v37 +
                    720 * u * v1 * v2 * v4 * v5 * v6 * v37 -
                    120 * u * v12 * v4 * v5 * v6 * v37 +
                    24 * u2 * v14 * v5 * v6 * v37 -
                    120 * u * v2 * v14 * v5 * v6 * v37 +
                    24 * u1 * v24 * v5 * v6 * v37 -
                    120 * u * v1 * v24 * v5 * v6 * v37 +
                    24 * u * v124 * v5 * v6 * v37 - 6 * u24 * v15 * v6 * v37 +
                    24 * u4 * v2 * v15 * v6 * v37 +
                    24 * u2 * v4 * v15 * v6 * v37 -
                    120 * u * v2 * v4 * v15 * v6 * v37 +
                    24 * u * v24 * v15 * v6 * v37 - 6 * u14 * v25 * v6 * v37 +
                    24 * u4 * v1 * v25 * v6 * v37 +
                    24 * u1 * v4 * v25 * v6 * v37 -
                    120 * u * v1 * v4 * v25 * v6 * v37 +
                    24 * u * v14 * v25 * v6 * v37 - 6 * u4 * v125 * v6 * v37 +
                    24 * u * v4 * v125 * v6 * v37 - 6 * u12 * v45 * v6 * v37 +
                    24 * u2 * v1 * v45 * v6 * v37 +
                    24 * u1 * v2 * v45 * v6 * v37 -
                    120 * u * v1 * v2 * v45 * v6 * v37 +
                    24 * u * v12 * v45 * v6 * v37 - 6 * u2 * v145 * v6 * v37 +
                    24 * u * v2 * v145 * v6 * v37 - 6 * u1 * v245 * v6 * v37 +
                    24 * u * v1 * v245 * v6 * v37 - 6 * u * v1245 * v6 * v37 +
                    2 * u245 * v16 * v37 - 6 * u45 * v2 * v16 * v37 -
                    6 * u25 * v4 * v16 * v37 + 24 * u5 * v2 * v4 * v16 * v37 -
                    6 * u5 * v24 * v16 * v37 - 6 * u24 * v5 * v16 * v37 +
                    24 * u4 * v2 * v5 * v16 * v37 +
                    24 * u2 * v4 * v5 * v16 * v37 -
                    120 * u * v2 * v4 * v5 * v16 * v37 +
                    24 * u * v24 * v5 * v16 * v37 - 6 * u4 * v25 * v16 * v37 +
                    24 * u * v4 * v25 * v16 * v37 - 6 * u2 * v45 * v16 * v37 +
                    24 * u * v2 * v45 * v16 * v37 - 6 * u * v245 * v16 * v37 +
                    2 * u145 * v26 * v37 - 6 * u45 * v1 * v26 * v37 -
                    6 * u15 * v4 * v26 * v37 + 24 * u5 * v1 * v4 * v26 * v37 -
                    6 * u5 * v14 * v26 * v37 - 6 * u14 * v5 * v26 * v37 +
                    24 * u4 * v1 * v5 * v26 * v37 +
                    24 * u1 * v4 * v5 * v26 * v37 -
                    120 * u * v1 * v4 * v5 * v26 * v37 +
                    24 * u * v14 * v5 * v26 * v37 - 6 * u4 * v15 * v26 * v37 +
                    24 * u * v4 * v15 * v26 * v37 - 6 * u1 * v45 * v26 * v37 +
                    24 * u * v1 * v45 * v26 * v37 - 6 * u * v145 * v26 * v37 +
                    2 * u45 * v126 * v37 - 6 * u5 * v4 * v126 * v37 -
                    6 * u4 * v5 * v126 * v37 + 24 * u * v4 * v5 * v126 * v37 -
                    6 * u * v45 * v126 * v37 + 2 * u125 * v46 * v37 -
                    6 * u25 * v1 * v46 * v37 - 6 * u15 * v2 * v46 * v37 +
                    24 * u5 * v1 * v2 * v46 * v37 - 6 * u5 * v12 * v46 * v37 -
                    6 * u12 * v5 * v46 * v37 + 24 * u2 * v1 * v5 * v46 * v37 +
                    24 * u1 * v2 * v5 * v46 * v37 -
                    120 * u * v1 * v2 * v5 * v46 * v37 +
                    24 * u * v12 * v5 * v46 * v37 - 6 * u2 * v15 * v46 * v37 +
                    24 * u * v2 * v15 * v46 * v37 - 6 * u1 * v25 * v46 * v37 +
                    24 * u * v1 * v25 * v46 * v37 - 6 * u * v125 * v46 * v37 +
                    2 * u25 * v146 * v37 - 6 * u5 * v2 * v146 * v37 -
                    6 * u2 * v5 * v146 * v37 + 24 * u * v2 * v5 * v146 * v37 -
                    6 * u * v25 * v146 * v37 + 2 * u15 * v246 * v37 -
                    6 * u5 * v1 * v246 * v37 - 6 * u1 * v5 * v246 * v37 +
                    24 * u * v1 * v5 * v246 * v37 - 6 * u * v15 * v246 * v37 +
                    2 * u5 * v1246 * v37 - 6 * u * v5 * v1246 * v37 +
                    2 * u124 * v56 * v37 - 6 * u24 * v1 * v56 * v37 -
                    6 * u14 * v2 * v56 * v37 + 24 * u4 * v1 * v2 * v56 * v37 -
                    6 * u4 * v12 * v56 * v37 - 6 * u12 * v4 * v56 * v37 +
                    24 * u2 * v1 * v4 * v56 * v37 +
                    24 * u1 * v2 * v4 * v56 * v37 -
                    120 * u * v1 * v2 * v4 * v56 * v37 +
                    24 * u * v12 * v4 * v56 * v37 - 6 * u2 * v14 * v56 * v37 +
                    24 * u * v2 * v14 * v56 * v37 - 6 * u1 * v24 * v56 * v37 +
                    24 * u * v1 * v24 * v56 * v37 - 6 * u * v124 * v56 * v37 +
                    2 * u24 * v156 * v37 - 6 * u4 * v2 * v156 * v37 -
                    6 * u2 * v4 * v156 * v37 + 24 * u * v2 * v4 * v156 * v37 -
                    6 * u * v24 * v156 * v37 + 2 * u14 * v256 * v37 -
                    6 * u4 * v1 * v256 * v37 - 6 * u1 * v4 * v256 * v37 +
                    24 * u * v1 * v4 * v256 * v37 - 6 * u * v14 * v256 * v37 +
                    2 * u4 * v1256 * v37 - 6 * u * v4 * v1256 * v37 +
                    2 * u12 * v456 * v37 - 6 * u2 * v1 * v456 * v37 -
                    6 * u1 * v2 * v456 * v37 + 24 * u * v1 * v2 * v456 * v37 -
                    6 * u * v12 * v456 * v37 + 2 * u2 * v1456 * v37 -
                    6 * u * v2 * v1456 * v37 + 2 * u1 * v2456 * v37 -
                    6 * u * v1 * v2456 * v37 + 2 * u * v12456 * v37 -
                    u2456 * v137 + 2 * u456 * v2 * v137 + 2 * u256 * v4 * v137 -
                    6 * u56 * v2 * v4 * v137 + 2 * u56 * v24 * v137 +
                    2 * u246 * v5 * v137 - 6 * u46 * v2 * v5 * v137 -
                    6 * u26 * v4 * v5 * v137 + 24 * u6 * v2 * v4 * v5 * v137 -
                    6 * u6 * v24 * v5 * v137 + 2 * u46 * v25 * v137 -
                    6 * u6 * v4 * v25 * v137 + 2 * u26 * v45 * v137 -
                    6 * u6 * v2 * v45 * v137 + 2 * u6 * v245 * v137 +
                    2 * u245 * v6 * v137 - 6 * u45 * v2 * v6 * v137 -
                    6 * u25 * v4 * v6 * v137 + 24 * u5 * v2 * v4 * v6 * v137 -
                    6 * u5 * v24 * v6 * v137 - 6 * u24 * v5 * v6 * v137 +
                    24 * u4 * v2 * v5 * v6 * v137 +
                    24 * u2 * v4 * v5 * v6 * v137 -
                    120 * u * v2 * v4 * v5 * v6 * v137 +
                    24 * u * v24 * v5 * v6 * v137 - 6 * u4 * v25 * v6 * v137 +
                    24 * u * v4 * v25 * v6 * v137 - 6 * u2 * v45 * v6 * v137 +
                    24 * u * v2 * v45 * v6 * v137 - 6 * u * v245 * v6 * v137 +
                    2 * u45 * v26 * v137 - 6 * u5 * v4 * v26 * v137 -
                    6 * u4 * v5 * v26 * v137 + 24 * u * v4 * v5 * v26 * v137 -
                    6 * u * v45 * v26 * v137 + 2 * u25 * v46 * v137 -
                    6 * u5 * v2 * v46 * v137 - 6 * u2 * v5 * v46 * v137 +
                    24 * u * v2 * v5 * v46 * v137 - 6 * u * v25 * v46 * v137 +
                    2 * u5 * v246 * v137 - 6 * u * v5 * v246 * v137 +
                    2 * u24 * v56 * v137 - 6 * u4 * v2 * v56 * v137 -
                    6 * u2 * v4 * v56 * v137 + 24 * u * v2 * v4 * v56 * v137 -
                    6 * u * v24 * v56 * v137 + 2 * u4 * v256 * v137 -
                    6 * u * v4 * v256 * v137 + 2 * u2 * v456 * v137 -
                    6 * u * v2 * v456 * v137 + 2 * u * v2456 * v137 -
                    u1456 * v237 + 2 * u456 * v1 * v237 + 2 * u156 * v4 * v237 -
                    6 * u56 * v1 * v4 * v237 + 2 * u56 * v14 * v237 +
                    2 * u146 * v5 * v237 - 6 * u46 * v1 * v5 * v237 -
                    6 * u16 * v4 * v5 * v237 + 24 * u6 * v1 * v4 * v5 * v237 -
                    6 * u6 * v14 * v5 * v237 + 2 * u46 * v15 * v237 -
                    6 * u6 * v4 * v15 * v237 + 2 * u16 * v45 * v237 -
                    6 * u6 * v1 * v45 * v237 + 2 * u6 * v145 * v237 +
                    2 * u145 * v6 * v237 - 6 * u45 * v1 * v6 * v237 -
                    6 * u15 * v4 * v6 * v237 + 24 * u5 * v1 * v4 * v6 * v237 -
                    6 * u5 * v14 * v6 * v237 - 6 * u14 * v5 * v6 * v237 +
                    24 * u4 * v1 * v5 * v6 * v237 +
                    24 * u1 * v4 * v5 * v6 * v237 -
                    120 * u * v1 * v4 * v5 * v6 * v237 +
                    24 * u * v14 * v5 * v6 * v237 - 6 * u4 * v15 * v6 * v237 +
                    24 * u * v4 * v15 * v6 * v237 - 6 * u1 * v45 * v6 * v237 +
                    24 * u * v1 * v45 * v6 * v237 - 6 * u * v145 * v6 * v237 +
                    2 * u45 * v16 * v237 - 6 * u5 * v4 * v16 * v237 -
                    6 * u4 * v5 * v16 * v237 + 24 * u * v4 * v5 * v16 * v237 -
                    6 * u * v45 * v16 * v237 + 2 * u15 * v46 * v237 -
                    6 * u5 * v1 * v46 * v237 - 6 * u1 * v5 * v46 * v237 +
                    24 * u * v1 * v5 * v46 * v237 - 6 * u * v15 * v46 * v237 +
                    2 * u5 * v146 * v237 - 6 * u * v5 * v146 * v237 +
                    2 * u14 * v56 * v237 - 6 * u4 * v1 * v56 * v237 -
                    6 * u1 * v4 * v56 * v237 + 24 * u * v1 * v4 * v56 * v237 -
                    6 * u * v14 * v56 * v237 + 2 * u4 * v156 * v237 -
                    6 * u * v4 * v156 * v237 + 2 * u1 * v456 * v237 -
                    6 * u * v1 * v456 * v237 + 2 * u * v1456 * v237 -
                    u456 * v1237 + 2 * u56 * v4 * v1237 + 2 * u46 * v5 * v1237 -
                    6 * u6 * v4 * v5 * v1237 + 2 * u6 * v45 * v1237 +
                    2 * u45 * v6 * v1237 - 6 * u5 * v4 * v6 * v1237 -
                    6 * u4 * v5 * v6 * v1237 + 24 * u * v4 * v5 * v6 * v1237 -
                    6 * u * v45 * v6 * v1237 + 2 * u5 * v46 * v1237 -
                    6 * u * v5 * v46 * v1237 + 2 * u4 * v56 * v1237 -
                    6 * u * v4 * v56 * v1237 + 2 * u * v456 * v1237 -
                    u12356 * v47 + 2 * u2356 * v1 * v47 + 2 * u1356 * v2 * v47 -
                    6 * u356 * v1 * v2 * v47 + 2 * u356 * v12 * v47 +
                    2 * u1256 * v3 * v47 - 6 * u256 * v1 * v3 * v47 -
                    6 * u156 * v2 * v3 * v47 + 24 * u56 * v1 * v2 * v3 * v47 -
                    6 * u56 * v12 * v3 * v47 + 2 * u256 * v13 * v47 -
                    6 * u56 * v2 * v13 * v47 + 2 * u156 * v23 * v47 -
                    6 * u56 * v1 * v23 * v47 + 2 * u56 * v123 * v47 +
                    2 * u1236 * v5 * v47 - 6 * u236 * v1 * v5 * v47 -
                    6 * u136 * v2 * v5 * v47 + 24 * u36 * v1 * v2 * v5 * v47 -
                    6 * u36 * v12 * v5 * v47 - 6 * u126 * v3 * v5 * v47 +
                    24 * u26 * v1 * v3 * v5 * v47 +
                    24 * u16 * v2 * v3 * v5 * v47 -
                    120 * u6 * v1 * v2 * v3 * v5 * v47 +
                    24 * u6 * v12 * v3 * v5 * v47 - 6 * u26 * v13 * v5 * v47 +
                    24 * u6 * v2 * v13 * v5 * v47 - 6 * u16 * v23 * v5 * v47 +
                    24 * u6 * v1 * v23 * v5 * v47 - 6 * u6 * v123 * v5 * v47 +
                    2 * u236 * v15 * v47 - 6 * u36 * v2 * v15 * v47 -
                    6 * u26 * v3 * v15 * v47 + 24 * u6 * v2 * v3 * v15 * v47 -
                    6 * u6 * v23 * v15 * v47 + 2 * u136 * v25 * v47 -
                    6 * u36 * v1 * v25 * v47 - 6 * u16 * v3 * v25 * v47 +
                    24 * u6 * v1 * v3 * v25 * v47 - 6 * u6 * v13 * v25 * v47 +
                    2 * u36 * v125 * v47 - 6 * u6 * v3 * v125 * v47 +
                    2 * u126 * v35 * v47 - 6 * u26 * v1 * v35 * v47 -
                    6 * u16 * v2 * v35 * v47 + 24 * u6 * v1 * v2 * v35 * v47 -
                    6 * u6 * v12 * v35 * v47 + 2 * u26 * v135 * v47 -
                    6 * u6 * v2 * v135 * v47 + 2 * u16 * v235 * v47 -
                    6 * u6 * v1 * v235 * v47 + 2 * u6 * v1235 * v47 +
                    2 * u1235 * v6 * v47 - 6 * u235 * v1 * v6 * v47 -
                    6 * u135 * v2 * v6 * v47 + 24 * u35 * v1 * v2 * v6 * v47 -
                    6 * u35 * v12 * v6 * v47 - 6 * u125 * v3 * v6 * v47 +
                    24 * u25 * v1 * v3 * v6 * v47 +
                    24 * u15 * v2 * v3 * v6 * v47 -
                    120 * u5 * v1 * v2 * v3 * v6 * v47 +
                    24 * u5 * v12 * v3 * v6 * v47 - 6 * u25 * v13 * v6 * v47 +
                    24 * u5 * v2 * v13 * v6 * v47 - 6 * u15 * v23 * v6 * v47 +
                    24 * u5 * v1 * v23 * v6 * v47 - 6 * u5 * v123 * v6 * v47 -
                    6 * u123 * v5 * v6 * v47 + 24 * u23 * v1 * v5 * v6 * v47 +
                    24 * u13 * v2 * v5 * v6 * v47 -
                    120 * u3 * v1 * v2 * v5 * v6 * v47 +
                    24 * u3 * v12 * v5 * v6 * v47 +
                    24 * u12 * v3 * v5 * v6 * v47 -
                    120 * u2 * v1 * v3 * v5 * v6 * v47 -
                    120 * u1 * v2 * v3 * v5 * v6 * v47 +
                    720 * u * v1 * v2 * v3 * v5 * v6 * v47 -
                    120 * u * v12 * v3 * v5 * v6 * v47 +
                    24 * u2 * v13 * v5 * v6 * v47 -
                    120 * u * v2 * v13 * v5 * v6 * v47 +
                    24 * u1 * v23 * v5 * v6 * v47 -
                    120 * u * v1 * v23 * v5 * v6 * v47 +
                    24 * u * v123 * v5 * v6 * v47 - 6 * u23 * v15 * v6 * v47 +
                    24 * u3 * v2 * v15 * v6 * v47 +
                    24 * u2 * v3 * v15 * v6 * v47 -
                    120 * u * v2 * v3 * v15 * v6 * v47 +
                    24 * u * v23 * v15 * v6 * v47 - 6 * u13 * v25 * v6 * v47 +
                    24 * u3 * v1 * v25 * v6 * v47 +
                    24 * u1 * v3 * v25 * v6 * v47 -
                    120 * u * v1 * v3 * v25 * v6 * v47 +
                    24 * u * v13 * v25 * v6 * v47 - 6 * u3 * v125 * v6 * v47 +
                    24 * u * v3 * v125 * v6 * v47 - 6 * u12 * v35 * v6 * v47 +
                    24 * u2 * v1 * v35 * v6 * v47 +
                    24 * u1 * v2 * v35 * v6 * v47 -
                    120 * u * v1 * v2 * v35 * v6 * v47 +
                    24 * u * v12 * v35 * v6 * v47 - 6 * u2 * v135 * v6 * v47 +
                    24 * u * v2 * v135 * v6 * v47 - 6 * u1 * v235 * v6 * v47 +
                    24 * u * v1 * v235 * v6 * v47 - 6 * u * v1235 * v6 * v47 +
                    2 * u235 * v16 * v47 - 6 * u35 * v2 * v16 * v47 -
                    6 * u25 * v3 * v16 * v47 + 24 * u5 * v2 * v3 * v16 * v47 -
                    6 * u5 * v23 * v16 * v47 - 6 * u23 * v5 * v16 * v47 +
                    24 * u3 * v2 * v5 * v16 * v47 +
                    24 * u2 * v3 * v5 * v16 * v47 -
                    120 * u * v2 * v3 * v5 * v16 * v47 +
                    24 * u * v23 * v5 * v16 * v47 - 6 * u3 * v25 * v16 * v47 +
                    24 * u * v3 * v25 * v16 * v47 - 6 * u2 * v35 * v16 * v47 +
                    24 * u * v2 * v35 * v16 * v47 - 6 * u * v235 * v16 * v47 +
                    2 * u135 * v26 * v47 - 6 * u35 * v1 * v26 * v47 -
                    6 * u15 * v3 * v26 * v47 + 24 * u5 * v1 * v3 * v26 * v47 -
                    6 * u5 * v13 * v26 * v47 - 6 * u13 * v5 * v26 * v47 +
                    24 * u3 * v1 * v5 * v26 * v47 +
                    24 * u1 * v3 * v5 * v26 * v47 -
                    120 * u * v1 * v3 * v5 * v26 * v47 +
                    24 * u * v13 * v5 * v26 * v47 - 6 * u3 * v15 * v26 * v47 +
                    24 * u * v3 * v15 * v26 * v47 - 6 * u1 * v35 * v26 * v47 +
                    24 * u * v1 * v35 * v26 * v47 - 6 * u * v135 * v26 * v47 +
                    2 * u35 * v126 * v47 - 6 * u5 * v3 * v126 * v47 -
                    6 * u3 * v5 * v126 * v47 + 24 * u * v3 * v5 * v126 * v47 -
                    6 * u * v35 * v126 * v47 + 2 * u125 * v36 * v47 -
                    6 * u25 * v1 * v36 * v47 - 6 * u15 * v2 * v36 * v47 +
                    24 * u5 * v1 * v2 * v36 * v47 - 6 * u5 * v12 * v36 * v47 -
                    6 * u12 * v5 * v36 * v47 + 24 * u2 * v1 * v5 * v36 * v47 +
                    24 * u1 * v2 * v5 * v36 * v47 -
                    120 * u * v1 * v2 * v5 * v36 * v47 +
                    24 * u * v12 * v5 * v36 * v47 - 6 * u2 * v15 * v36 * v47 +
                    24 * u * v2 * v15 * v36 * v47 - 6 * u1 * v25 * v36 * v47 +
                    24 * u * v1 * v25 * v36 * v47 - 6 * u * v125 * v36 * v47 +
                    2 * u25 * v136 * v47 - 6 * u5 * v2 * v136 * v47 -
                    6 * u2 * v5 * v136 * v47 + 24 * u * v2 * v5 * v136 * v47 -
                    6 * u * v25 * v136 * v47 + 2 * u15 * v236 * v47 -
                    6 * u5 * v1 * v236 * v47 - 6 * u1 * v5 * v236 * v47 +
                    24 * u * v1 * v5 * v236 * v47 - 6 * u * v15 * v236 * v47 +
                    2 * u5 * v1236 * v47 - 6 * u * v5 * v1236 * v47 +
                    2 * u123 * v56 * v47 - 6 * u23 * v1 * v56 * v47 -
                    6 * u13 * v2 * v56 * v47 + 24 * u3 * v1 * v2 * v56 * v47 -
                    6 * u3 * v12 * v56 * v47 - 6 * u12 * v3 * v56 * v47 +
                    24 * u2 * v1 * v3 * v56 * v47 +
                    24 * u1 * v2 * v3 * v56 * v47 -
                    120 * u * v1 * v2 * v3 * v56 * v47 +
                    24 * u * v12 * v3 * v56 * v47 - 6 * u2 * v13 * v56 * v47 +
                    24 * u * v2 * v13 * v56 * v47 - 6 * u1 * v23 * v56 * v47 +
                    24 * u * v1 * v23 * v56 * v47 - 6 * u * v123 * v56 * v47 +
                    2 * u23 * v156 * v47 - 6 * u3 * v2 * v156 * v47 -
                    6 * u2 * v3 * v156 * v47 + 24 * u * v2 * v3 * v156 * v47 -
                    6 * u * v23 * v156 * v47 + 2 * u13 * v256 * v47 -
                    6 * u3 * v1 * v256 * v47 - 6 * u1 * v3 * v256 * v47 +
                    24 * u * v1 * v3 * v256 * v47 - 6 * u * v13 * v256 * v47 +
                    2 * u3 * v1256 * v47 - 6 * u * v3 * v1256 * v47 +
                    2 * u12 * v356 * v47 - 6 * u2 * v1 * v356 * v47 -
                    6 * u1 * v2 * v356 * v47 + 24 * u * v1 * v2 * v356 * v47 -
                    6 * u * v12 * v356 * v47 + 2 * u2 * v1356 * v47 -
                    6 * u * v2 * v1356 * v47 + 2 * u1 * v2356 * v47 -
                    6 * u * v1 * v2356 * v47 + 2 * u * v12356 * v47 -
                    u2356 * v147 + 2 * u356 * v2 * v147 + 2 * u256 * v3 * v147 -
                    6 * u56 * v2 * v3 * v147 + 2 * u56 * v23 * v147 +
                    2 * u236 * v5 * v147 - 6 * u36 * v2 * v5 * v147 -
                    6 * u26 * v3 * v5 * v147 + 24 * u6 * v2 * v3 * v5 * v147 -
                    6 * u6 * v23 * v5 * v147 + 2 * u36 * v25 * v147 -
                    6 * u6 * v3 * v25 * v147 + 2 * u26 * v35 * v147 -
                    6 * u6 * v2 * v35 * v147 + 2 * u6 * v235 * v147 +
                    2 * u235 * v6 * v147 - 6 * u35 * v2 * v6 * v147 -
                    6 * u25 * v3 * v6 * v147 + 24 * u5 * v2 * v3 * v6 * v147 -
                    6 * u5 * v23 * v6 * v147 - 6 * u23 * v5 * v6 * v147 +
                    24 * u3 * v2 * v5 * v6 * v147 +
                    24 * u2 * v3 * v5 * v6 * v147 -
                    120 * u * v2 * v3 * v5 * v6 * v147 +
                    24 * u * v23 * v5 * v6 * v147 - 6 * u3 * v25 * v6 * v147 +
                    24 * u * v3 * v25 * v6 * v147 - 6 * u2 * v35 * v6 * v147 +
                    24 * u * v2 * v35 * v6 * v147 - 6 * u * v235 * v6 * v147 +
                    2 * u35 * v26 * v147 - 6 * u5 * v3 * v26 * v147 -
                    6 * u3 * v5 * v26 * v147 + 24 * u * v3 * v5 * v26 * v147 -
                    6 * u * v35 * v26 * v147 + 2 * u25 * v36 * v147 -
                    6 * u5 * v2 * v36 * v147 - 6 * u2 * v5 * v36 * v147 +
                    24 * u * v2 * v5 * v36 * v147 - 6 * u * v25 * v36 * v147 +
                    2 * u5 * v236 * v147 - 6 * u * v5 * v236 * v147 +
                    2 * u23 * v56 * v147 - 6 * u3 * v2 * v56 * v147 -
                    6 * u2 * v3 * v56 * v147 + 24 * u * v2 * v3 * v56 * v147 -
                    6 * u * v23 * v56 * v147 + 2 * u3 * v256 * v147 -
                    6 * u * v3 * v256 * v147 + 2 * u2 * v356 * v147 -
                    6 * u * v2 * v356 * v147 + 2 * u * v2356 * v147 -
                    u1356 * v247 + 2 * u356 * v1 * v247 + 2 * u156 * v3 * v247 -
                    6 * u56 * v1 * v3 * v247 + 2 * u56 * v13 * v247 +
                    2 * u136 * v5 * v247 - 6 * u36 * v1 * v5 * v247 -
                    6 * u16 * v3 * v5 * v247 + 24 * u6 * v1 * v3 * v5 * v247 -
                    6 * u6 * v13 * v5 * v247 + 2 * u36 * v15 * v247 -
                    6 * u6 * v3 * v15 * v247 + 2 * u16 * v35 * v247 -
                    6 * u6 * v1 * v35 * v247 + 2 * u6 * v135 * v247 +
                    2 * u135 * v6 * v247 - 6 * u35 * v1 * v6 * v247 -
                    6 * u15 * v3 * v6 * v247 + 24 * u5 * v1 * v3 * v6 * v247 -
                    6 * u5 * v13 * v6 * v247 - 6 * u13 * v5 * v6 * v247 +
                    24 * u3 * v1 * v5 * v6 * v247 +
                    24 * u1 * v3 * v5 * v6 * v247 -
                    120 * u * v1 * v3 * v5 * v6 * v247 +
                    24 * u * v13 * v5 * v6 * v247 - 6 * u3 * v15 * v6 * v247 +
                    24 * u * v3 * v15 * v6 * v247 - 6 * u1 * v35 * v6 * v247 +
                    24 * u * v1 * v35 * v6 * v247 - 6 * u * v135 * v6 * v247 +
                    2 * u35 * v16 * v247 - 6 * u5 * v3 * v16 * v247 -
                    6 * u3 * v5 * v16 * v247 + 24 * u * v3 * v5 * v16 * v247 -
                    6 * u * v35 * v16 * v247 + 2 * u15 * v36 * v247 -
                    6 * u5 * v1 * v36 * v247 - 6 * u1 * v5 * v36 * v247 +
                    24 * u * v1 * v5 * v36 * v247 - 6 * u * v15 * v36 * v247 +
                    2 * u5 * v136 * v247 - 6 * u * v5 * v136 * v247 +
                    2 * u13 * v56 * v247 - 6 * u3 * v1 * v56 * v247 -
                    6 * u1 * v3 * v56 * v247 + 24 * u * v1 * v3 * v56 * v247 -
                    6 * u * v13 * v56 * v247 + 2 * u3 * v156 * v247 -
                    6 * u * v3 * v156 * v247 + 2 * u1 * v356 * v247 -
                    6 * u * v1 * v356 * v247 + 2 * u * v1356 * v247 -
                    u356 * v1247 + 2 * u56 * v3 * v1247 + 2 * u36 * v5 * v1247 -
                    6 * u6 * v3 * v5 * v1247 + 2 * u6 * v35 * v1247 +
                    2 * u35 * v6 * v1247 - 6 * u5 * v3 * v6 * v1247 -
                    6 * u3 * v5 * v6 * v1247 + 24 * u * v3 * v5 * v6 * v1247 -
                    6 * u * v35 * v6 * v1247 + 2 * u5 * v36 * v1247 -
                    6 * u * v5 * v36 * v1247 + 2 * u3 * v56 * v1247 -
                    6 * u * v3 * v56 * v1247 + 2 * u * v356 * v1247 -
                    u1256 * v347 + 2 * u256 * v1 * v347 + 2 * u156 * v2 * v347 -
                    6 * u56 * v1 * v2 * v347 + 2 * u56 * v12 * v347 +
                    2 * u126 * v5 * v347 - 6 * u26 * v1 * v5 * v347 -
                    6 * u16 * v2 * v5 * v347 + 24 * u6 * v1 * v2 * v5 * v347 -
                    6 * u6 * v12 * v5 * v347 + 2 * u26 * v15 * v347 -
                    6 * u6 * v2 * v15 * v347 + 2 * u16 * v25 * v347 -
                    6 * u6 * v1 * v25 * v347 + 2 * u6 * v125 * v347 +
                    2 * u125 * v6 * v347 - 6 * u25 * v1 * v6 * v347 -
                    6 * u15 * v2 * v6 * v347 + 24 * u5 * v1 * v2 * v6 * v347 -
                    6 * u5 * v12 * v6 * v347 - 6 * u12 * v5 * v6 * v347 +
                    24 * u2 * v1 * v5 * v6 * v347 +
                    24 * u1 * v2 * v5 * v6 * v347 -
                    120 * u * v1 * v2 * v5 * v6 * v347 +
                    24 * u * v12 * v5 * v6 * v347 - 6 * u2 * v15 * v6 * v347 +
                    24 * u * v2 * v15 * v6 * v347 - 6 * u1 * v25 * v6 * v347 +
                    24 * u * v1 * v25 * v6 * v347 - 6 * u * v125 * v6 * v347 +
                    2 * u25 * v16 * v347 - 6 * u5 * v2 * v16 * v347 -
                    6 * u2 * v5 * v16 * v347 + 24 * u * v2 * v5 * v16 * v347 -
                    6 * u * v25 * v16 * v347 + 2 * u15 * v26 * v347 -
                    6 * u5 * v1 * v26 * v347 - 6 * u1 * v5 * v26 * v347 +
                    24 * u * v1 * v5 * v26 * v347 - 6 * u * v15 * v26 * v347 +
                    2 * u5 * v126 * v347 - 6 * u * v5 * v126 * v347 +
                    2 * u12 * v56 * v347 - 6 * u2 * v1 * v56 * v347 -
                    6 * u1 * v2 * v56 * v347 + 24 * u * v1 * v2 * v56 * v347 -
                    6 * u * v12 * v56 * v347 + 2 * u2 * v156 * v347 -
                    6 * u * v2 * v156 * v347 + 2 * u1 * v256 * v347 -
                    6 * u * v1 * v256 * v347 + 2 * u * v1256 * v347 -
                    u256 * v1347 + 2 * u56 * v2 * v1347 + 2 * u26 * v5 * v1347 -
                    6 * u6 * v2 * v5 * v1347 + 2 * u6 * v25 * v1347 +
                    2 * u25 * v6 * v1347 - 6 * u5 * v2 * v6 * v1347 -
                    6 * u2 * v5 * v6 * v1347 + 24 * u * v2 * v5 * v6 * v1347 -
                    6 * u * v25 * v6 * v1347 + 2 * u5 * v26 * v1347 -
                    6 * u * v5 * v26 * v1347 + 2 * u2 * v56 * v1347 -
                    6 * u * v2 * v56 * v1347 + 2 * u * v256 * v1347 -
                    u156 * v2347 + 2 * u56 * v1 * v2347 + 2 * u16 * v5 * v2347 -
                    6 * u6 * v1 * v5 * v2347 + 2 * u6 * v15 * v2347 +
                    2 * u15 * v6 * v2347 - 6 * u5 * v1 * v6 * v2347 -
                    6 * u1 * v5 * v6 * v2347 + 24 * u * v1 * v5 * v6 * v2347 -
                    6 * u * v15 * v6 * v2347 + 2 * u5 * v16 * v2347 -
                    6 * u * v5 * v16 * v2347 + 2 * u1 * v56 * v2347 -
                    6 * u * v1 * v56 * v2347 + 2 * u * v156 * v2347 -
                    u56 * v12347 + 2 * u6 * v5 * v12347 + 2 * u5 * v6 * v12347 -
                    6 * u * v5 * v6 * v12347 + 2 * u * v56 * v12347 -
                    u12346 * v57 + 2 * u2346 * v1 * v57 + 2 * u1346 * v2 * v57 -
                    6 * u346 * v1 * v2 * v57 + 2 * u346 * v12 * v57 +
                    2 * u1246 * v3 * v57 - 6 * u246 * v1 * v3 * v57 -
                    6 * u146 * v2 * v3 * v57 + 24 * u46 * v1 * v2 * v3 * v57 -
                    6 * u46 * v12 * v3 * v57 + 2 * u246 * v13 * v57 -
                    6 * u46 * v2 * v13 * v57 + 2 * u146 * v23 * v57 -
                    6 * u46 * v1 * v23 * v57 + 2 * u46 * v123 * v57 +
                    2 * u1236 * v4 * v57 - 6 * u236 * v1 * v4 * v57 -
                    6 * u136 * v2 * v4 * v57 + 24 * u36 * v1 * v2 * v4 * v57 -
                    6 * u36 * v12 * v4 * v57 - 6 * u126 * v3 * v4 * v57 +
                    24 * u26 * v1 * v3 * v4 * v57 +
                    24 * u16 * v2 * v3 * v4 * v57 -
                    120 * u6 * v1 * v2 * v3 * v4 * v57 +
                    24 * u6 * v12 * v3 * v4 * v57 - 6 * u26 * v13 * v4 * v57 +
                    24 * u6 * v2 * v13 * v4 * v57 - 6 * u16 * v23 * v4 * v57 +
                    24 * u6 * v1 * v23 * v4 * v57 - 6 * u6 * v123 * v4 * v57 +
                    2 * u236 * v14 * v57 - 6 * u36 * v2 * v14 * v57 -
                    6 * u26 * v3 * v14 * v57 + 24 * u6 * v2 * v3 * v14 * v57 -
                    6 * u6 * v23 * v14 * v57 + 2 * u136 * v24 * v57 -
                    6 * u36 * v1 * v24 * v57 - 6 * u16 * v3 * v24 * v57 +
                    24 * u6 * v1 * v3 * v24 * v57 - 6 * u6 * v13 * v24 * v57 +
                    2 * u36 * v124 * v57 - 6 * u6 * v3 * v124 * v57 +
                    2 * u126 * v34 * v57 - 6 * u26 * v1 * v34 * v57 -
                    6 * u16 * v2 * v34 * v57 + 24 * u6 * v1 * v2 * v34 * v57 -
                    6 * u6 * v12 * v34 * v57 + 2 * u26 * v134 * v57 -
                    6 * u6 * v2 * v134 * v57 + 2 * u16 * v234 * v57 -
                    6 * u6 * v1 * v234 * v57 + 2 * u6 * v1234 * v57 +
                    2 * u1234 * v6 * v57 - 6 * u234 * v1 * v6 * v57 -
                    6 * u134 * v2 * v6 * v57 + 24 * u34 * v1 * v2 * v6 * v57 -
                    6 * u34 * v12 * v6 * v57 - 6 * u124 * v3 * v6 * v57 +
                    24 * u24 * v1 * v3 * v6 * v57 +
                    24 * u14 * v2 * v3 * v6 * v57 -
                    120 * u4 * v1 * v2 * v3 * v6 * v57 +
                    24 * u4 * v12 * v3 * v6 * v57 - 6 * u24 * v13 * v6 * v57 +
                    24 * u4 * v2 * v13 * v6 * v57 - 6 * u14 * v23 * v6 * v57 +
                    24 * u4 * v1 * v23 * v6 * v57 - 6 * u4 * v123 * v6 * v57 -
                    6 * u123 * v4 * v6 * v57 + 24 * u23 * v1 * v4 * v6 * v57 +
                    24 * u13 * v2 * v4 * v6 * v57 -
                    120 * u3 * v1 * v2 * v4 * v6 * v57 +
                    24 * u3 * v12 * v4 * v6 * v57 +
                    24 * u12 * v3 * v4 * v6 * v57 -
                    120 * u2 * v1 * v3 * v4 * v6 * v57 -
                    120 * u1 * v2 * v3 * v4 * v6 * v57 +
                    720 * u * v1 * v2 * v3 * v4 * v6 * v57 -
                    120 * u * v12 * v3 * v4 * v6 * v57 +
                    24 * u2 * v13 * v4 * v6 * v57 -
                    120 * u * v2 * v13 * v4 * v6 * v57 +
                    24 * u1 * v23 * v4 * v6 * v57 -
                    120 * u * v1 * v23 * v4 * v6 * v57 +
                    24 * u * v123 * v4 * v6 * v57 - 6 * u23 * v14 * v6 * v57 +
                    24 * u3 * v2 * v14 * v6 * v57 +
                    24 * u2 * v3 * v14 * v6 * v57 -
                    120 * u * v2 * v3 * v14 * v6 * v57 +
                    24 * u * v23 * v14 * v6 * v57 - 6 * u13 * v24 * v6 * v57 +
                    24 * u3 * v1 * v24 * v6 * v57 +
                    24 * u1 * v3 * v24 * v6 * v57 -
                    120 * u * v1 * v3 * v24 * v6 * v57 +
                    24 * u * v13 * v24 * v6 * v57 - 6 * u3 * v124 * v6 * v57 +
                    24 * u * v3 * v124 * v6 * v57 - 6 * u12 * v34 * v6 * v57 +
                    24 * u2 * v1 * v34 * v6 * v57 +
                    24 * u1 * v2 * v34 * v6 * v57 -
                    120 * u * v1 * v2 * v34 * v6 * v57 +
                    24 * u * v12 * v34 * v6 * v57 - 6 * u2 * v134 * v6 * v57 +
                    24 * u * v2 * v134 * v6 * v57 - 6 * u1 * v234 * v6 * v57 +
                    24 * u * v1 * v234 * v6 * v57 - 6 * u * v1234 * v6 * v57 +
                    2 * u234 * v16 * v57 - 6 * u34 * v2 * v16 * v57 -
                    6 * u24 * v3 * v16 * v57 + 24 * u4 * v2 * v3 * v16 * v57 -
                    6 * u4 * v23 * v16 * v57 - 6 * u23 * v4 * v16 * v57 +
                    24 * u3 * v2 * v4 * v16 * v57 +
                    24 * u2 * v3 * v4 * v16 * v57 -
                    120 * u * v2 * v3 * v4 * v16 * v57 +
                    24 * u * v23 * v4 * v16 * v57 - 6 * u3 * v24 * v16 * v57 +
                    24 * u * v3 * v24 * v16 * v57 - 6 * u2 * v34 * v16 * v57 +
                    24 * u * v2 * v34 * v16 * v57 - 6 * u * v234 * v16 * v57 +
                    2 * u134 * v26 * v57 - 6 * u34 * v1 * v26 * v57 -
                    6 * u14 * v3 * v26 * v57 + 24 * u4 * v1 * v3 * v26 * v57 -
                    6 * u4 * v13 * v26 * v57 - 6 * u13 * v4 * v26 * v57 +
                    24 * u3 * v1 * v4 * v26 * v57 +
                    24 * u1 * v3 * v4 * v26 * v57 -
                    120 * u * v1 * v3 * v4 * v26 * v57 +
                    24 * u * v13 * v4 * v26 * v57 - 6 * u3 * v14 * v26 * v57 +
                    24 * u * v3 * v14 * v26 * v57 - 6 * u1 * v34 * v26 * v57 +
                    24 * u * v1 * v34 * v26 * v57 - 6 * u * v134 * v26 * v57 +
                    2 * u34 * v126 * v57 - 6 * u4 * v3 * v126 * v57 -
                    6 * u3 * v4 * v126 * v57 + 24 * u * v3 * v4 * v126 * v57 -
                    6 * u * v34 * v126 * v57 + 2 * u124 * v36 * v57 -
                    6 * u24 * v1 * v36 * v57 - 6 * u14 * v2 * v36 * v57 +
                    24 * u4 * v1 * v2 * v36 * v57 - 6 * u4 * v12 * v36 * v57 -
                    6 * u12 * v4 * v36 * v57 + 24 * u2 * v1 * v4 * v36 * v57 +
                    24 * u1 * v2 * v4 * v36 * v57 -
                    120 * u * v1 * v2 * v4 * v36 * v57 +
                    24 * u * v12 * v4 * v36 * v57 - 6 * u2 * v14 * v36 * v57 +
                    24 * u * v2 * v14 * v36 * v57 - 6 * u1 * v24 * v36 * v57 +
                    24 * u * v1 * v24 * v36 * v57 - 6 * u * v124 * v36 * v57 +
                    2 * u24 * v136 * v57 - 6 * u4 * v2 * v136 * v57 -
                    6 * u2 * v4 * v136 * v57 + 24 * u * v2 * v4 * v136 * v57 -
                    6 * u * v24 * v136 * v57 + 2 * u14 * v236 * v57 -
                    6 * u4 * v1 * v236 * v57 - 6 * u1 * v4 * v236 * v57 +
                    24 * u * v1 * v4 * v236 * v57 - 6 * u * v14 * v236 * v57 +
                    2 * u4 * v1236 * v57 - 6 * u * v4 * v1236 * v57 +
                    2 * u123 * v46 * v57 - 6 * u23 * v1 * v46 * v57 -
                    6 * u13 * v2 * v46 * v57 + 24 * u3 * v1 * v2 * v46 * v57 -
                    6 * u3 * v12 * v46 * v57 - 6 * u12 * v3 * v46 * v57 +
                    24 * u2 * v1 * v3 * v46 * v57 +
                    24 * u1 * v2 * v3 * v46 * v57 -
                    120 * u * v1 * v2 * v3 * v46 * v57 +
                    24 * u * v12 * v3 * v46 * v57 - 6 * u2 * v13 * v46 * v57 +
                    24 * u * v2 * v13 * v46 * v57 - 6 * u1 * v23 * v46 * v57 +
                    24 * u * v1 * v23 * v46 * v57 - 6 * u * v123 * v46 * v57 +
                    2 * u23 * v146 * v57 - 6 * u3 * v2 * v146 * v57 -
                    6 * u2 * v3 * v146 * v57 + 24 * u * v2 * v3 * v146 * v57 -
                    6 * u * v23 * v146 * v57 + 2 * u13 * v246 * v57 -
                    6 * u3 * v1 * v246 * v57 - 6 * u1 * v3 * v246 * v57 +
                    24 * u * v1 * v3 * v246 * v57 - 6 * u * v13 * v246 * v57 +
                    2 * u3 * v1246 * v57 - 6 * u * v3 * v1246 * v57 +
                    2 * u12 * v346 * v57 - 6 * u2 * v1 * v346 * v57 -
                    6 * u1 * v2 * v346 * v57 + 24 * u * v1 * v2 * v346 * v57 -
                    6 * u * v12 * v346 * v57 + 2 * u2 * v1346 * v57 -
                    6 * u * v2 * v1346 * v57 + 2 * u1 * v2346 * v57 -
                    6 * u * v1 * v2346 * v57 + 2 * u * v12346 * v57 -
                    u2346 * v157 + 2 * u346 * v2 * v157 + 2 * u246 * v3 * v157 -
                    6 * u46 * v2 * v3 * v157 + 2 * u46 * v23 * v157 +
                    2 * u236 * v4 * v157 - 6 * u36 * v2 * v4 * v157 -
                    6 * u26 * v3 * v4 * v157 + 24 * u6 * v2 * v3 * v4 * v157 -
                    6 * u6 * v23 * v4 * v157 + 2 * u36 * v24 * v157 -
                    6 * u6 * v3 * v24 * v157 + 2 * u26 * v34 * v157 -
                    6 * u6 * v2 * v34 * v157 + 2 * u6 * v234 * v157 +
                    2 * u234 * v6 * v157 - 6 * u34 * v2 * v6 * v157 -
                    6 * u24 * v3 * v6 * v157 + 24 * u4 * v2 * v3 * v6 * v157 -
                    6 * u4 * v23 * v6 * v157 - 6 * u23 * v4 * v6 * v157 +
                    24 * u3 * v2 * v4 * v6 * v157 +
                    24 * u2 * v3 * v4 * v6 * v157 -
                    120 * u * v2 * v3 * v4 * v6 * v157 +
                    24 * u * v23 * v4 * v6 * v157 - 6 * u3 * v24 * v6 * v157 +
                    24 * u * v3 * v24 * v6 * v157 - 6 * u2 * v34 * v6 * v157 +
                    24 * u * v2 * v34 * v6 * v157 - 6 * u * v234 * v6 * v157 +
                    2 * u34 * v26 * v157 - 6 * u4 * v3 * v26 * v157 -
                    6 * u3 * v4 * v26 * v157 + 24 * u * v3 * v4 * v26 * v157 -
                    6 * u * v34 * v26 * v157 + 2 * u24 * v36 * v157 -
                    6 * u4 * v2 * v36 * v157 - 6 * u2 * v4 * v36 * v157 +
                    24 * u * v2 * v4 * v36 * v157 - 6 * u * v24 * v36 * v157 +
                    2 * u4 * v236 * v157 - 6 * u * v4 * v236 * v157 +
                    2 * u23 * v46 * v157 - 6 * u3 * v2 * v46 * v157 -
                    6 * u2 * v3 * v46 * v157 + 24 * u * v2 * v3 * v46 * v157 -
                    6 * u * v23 * v46 * v157 + 2 * u3 * v246 * v157 -
                    6 * u * v3 * v246 * v157 + 2 * u2 * v346 * v157 -
                    6 * u * v2 * v346 * v157 + 2 * u * v2346 * v157 -
                    u1346 * v257 + 2 * u346 * v1 * v257 + 2 * u146 * v3 * v257 -
                    6 * u46 * v1 * v3 * v257 + 2 * u46 * v13 * v257 +
                    2 * u136 * v4 * v257 - 6 * u36 * v1 * v4 * v257 -
                    6 * u16 * v3 * v4 * v257 + 24 * u6 * v1 * v3 * v4 * v257 -
                    6 * u6 * v13 * v4 * v257 + 2 * u36 * v14 * v257 -
                    6 * u6 * v3 * v14 * v257 + 2 * u16 * v34 * v257 -
                    6 * u6 * v1 * v34 * v257 + 2 * u6 * v134 * v257 +
                    2 * u134 * v6 * v257 - 6 * u34 * v1 * v6 * v257 -
                    6 * u14 * v3 * v6 * v257 + 24 * u4 * v1 * v3 * v6 * v257 -
                    6 * u4 * v13 * v6 * v257 - 6 * u13 * v4 * v6 * v257 +
                    24 * u3 * v1 * v4 * v6 * v257 +
                    24 * u1 * v3 * v4 * v6 * v257 -
                    120 * u * v1 * v3 * v4 * v6 * v257 +
                    24 * u * v13 * v4 * v6 * v257 - 6 * u3 * v14 * v6 * v257 +
                    24 * u * v3 * v14 * v6 * v257 - 6 * u1 * v34 * v6 * v257 +
                    24 * u * v1 * v34 * v6 * v257 - 6 * u * v134 * v6 * v257 +
                    2 * u34 * v16 * v257 - 6 * u4 * v3 * v16 * v257 -
                    6 * u3 * v4 * v16 * v257 + 24 * u * v3 * v4 * v16 * v257 -
                    6 * u * v34 * v16 * v257 + 2 * u14 * v36 * v257 -
                    6 * u4 * v1 * v36 * v257 - 6 * u1 * v4 * v36 * v257 +
                    24 * u * v1 * v4 * v36 * v257 - 6 * u * v14 * v36 * v257 +
                    2 * u4 * v136 * v257 - 6 * u * v4 * v136 * v257 +
                    2 * u13 * v46 * v257 - 6 * u3 * v1 * v46 * v257 -
                    6 * u1 * v3 * v46 * v257 + 24 * u * v1 * v3 * v46 * v257 -
                    6 * u * v13 * v46 * v257 + 2 * u3 * v146 * v257 -
                    6 * u * v3 * v146 * v257 + 2 * u1 * v346 * v257 -
                    6 * u * v1 * v346 * v257 + 2 * u * v1346 * v257 -
                    u346 * v1257 + 2 * u46 * v3 * v1257 + 2 * u36 * v4 * v1257 -
                    6 * u6 * v3 * v4 * v1257 + 2 * u6 * v34 * v1257 +
                    2 * u34 * v6 * v1257 - 6 * u4 * v3 * v6 * v1257 -
                    6 * u3 * v4 * v6 * v1257 + 24 * u * v3 * v4 * v6 * v1257 -
                    6 * u * v34 * v6 * v1257 + 2 * u4 * v36 * v1257 -
                    6 * u * v4 * v36 * v1257 + 2 * u3 * v46 * v1257 -
                    6 * u * v3 * v46 * v1257 + 2 * u * v346 * v1257 -
                    u1246 * v357 + 2 * u246 * v1 * v357 + 2 * u146 * v2 * v357 -
                    6 * u46 * v1 * v2 * v357 + 2 * u46 * v12 * v357 +
                    2 * u126 * v4 * v357 - 6 * u26 * v1 * v4 * v357 -
                    6 * u16 * v2 * v4 * v357 + 24 * u6 * v1 * v2 * v4 * v357 -
                    6 * u6 * v12 * v4 * v357 + 2 * u26 * v14 * v357 -
                    6 * u6 * v2 * v14 * v357 + 2 * u16 * v24 * v357 -
                    6 * u6 * v1 * v24 * v357 + 2 * u6 * v124 * v357 +
                    2 * u124 * v6 * v357 - 6 * u24 * v1 * v6 * v357 -
                    6 * u14 * v2 * v6 * v357 + 24 * u4 * v1 * v2 * v6 * v357 -
                    6 * u4 * v12 * v6 * v357 - 6 * u12 * v4 * v6 * v357 +
                    24 * u2 * v1 * v4 * v6 * v357 +
                    24 * u1 * v2 * v4 * v6 * v357 -
                    120 * u * v1 * v2 * v4 * v6 * v357 +
                    24 * u * v12 * v4 * v6 * v357 - 6 * u2 * v14 * v6 * v357 +
                    24 * u * v2 * v14 * v6 * v357 - 6 * u1 * v24 * v6 * v357 +
                    24 * u * v1 * v24 * v6 * v357 - 6 * u * v124 * v6 * v357 +
                    2 * u24 * v16 * v357 - 6 * u4 * v2 * v16 * v357 -
                    6 * u2 * v4 * v16 * v357 + 24 * u * v2 * v4 * v16 * v357 -
                    6 * u * v24 * v16 * v357 + 2 * u14 * v26 * v357 -
                    6 * u4 * v1 * v26 * v357 - 6 * u1 * v4 * v26 * v357 +
                    24 * u * v1 * v4 * v26 * v357 - 6 * u * v14 * v26 * v357 +
                    2 * u4 * v126 * v357 - 6 * u * v4 * v126 * v357 +
                    2 * u12 * v46 * v357 - 6 * u2 * v1 * v46 * v357 -
                    6 * u1 * v2 * v46 * v357 + 24 * u * v1 * v2 * v46 * v357 -
                    6 * u * v12 * v46 * v357 + 2 * u2 * v146 * v357 -
                    6 * u * v2 * v146 * v357 + 2 * u1 * v246 * v357 -
                    6 * u * v1 * v246 * v357 + 2 * u * v1246 * v357 -
                    u246 * v1357 + 2 * u46 * v2 * v1357 + 2 * u26 * v4 * v1357 -
                    6 * u6 * v2 * v4 * v1357 + 2 * u6 * v24 * v1357 +
                    2 * u24 * v6 * v1357 - 6 * u4 * v2 * v6 * v1357 -
                    6 * u2 * v4 * v6 * v1357 + 24 * u * v2 * v4 * v6 * v1357 -
                    6 * u * v24 * v6 * v1357 + 2 * u4 * v26 * v1357 -
                    6 * u * v4 * v26 * v1357 + 2 * u2 * v46 * v1357 -
                    6 * u * v2 * v46 * v1357 + 2 * u * v246 * v1357 -
                    u146 * v2357 + 2 * u46 * v1 * v2357 + 2 * u16 * v4 * v2357 -
                    6 * u6 * v1 * v4 * v2357 + 2 * u6 * v14 * v2357 +
                    2 * u14 * v6 * v2357 - 6 * u4 * v1 * v6 * v2357 -
                    6 * u1 * v4 * v6 * v2357 + 24 * u * v1 * v4 * v6 * v2357 -
                    6 * u * v14 * v6 * v2357 + 2 * u4 * v16 * v2357 -
                    6 * u * v4 * v16 * v2357 + 2 * u1 * v46 * v2357 -
                    6 * u * v1 * v46 * v2357 + 2 * u * v146 * v2357 -
                    u46 * v12357 + 2 * u6 * v4 * v12357 + 2 * u4 * v6 * v12357 -
                    6 * u * v4 * v6 * v12357 + 2 * u * v46 * v12357 -
                    u1236 * v457 + 2 * u236 * v1 * v457 + 2 * u136 * v2 * v457 -
                    6 * u36 * v1 * v2 * v457 + 2 * u36 * v12 * v457 +
                    2 * u126 * v3 * v457 - 6 * u26 * v1 * v3 * v457 -
                    6 * u16 * v2 * v3 * v457 + 24 * u6 * v1 * v2 * v3 * v457 -
                    6 * u6 * v12 * v3 * v457 + 2 * u26 * v13 * v457 -
                    6 * u6 * v2 * v13 * v457 + 2 * u16 * v23 * v457 -
                    6 * u6 * v1 * v23 * v457 + 2 * u6 * v123 * v457 +
                    2 * u123 * v6 * v457 - 6 * u23 * v1 * v6 * v457 -
                    6 * u13 * v2 * v6 * v457 + 24 * u3 * v1 * v2 * v6 * v457 -
                    6 * u3 * v12 * v6 * v457 - 6 * u12 * v3 * v6 * v457 +
                    24 * u2 * v1 * v3 * v6 * v457 +
                    24 * u1 * v2 * v3 * v6 * v457 -
                    120 * u * v1 * v2 * v3 * v6 * v457 +
                    24 * u * v12 * v3 * v6 * v457 - 6 * u2 * v13 * v6 * v457 +
                    24 * u * v2 * v13 * v6 * v457 - 6 * u1 * v23 * v6 * v457 +
                    24 * u * v1 * v23 * v6 * v457 - 6 * u * v123 * v6 * v457 +
                    2 * u23 * v16 * v457 - 6 * u3 * v2 * v16 * v457 -
                    6 * u2 * v3 * v16 * v457 + 24 * u * v2 * v3 * v16 * v457 -
                    6 * u * v23 * v16 * v457 + 2 * u13 * v26 * v457 -
                    6 * u3 * v1 * v26 * v457 - 6 * u1 * v3 * v26 * v457 +
                    24 * u * v1 * v3 * v26 * v457 - 6 * u * v13 * v26 * v457 +
                    2 * u3 * v126 * v457 - 6 * u * v3 * v126 * v457 +
                    2 * u12 * v36 * v457 - 6 * u2 * v1 * v36 * v457 -
                    6 * u1 * v2 * v36 * v457 + 24 * u * v1 * v2 * v36 * v457 -
                    6 * u * v12 * v36 * v457 + 2 * u2 * v136 * v457 -
                    6 * u * v2 * v136 * v457 + 2 * u1 * v236 * v457 -
                    6 * u * v1 * v236 * v457 + 2 * u * v1236 * v457 -
                    u236 * v1457 + 2 * u36 * v2 * v1457 + 2 * u26 * v3 * v1457 -
                    6 * u6 * v2 * v3 * v1457 + 2 * u6 * v23 * v1457 +
                    2 * u23 * v6 * v1457 - 6 * u3 * v2 * v6 * v1457 -
                    6 * u2 * v3 * v6 * v1457 + 24 * u * v2 * v3 * v6 * v1457 -
                    6 * u * v23 * v6 * v1457 + 2 * u3 * v26 * v1457 -
                    6 * u * v3 * v26 * v1457 + 2 * u2 * v36 * v1457 -
                    6 * u * v2 * v36 * v1457 + 2 * u * v236 * v1457 -
                    u136 * v2457 + 2 * u36 * v1 * v2457 + 2 * u16 * v3 * v2457 -
                    6 * u6 * v1 * v3 * v2457 + 2 * u6 * v13 * v2457 +
                    2 * u13 * v6 * v2457 - 6 * u3 * v1 * v6 * v2457 -
                    6 * u1 * v3 * v6 * v2457 + 24 * u * v1 * v3 * v6 * v2457 -
                    6 * u * v13 * v6 * v2457 + 2 * u3 * v16 * v2457 -
                    6 * u * v3 * v16 * v2457 + 2 * u1 * v36 * v2457 -
                    6 * u * v1 * v36 * v2457 + 2 * u * v136 * v2457 -
                    u36 * v12457 + 2 * u6 * v3 * v12457 + 2 * u3 * v6 * v12457 -
                    6 * u * v3 * v6 * v12457 + 2 * u * v36 * v12457 -
                    u126 * v3457 + 2 * u26 * v1 * v3457 + 2 * u16 * v2 * v3457 -
                    6 * u6 * v1 * v2 * v3457 + 2 * u6 * v12 * v3457 +
                    2 * u12 * v6 * v3457 - 6 * u2 * v1 * v6 * v3457 -
                    6 * u1 * v2 * v6 * v3457 + 24 * u * v1 * v2 * v6 * v3457 -
                    6 * u * v12 * v6 * v3457 + 2 * u2 * v16 * v3457 -
                    6 * u * v2 * v16 * v3457 + 2 * u1 * v26 * v3457 -
                    6 * u * v1 * v26 * v3457 + 2 * u * v126 * v3457 -
                    u26 * v13457 + 2 * u6 * v2 * v13457 + 2 * u2 * v6 * v13457 -
                    6 * u * v2 * v6 * v13457 + 2 * u * v26 * v13457 -
                    u16 * v23457 + 2 * u6 * v1 * v23457 + 2 * u1 * v6 * v23457 -
                    6 * u * v1 * v6 * v23457 + 2 * u * v16 * v23457 -
                    u6 * v123457 + 2 * u * v6 * v123457 - u12345 * v67 +
                    2 * u2345 * v1 * v67 + 2 * u1345 * v2 * v67 -
                    6 * u345 * v1 * v2 * v67 + 2 * u345 * v12 * v67 +
                    2 * u1245 * v3 * v67 - 6 * u245 * v1 * v3 * v67 -
                    6 * u145 * v2 * v3 * v67 + 24 * u45 * v1 * v2 * v3 * v67 -
                    6 * u45 * v12 * v3 * v67 + 2 * u245 * v13 * v67 -
                    6 * u45 * v2 * v13 * v67 + 2 * u145 * v23 * v67 -
                    6 * u45 * v1 * v23 * v67 + 2 * u45 * v123 * v67 +
                    2 * u1235 * v4 * v67 - 6 * u235 * v1 * v4 * v67 -
                    6 * u135 * v2 * v4 * v67 + 24 * u35 * v1 * v2 * v4 * v67 -
                    6 * u35 * v12 * v4 * v67 - 6 * u125 * v3 * v4 * v67 +
                    24 * u25 * v1 * v3 * v4 * v67 +
                    24 * u15 * v2 * v3 * v4 * v67 -
                    120 * u5 * v1 * v2 * v3 * v4 * v67 +
                    24 * u5 * v12 * v3 * v4 * v67 - 6 * u25 * v13 * v4 * v67 +
                    24 * u5 * v2 * v13 * v4 * v67 - 6 * u15 * v23 * v4 * v67 +
                    24 * u5 * v1 * v23 * v4 * v67 - 6 * u5 * v123 * v4 * v67 +
                    2 * u235 * v14 * v67 - 6 * u35 * v2 * v14 * v67 -
                    6 * u25 * v3 * v14 * v67 + 24 * u5 * v2 * v3 * v14 * v67 -
                    6 * u5 * v23 * v14 * v67 + 2 * u135 * v24 * v67 -
                    6 * u35 * v1 * v24 * v67 - 6 * u15 * v3 * v24 * v67 +
                    24 * u5 * v1 * v3 * v24 * v67 - 6 * u5 * v13 * v24 * v67 +
                    2 * u35 * v124 * v67 - 6 * u5 * v3 * v124 * v67 +
                    2 * u125 * v34 * v67 - 6 * u25 * v1 * v34 * v67 -
                    6 * u15 * v2 * v34 * v67 + 24 * u5 * v1 * v2 * v34 * v67 -
                    6 * u5 * v12 * v34 * v67 + 2 * u25 * v134 * v67 -
                    6 * u5 * v2 * v134 * v67 + 2 * u15 * v234 * v67 -
                    6 * u5 * v1 * v234 * v67 + 2 * u5 * v1234 * v67 +
                    2 * u1234 * v5 * v67 - 6 * u234 * v1 * v5 * v67 -
                    6 * u134 * v2 * v5 * v67 + 24 * u34 * v1 * v2 * v5 * v67 -
                    6 * u34 * v12 * v5 * v67 - 6 * u124 * v3 * v5 * v67 +
                    24 * u24 * v1 * v3 * v5 * v67 +
                    24 * u14 * v2 * v3 * v5 * v67 -
                    120 * u4 * v1 * v2 * v3 * v5 * v67 +
                    24 * u4 * v12 * v3 * v5 * v67 - 6 * u24 * v13 * v5 * v67 +
                    24 * u4 * v2 * v13 * v5 * v67 - 6 * u14 * v23 * v5 * v67 +
                    24 * u4 * v1 * v23 * v5 * v67 - 6 * u4 * v123 * v5 * v67 -
                    6 * u123 * v4 * v5 * v67 + 24 * u23 * v1 * v4 * v5 * v67 +
                    24 * u13 * v2 * v4 * v5 * v67 -
                    120 * u3 * v1 * v2 * v4 * v5 * v67 +
                    24 * u3 * v12 * v4 * v5 * v67 +
                    24 * u12 * v3 * v4 * v5 * v67 -
                    120 * u2 * v1 * v3 * v4 * v5 * v67 -
                    120 * u1 * v2 * v3 * v4 * v5 * v67 +
                    720 * u * v1 * v2 * v3 * v4 * v5 * v67 -
                    120 * u * v12 * v3 * v4 * v5 * v67 +
                    24 * u2 * v13 * v4 * v5 * v67 -
                    120 * u * v2 * v13 * v4 * v5 * v67 +
                    24 * u1 * v23 * v4 * v5 * v67 -
                    120 * u * v1 * v23 * v4 * v5 * v67 +
                    24 * u * v123 * v4 * v5 * v67 - 6 * u23 * v14 * v5 * v67 +
                    24 * u3 * v2 * v14 * v5 * v67 +
                    24 * u2 * v3 * v14 * v5 * v67 -
                    120 * u * v2 * v3 * v14 * v5 * v67 +
                    24 * u * v23 * v14 * v5 * v67 - 6 * u13 * v24 * v5 * v67 +
                    24 * u3 * v1 * v24 * v5 * v67 +
                    24 * u1 * v3 * v24 * v5 * v67 -
                    120 * u * v1 * v3 * v24 * v5 * v67 +
                    24 * u * v13 * v24 * v5 * v67 - 6 * u3 * v124 * v5 * v67 +
                    24 * u * v3 * v124 * v5 * v67 - 6 * u12 * v34 * v5 * v67 +
                    24 * u2 * v1 * v34 * v5 * v67 +
                    24 * u1 * v2 * v34 * v5 * v67 -
                    120 * u * v1 * v2 * v34 * v5 * v67 +
                    24 * u * v12 * v34 * v5 * v67 - 6 * u2 * v134 * v5 * v67 +
                    24 * u * v2 * v134 * v5 * v67 - 6 * u1 * v234 * v5 * v67 +
                    24 * u * v1 * v234 * v5 * v67 - 6 * u * v1234 * v5 * v67 +
                    2 * u234 * v15 * v67 - 6 * u34 * v2 * v15 * v67 -
                    6 * u24 * v3 * v15 * v67 + 24 * u4 * v2 * v3 * v15 * v67 -
                    6 * u4 * v23 * v15 * v67 - 6 * u23 * v4 * v15 * v67 +
                    24 * u3 * v2 * v4 * v15 * v67 +
                    24 * u2 * v3 * v4 * v15 * v67 -
                    120 * u * v2 * v3 * v4 * v15 * v67 +
                    24 * u * v23 * v4 * v15 * v67 - 6 * u3 * v24 * v15 * v67 +
                    24 * u * v3 * v24 * v15 * v67 - 6 * u2 * v34 * v15 * v67 +
                    24 * u * v2 * v34 * v15 * v67 - 6 * u * v234 * v15 * v67 +
                    2 * u134 * v25 * v67 - 6 * u34 * v1 * v25 * v67 -
                    6 * u14 * v3 * v25 * v67 + 24 * u4 * v1 * v3 * v25 * v67 -
                    6 * u4 * v13 * v25 * v67 - 6 * u13 * v4 * v25 * v67 +
                    24 * u3 * v1 * v4 * v25 * v67 +
                    24 * u1 * v3 * v4 * v25 * v67 -
                    120 * u * v1 * v3 * v4 * v25 * v67 +
                    24 * u * v13 * v4 * v25 * v67 - 6 * u3 * v14 * v25 * v67 +
                    24 * u * v3 * v14 * v25 * v67 - 6 * u1 * v34 * v25 * v67 +
                    24 * u * v1 * v34 * v25 * v67 - 6 * u * v134 * v25 * v67 +
                    2 * u34 * v125 * v67 - 6 * u4 * v3 * v125 * v67 -
                    6 * u3 * v4 * v125 * v67 + 24 * u * v3 * v4 * v125 * v67 -
                    6 * u * v34 * v125 * v67 + 2 * u124 * v35 * v67 -
                    6 * u24 * v1 * v35 * v67 - 6 * u14 * v2 * v35 * v67 +
                    24 * u4 * v1 * v2 * v35 * v67 - 6 * u4 * v12 * v35 * v67 -
                    6 * u12 * v4 * v35 * v67 + 24 * u2 * v1 * v4 * v35 * v67 +
                    24 * u1 * v2 * v4 * v35 * v67 -
                    120 * u * v1 * v2 * v4 * v35 * v67 +
                    24 * u * v12 * v4 * v35 * v67 - 6 * u2 * v14 * v35 * v67 +
                    24 * u * v2 * v14 * v35 * v67 - 6 * u1 * v24 * v35 * v67 +
                    24 * u * v1 * v24 * v35 * v67 - 6 * u * v124 * v35 * v67 +
                    2 * u24 * v135 * v67 - 6 * u4 * v2 * v135 * v67 -
                    6 * u2 * v4 * v135 * v67 + 24 * u * v2 * v4 * v135 * v67 -
                    6 * u * v24 * v135 * v67 + 2 * u14 * v235 * v67 -
                    6 * u4 * v1 * v235 * v67 - 6 * u1 * v4 * v235 * v67 +
                    24 * u * v1 * v4 * v235 * v67 - 6 * u * v14 * v235 * v67 +
                    2 * u4 * v1235 * v67 - 6 * u * v4 * v1235 * v67 +
                    2 * u123 * v45 * v67 - 6 * u23 * v1 * v45 * v67 -
                    6 * u13 * v2 * v45 * v67 + 24 * u3 * v1 * v2 * v45 * v67 -
                    6 * u3 * v12 * v45 * v67 - 6 * u12 * v3 * v45 * v67 +
                    24 * u2 * v1 * v3 * v45 * v67 +
                    24 * u1 * v2 * v3 * v45 * v67 -
                    120 * u * v1 * v2 * v3 * v45 * v67 +
                    24 * u * v12 * v3 * v45 * v67 - 6 * u2 * v13 * v45 * v67 +
                    24 * u * v2 * v13 * v45 * v67 - 6 * u1 * v23 * v45 * v67 +
                    24 * u * v1 * v23 * v45 * v67 - 6 * u * v123 * v45 * v67 +
                    2 * u23 * v145 * v67 - 6 * u3 * v2 * v145 * v67 -
                    6 * u2 * v3 * v145 * v67 + 24 * u * v2 * v3 * v145 * v67 -
                    6 * u * v23 * v145 * v67 + 2 * u13 * v245 * v67 -
                    6 * u3 * v1 * v245 * v67 - 6 * u1 * v3 * v245 * v67 +
                    24 * u * v1 * v3 * v245 * v67 - 6 * u * v13 * v245 * v67 +
                    2 * u3 * v1245 * v67 - 6 * u * v3 * v1245 * v67 +
                    2 * u12 * v345 * v67 - 6 * u2 * v1 * v345 * v67 -
                    6 * u1 * v2 * v345 * v67 + 24 * u * v1 * v2 * v345 * v67 -
                    6 * u * v12 * v345 * v67 + 2 * u2 * v1345 * v67 -
                    6 * u * v2 * v1345 * v67 + 2 * u1 * v2345 * v67 -
                    6 * u * v1 * v2345 * v67 + 2 * u * v12345 * v67 -
                    u2345 * v167 + 2 * u345 * v2 * v167 + 2 * u245 * v3 * v167 -
                    6 * u45 * v2 * v3 * v167 + 2 * u45 * v23 * v167 +
                    2 * u235 * v4 * v167 - 6 * u35 * v2 * v4 * v167 -
                    6 * u25 * v3 * v4 * v167 + 24 * u5 * v2 * v3 * v4 * v167 -
                    6 * u5 * v23 * v4 * v167 + 2 * u35 * v24 * v167 -
                    6 * u5 * v3 * v24 * v167 + 2 * u25 * v34 * v167 -
                    6 * u5 * v2 * v34 * v167 + 2 * u5 * v234 * v167 +
                    2 * u234 * v5 * v167 - 6 * u34 * v2 * v5 * v167 -
                    6 * u24 * v3 * v5 * v167 + 24 * u4 * v2 * v3 * v5 * v167 -
                    6 * u4 * v23 * v5 * v167 - 6 * u23 * v4 * v5 * v167 +
                    24 * u3 * v2 * v4 * v5 * v167 +
                    24 * u2 * v3 * v4 * v5 * v167 -
                    120 * u * v2 * v3 * v4 * v5 * v167 +
                    24 * u * v23 * v4 * v5 * v167 - 6 * u3 * v24 * v5 * v167 +
                    24 * u * v3 * v24 * v5 * v167 - 6 * u2 * v34 * v5 * v167 +
                    24 * u * v2 * v34 * v5 * v167 - 6 * u * v234 * v5 * v167 +
                    2 * u34 * v25 * v167 - 6 * u4 * v3 * v25 * v167 -
                    6 * u3 * v4 * v25 * v167 + 24 * u * v3 * v4 * v25 * v167 -
                    6 * u * v34 * v25 * v167 + 2 * u24 * v35 * v167 -
                    6 * u4 * v2 * v35 * v167 - 6 * u2 * v4 * v35 * v167 +
                    24 * u * v2 * v4 * v35 * v167 - 6 * u * v24 * v35 * v167 +
                    2 * u4 * v235 * v167 - 6 * u * v4 * v235 * v167 +
                    2 * u23 * v45 * v167 - 6 * u3 * v2 * v45 * v167 -
                    6 * u2 * v3 * v45 * v167 + 24 * u * v2 * v3 * v45 * v167 -
                    6 * u * v23 * v45 * v167 + 2 * u3 * v245 * v167 -
                    6 * u * v3 * v245 * v167 + 2 * u2 * v345 * v167 -
                    6 * u * v2 * v345 * v167 + 2 * u * v2345 * v167 -
                    u1345 * v267 + 2 * u345 * v1 * v267 + 2 * u145 * v3 * v267 -
                    6 * u45 * v1 * v3 * v267 + 2 * u45 * v13 * v267 +
                    2 * u135 * v4 * v267 - 6 * u35 * v1 * v4 * v267 -
                    6 * u15 * v3 * v4 * v267 + 24 * u5 * v1 * v3 * v4 * v267 -
                    6 * u5 * v13 * v4 * v267 + 2 * u35 * v14 * v267 -
                    6 * u5 * v3 * v14 * v267 + 2 * u15 * v34 * v267 -
                    6 * u5 * v1 * v34 * v267 + 2 * u5 * v134 * v267 +
                    2 * u134 * v5 * v267 - 6 * u34 * v1 * v5 * v267 -
                    6 * u14 * v3 * v5 * v267 + 24 * u4 * v1 * v3 * v5 * v267 -
                    6 * u4 * v13 * v5 * v267 - 6 * u13 * v4 * v5 * v267 +
                    24 * u3 * v1 * v4 * v5 * v267 +
                    24 * u1 * v3 * v4 * v5 * v267 -
                    120 * u * v1 * v3 * v4 * v5 * v267 +
                    24 * u * v13 * v4 * v5 * v267 - 6 * u3 * v14 * v5 * v267 +
                    24 * u * v3 * v14 * v5 * v267 - 6 * u1 * v34 * v5 * v267 +
                    24 * u * v1 * v34 * v5 * v267 - 6 * u * v134 * v5 * v267 +
                    2 * u34 * v15 * v267 - 6 * u4 * v3 * v15 * v267 -
                    6 * u3 * v4 * v15 * v267 + 24 * u * v3 * v4 * v15 * v267 -
                    6 * u * v34 * v15 * v267 + 2 * u14 * v35 * v267 -
                    6 * u4 * v1 * v35 * v267 - 6 * u1 * v4 * v35 * v267 +
                    24 * u * v1 * v4 * v35 * v267 - 6 * u * v14 * v35 * v267 +
                    2 * u4 * v135 * v267 - 6 * u * v4 * v135 * v267 +
                    2 * u13 * v45 * v267 - 6 * u3 * v1 * v45 * v267 -
                    6 * u1 * v3 * v45 * v267 + 24 * u * v1 * v3 * v45 * v267 -
                    6 * u * v13 * v45 * v267 + 2 * u3 * v145 * v267 -
                    6 * u * v3 * v145 * v267 + 2 * u1 * v345 * v267 -
                    6 * u * v1 * v345 * v267 + 2 * u * v1345 * v267 -
                    u345 * v1267 + 2 * u45 * v3 * v1267 + 2 * u35 * v4 * v1267 -
                    6 * u5 * v3 * v4 * v1267 + 2 * u5 * v34 * v1267 +
                    2 * u34 * v5 * v1267 - 6 * u4 * v3 * v5 * v1267 -
                    6 * u3 * v4 * v5 * v1267 + 24 * u * v3 * v4 * v5 * v1267 -
                    6 * u * v34 * v5 * v1267 + 2 * u4 * v35 * v1267 -
                    6 * u * v4 * v35 * v1267 + 2 * u3 * v45 * v1267 -
                    6 * u * v3 * v45 * v1267 + 2 * u * v345 * v1267 -
                    u1245 * v367 + 2 * u245 * v1 * v367 + 2 * u145 * v2 * v367 -
                    6 * u45 * v1 * v2 * v367 + 2 * u45 * v12 * v367 +
                    2 * u125 * v4 * v367 - 6 * u25 * v1 * v4 * v367 -
                    6 * u15 * v2 * v4 * v367 + 24 * u5 * v1 * v2 * v4 * v367 -
                    6 * u5 * v12 * v4 * v367 + 2 * u25 * v14 * v367 -
                    6 * u5 * v2 * v14 * v367 + 2 * u15 * v24 * v367 -
                    6 * u5 * v1 * v24 * v367 + 2 * u5 * v124 * v367 +
                    2 * u124 * v5 * v367 - 6 * u24 * v1 * v5 * v367 -
                    6 * u14 * v2 * v5 * v367 + 24 * u4 * v1 * v2 * v5 * v367 -
                    6 * u4 * v12 * v5 * v367 - 6 * u12 * v4 * v5 * v367 +
                    24 * u2 * v1 * v4 * v5 * v367 +
                    24 * u1 * v2 * v4 * v5 * v367 -
                    120 * u * v1 * v2 * v4 * v5 * v367 +
                    24 * u * v12 * v4 * v5 * v367 - 6 * u2 * v14 * v5 * v367 +
                    24 * u * v2 * v14 * v5 * v367 - 6 * u1 * v24 * v5 * v367 +
                    24 * u * v1 * v24 * v5 * v367 - 6 * u * v124 * v5 * v367 +
                    2 * u24 * v15 * v367 - 6 * u4 * v2 * v15 * v367 -
                    6 * u2 * v4 * v15 * v367 + 24 * u * v2 * v4 * v15 * v367 -
                    6 * u * v24 * v15 * v367 + 2 * u14 * v25 * v367 -
                    6 * u4 * v1 * v25 * v367 - 6 * u1 * v4 * v25 * v367 +
                    24 * u * v1 * v4 * v25 * v367 - 6 * u * v14 * v25 * v367 +
                    2 * u4 * v125 * v367 - 6 * u * v4 * v125 * v367 +
                    2 * u12 * v45 * v367 - 6 * u2 * v1 * v45 * v367 -
                    6 * u1 * v2 * v45 * v367 + 24 * u * v1 * v2 * v45 * v367 -
                    6 * u * v12 * v45 * v367 + 2 * u2 * v145 * v367 -
                    6 * u * v2 * v145 * v367 + 2 * u1 * v245 * v367 -
                    6 * u * v1 * v245 * v367 + 2 * u * v1245 * v367 -
                    u245 * v1367 + 2 * u45 * v2 * v1367 + 2 * u25 * v4 * v1367 -
                    6 * u5 * v2 * v4 * v1367 + 2 * u5 * v24 * v1367 +
                    2 * u24 * v5 * v1367 - 6 * u4 * v2 * v5 * v1367 -
                    6 * u2 * v4 * v5 * v1367 + 24 * u * v2 * v4 * v5 * v1367 -
                    6 * u * v24 * v5 * v1367 + 2 * u4 * v25 * v1367 -
                    6 * u * v4 * v25 * v1367 + 2 * u2 * v45 * v1367 -
                    6 * u * v2 * v45 * v1367 + 2 * u * v245 * v1367 -
                    u145 * v2367 + 2 * u45 * v1 * v2367 + 2 * u15 * v4 * v2367 -
                    6 * u5 * v1 * v4 * v2367 + 2 * u5 * v14 * v2367 +
                    2 * u14 * v5 * v2367 - 6 * u4 * v1 * v5 * v2367 -
                    6 * u1 * v4 * v5 * v2367 + 24 * u * v1 * v4 * v5 * v2367 -
                    6 * u * v14 * v5 * v2367 + 2 * u4 * v15 * v2367 -
                    6 * u * v4 * v15 * v2367 + 2 * u1 * v45 * v2367 -
                    6 * u * v1 * v45 * v2367 + 2 * u * v145 * v2367 -
                    u45 * v12367 + 2 * u5 * v4 * v12367 + 2 * u4 * v5 * v12367 -
                    6 * u * v4 * v5 * v12367 + 2 * u * v45 * v12367 -
                    u1235 * v467 + 2 * u235 * v1 * v467 + 2 * u135 * v2 * v467 -
                    6 * u35 * v1 * v2 * v467 + 2 * u35 * v12 * v467 +
                    2 * u125 * v3 * v467 - 6 * u25 * v1 * v3 * v467 -
                    6 * u15 * v2 * v3 * v467 + 24 * u5 * v1 * v2 * v3 * v467 -
                    6 * u5 * v12 * v3 * v467 + 2 * u25 * v13 * v467 -
                    6 * u5 * v2 * v13 * v467 + 2 * u15 * v23 * v467 -
                    6 * u5 * v1 * v23 * v467 + 2 * u5 * v123 * v467 +
                    2 * u123 * v5 * v467 - 6 * u23 * v1 * v5 * v467 -
                    6 * u13 * v2 * v5 * v467 + 24 * u3 * v1 * v2 * v5 * v467 -
                    6 * u3 * v12 * v5 * v467 - 6 * u12 * v3 * v5 * v467 +
                    24 * u2 * v1 * v3 * v5 * v467 +
                    24 * u1 * v2 * v3 * v5 * v467 -
                    120 * u * v1 * v2 * v3 * v5 * v467 +
                    24 * u * v12 * v3 * v5 * v467 - 6 * u2 * v13 * v5 * v467 +
                    24 * u * v2 * v13 * v5 * v467 - 6 * u1 * v23 * v5 * v467 +
                    24 * u * v1 * v23 * v5 * v467 - 6 * u * v123 * v5 * v467 +
                    2 * u23 * v15 * v467 - 6 * u3 * v2 * v15 * v467 -
                    6 * u2 * v3 * v15 * v467 + 24 * u * v2 * v3 * v15 * v467 -
                    6 * u * v23 * v15 * v467 + 2 * u13 * v25 * v467 -
                    6 * u3 * v1 * v25 * v467 - 6 * u1 * v3 * v25 * v467 +
                    24 * u * v1 * v3 * v25 * v467 - 6 * u * v13 * v25 * v467 +
                    2 * u3 * v125 * v467 - 6 * u * v3 * v125 * v467 +
                    2 * u12 * v35 * v467 - 6 * u2 * v1 * v35 * v467 -
                    6 * u1 * v2 * v35 * v467 + 24 * u * v1 * v2 * v35 * v467 -
                    6 * u * v12 * v35 * v467 + 2 * u2 * v135 * v467 -
                    6 * u * v2 * v135 * v467 + 2 * u1 * v235 * v467 -
                    6 * u * v1 * v235 * v467 + 2 * u * v1235 * v467 -
                    u235 * v1467 + 2 * u35 * v2 * v1467 + 2 * u25 * v3 * v1467 -
                    6 * u5 * v2 * v3 * v1467 + 2 * u5 * v23 * v1467 +
                    2 * u23 * v5 * v1467 - 6 * u3 * v2 * v5 * v1467 -
                    6 * u2 * v3 * v5 * v1467 + 24 * u * v2 * v3 * v5 * v1467 -
                    6 * u * v23 * v5 * v1467 + 2 * u3 * v25 * v1467 -
                    6 * u * v3 * v25 * v1467 + 2 * u2 * v35 * v1467 -
                    6 * u * v2 * v35 * v1467 + 2 * u * v235 * v1467 -
                    u135 * v2467 + 2 * u35 * v1 * v2467 + 2 * u15 * v3 * v2467 -
                    6 * u5 * v1 * v3 * v2467 + 2 * u5 * v13 * v2467 +
                    2 * u13 * v5 * v2467 - 6 * u3 * v1 * v5 * v2467 -
                    6 * u1 * v3 * v5 * v2467 + 24 * u * v1 * v3 * v5 * v2467 -
                    6 * u * v13 * v5 * v2467 + 2 * u3 * v15 * v2467 -
                    6 * u * v3 * v15 * v2467 + 2 * u1 * v35 * v2467 -
                    6 * u * v1 * v35 * v2467 + 2 * u * v135 * v2467 -
                    u35 * v12467 + 2 * u5 * v3 * v12467 + 2 * u3 * v5 * v12467 -
                    6 * u * v3 * v5 * v12467 + 2 * u * v35 * v12467 -
                    u125 * v3467 + 2 * u25 * v1 * v3467 + 2 * u15 * v2 * v3467 -
                    6 * u5 * v1 * v2 * v3467 + 2 * u5 * v12 * v3467 +
                    2 * u12 * v5 * v3467 - 6 * u2 * v1 * v5 * v3467 -
                    6 * u1 * v2 * v5 * v3467 + 24 * u * v1 * v2 * v5 * v3467 -
                    6 * u * v12 * v5 * v3467 + 2 * u2 * v15 * v3467 -
                    6 * u * v2 * v15 * v3467 + 2 * u1 * v25 * v3467 -
                    6 * u * v1 * v25 * v3467 + 2 * u * v125 * v3467 -
                    u25 * v13467 + 2 * u5 * v2 * v13467 + 2 * u2 * v5 * v13467 -
                    6 * u * v2 * v5 * v13467 + 2 * u * v25 * v13467 -
                    u15 * v23467 + 2 * u5 * v1 * v23467 + 2 * u1 * v5 * v23467 -
                    6 * u * v1 * v5 * v23467 + 2 * u * v15 * v23467 -
                    u5 * v123467 + 2 * u * v5 * v123467 - u1234 * v567 +
                    2 * u234 * v1 * v567 + 2 * u134 * v2 * v567 -
                    6 * u34 * v1 * v2 * v567 + 2 * u34 * v12 * v567 +
                    2 * u124 * v3 * v567 - 6 * u24 * v1 * v3 * v567 -
                    6 * u14 * v2 * v3 * v567 + 24 * u4 * v1 * v2 * v3 * v567 -
                    6 * u4 * v12 * v3 * v567 + 2 * u24 * v13 * v567 -
                    6 * u4 * v2 * v13 * v567 + 2 * u14 * v23 * v567 -
                    6 * u4 * v1 * v23 * v567 + 2 * u4 * v123 * v567 +
                    2 * u123 * v4 * v567 - 6 * u23 * v1 * v4 * v567 -
                    6 * u13 * v2 * v4 * v567 + 24 * u3 * v1 * v2 * v4 * v567 -
                    6 * u3 * v12 * v4 * v567 - 6 * u12 * v3 * v4 * v567 +
                    24 * u2 * v1 * v3 * v4 * v567 +
                    24 * u1 * v2 * v3 * v4 * v567 -
                    120 * u * v1 * v2 * v3 * v4 * v567 +
                    24 * u * v12 * v3 * v4 * v567 - 6 * u2 * v13 * v4 * v567 +
                    24 * u * v2 * v13 * v4 * v567 - 6 * u1 * v23 * v4 * v567 +
                    24 * u * v1 * v23 * v4 * v567 - 6 * u * v123 * v4 * v567 +
                    2 * u23 * v14 * v567 - 6 * u3 * v2 * v14 * v567 -
                    6 * u2 * v3 * v14 * v567 + 24 * u * v2 * v3 * v14 * v567 -
                    6 * u * v23 * v14 * v567 + 2 * u13 * v24 * v567 -
                    6 * u3 * v1 * v24 * v567 - 6 * u1 * v3 * v24 * v567 +
                    24 * u * v1 * v3 * v24 * v567 - 6 * u * v13 * v24 * v567 +
                    2 * u3 * v124 * v567 - 6 * u * v3 * v124 * v567 +
                    2 * u12 * v34 * v567 - 6 * u2 * v1 * v34 * v567 -
                    6 * u1 * v2 * v34 * v567 + 24 * u * v1 * v2 * v34 * v567 -
                    6 * u * v12 * v34 * v567 + 2 * u2 * v134 * v567 -
                    6 * u * v2 * v134 * v567 + 2 * u1 * v234 * v567 -
                    6 * u * v1 * v234 * v567 + 2 * u * v1234 * v567 -
                    u234 * v1567 + 2 * u34 * v2 * v1567 + 2 * u24 * v3 * v1567 -
                    6 * u4 * v2 * v3 * v1567 + 2 * u4 * v23 * v1567 +
                    2 * u23 * v4 * v1567 - 6 * u3 * v2 * v4 * v1567 -
                    6 * u2 * v3 * v4 * v1567 + 24 * u * v2 * v3 * v4 * v1567 -
                    6 * u * v23 * v4 * v1567 + 2 * u3 * v24 * v1567 -
                    6 * u * v3 * v24 * v1567 + 2 * u2 * v34 * v1567 -
                    6 * u * v2 * v34 * v1567 + 2 * u * v234 * v1567 -
                    u134 * v2567 + 2 * u34 * v1 * v2567 + 2 * u14 * v3 * v2567 -
                    6 * u4 * v1 * v3 * v2567 + 2 * u4 * v13 * v2567 +
                    2 * u13 * v4 * v2567 - 6 * u3 * v1 * v4 * v2567 -
                    6 * u1 * v3 * v4 * v2567 + 24 * u * v1 * v3 * v4 * v2567 -
                    6 * u * v13 * v4 * v2567 + 2 * u3 * v14 * v2567 -
                    6 * u * v3 * v14 * v2567 + 2 * u1 * v34 * v2567 -
                    6 * u * v1 * v34 * v2567 + 2 * u * v134 * v2567 -
                    u34 * v12567 + 2 * u4 * v3 * v12567 + 2 * u3 * v4 * v12567 -
                    6 * u * v3 * v4 * v12567 + 2 * u * v34 * v12567 -
                    u124 * v3567 + 2 * u24 * v1 * v3567 + 2 * u14 * v2 * v3567 -
                    6 * u4 * v1 * v2 * v3567 + 2 * u4 * v12 * v3567 +
                    2 * u12 * v4 * v3567 - 6 * u2 * v1 * v4 * v3567 -
                    6 * u1 * v2 * v4 * v3567 + 24 * u * v1 * v2 * v4 * v3567 -
                    6 * u * v12 * v4 * v3567 + 2 * u2 * v14 * v3567 -
                    6 * u * v2 * v14 * v3567 + 2 * u1 * v24 * v3567 -
                    6 * u * v1 * v24 * v3567 + 2 * u * v124 * v3567 -
                    u24 * v13567 + 2 * u4 * v2 * v13567 + 2 * u2 * v4 * v13567 -
                    6 * u * v2 * v4 * v13567 + 2 * u * v24 * v13567 -
                    u14 * v23567 + 2 * u4 * v1 * v23567 + 2 * u1 * v4 * v23567 -
                    6 * u * v1 * v4 * v23567 + 2 * u * v14 * v23567 -
                    u4 * v123567 + 2 * u * v4 * v123567 - u123 * v4567 +
                    2 * u23 * v1 * v4567 + 2 * u13 * v2 * v4567 -
                    6 * u3 * v1 * v2 * v4567 + 2 * u3 * v12 * v4567 +
                    2 * u12 * v3 * v4567 - 6 * u2 * v1 * v3 * v4567 -
                    6 * u1 * v2 * v3 * v4567 + 24 * u * v1 * v2 * v3 * v4567 -
                    6 * u * v12 * v3 * v4567 + 2 * u2 * v13 * v4567 -
                    6 * u * v2 * v13 * v4567 + 2 * u1 * v23 * v4567 -
                    6 * u * v1 * v23 * v4567 + 2 * u * v123 * v4567 -
                    u23 * v14567 + 2 * u3 * v2 * v14567 + 2 * u2 * v3 * v14567 -
                    6 * u * v2 * v3 * v14567 + 2 * u * v23 * v14567 -
                    u13 * v24567 + 2 * u3 * v1 * v24567 + 2 * u1 * v3 * v24567 -
                    6 * u * v1 * v3 * v24567 + 2 * u * v13 * v24567 -
                    u3 * v124567 + 2 * u * v3 * v124567 - u12 * v34567 +
                    2 * u2 * v1 * v34567 + 2 * u1 * v2 * v34567 -
                    6 * u * v1 * v2 * v34567 + 2 * u * v12 * v34567 -
                    u2 * v134567 + 2 * u * v2 * v134567 - u1 * v234567 +
                    2 * u * v1 * v234567 - u * v1234567,
    };
}

#endif // DZNL_HYPERDUAL7_H
