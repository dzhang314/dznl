Remove-Item -Path "bin" -Recurse -Force
New-Item -Path "bin" -ItemType "directory" -Force

$ClangWarningFlags = @(
    "-Weverything"
    "-Werror"
    "-Wfatal-errors"
    "-Wno-c++98-compat"
    "-Wno-c++98-compat-pedantic"
    "-Wno-unsafe-buffer-usage"
    "-Wno-float-equal"
    "-Wno-padded"
)

g++ -std=c++17 -Wall -Wextra -Werror -pedantic -pedantic-errors `
    -I. test\TestFloatingPointProperties.cpp -lCatch2Main -lCatch2 `
    -o bin\TestFloatingPointPropertiesGCC

.\bin\TestFloatingPointPropertiesGCC

clang++ -std=c++17 $ClangWarningFlags `
    -I. test\TestFloatingPointProperties.cpp -lCatch2Main -lCatch2 `
    -o bin\TestFloatingPointPropertiesClang

.\bin\TestFloatingPointPropertiesClang

g++ -std=c++17 -Wall -Wextra -Werror -pedantic -pedantic-errors `
    -I. test\TestRandomNumberGenerator.cpp -lCatch2Main -lCatch2 `
    -o bin\TestRandomNumberGeneratorGCC

.\bin\TestRandomNumberGeneratorGCC

clang++ -std=c++17 $ClangWarningFlags `
    -I. test\TestRandomNumberGenerator.cpp -lCatch2Main -lCatch2 `
    -o bin\TestRandomNumberGeneratorClang

.\bin\TestRandomNumberGeneratorClang

g++ -std=c++17 -Wall -Wextra -Werror -pedantic -pedantic-errors `
    -I. test\TestNelderMeadOptimizer.cpp -lCatch2Main -lCatch2 `
    -o bin\TestNelderMeadOptimizerGCC

.\bin\TestNelderMeadOptimizerGCC

clang++ -std=c++17 $ClangWarningFlags `
    -I. test\TestNelderMeadOptimizer.cpp -lCatch2Main -lCatch2 `
    -o bin\TestNelderMeadOptimizerClang

.\bin\TestNelderMeadOptimizerClang

g++ -std=c++17 -Wall -Wextra -Werror -pedantic -pedantic-errors `
    -I. test\TestNelderMeadOptimizerMut.cpp -lCatch2Main -lCatch2 `
    -o bin\TestNelderMeadOptimizerMutGCC

.\bin\TestNelderMeadOptimizerMutGCC

clang++ -std=c++17 $ClangWarningFlags `
    -I. test\TestNelderMeadOptimizerMut.cpp -lCatch2Main -lCatch2 `
    -o bin\TestNelderMeadOptimizerMutClang

.\bin\TestNelderMeadOptimizerMutClang
