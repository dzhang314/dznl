Import-Module "C:\Program Files\Microsoft Visual Studio\2022\Community\Common7\Tools\Microsoft.VisualStudio.DevShell.dll"
Enter-VsDevShell 08c4929b -DevCmdArguments "-arch=x64 -no_logo"

function Compile-And-Run-MSVC {
    param (
        [string]$sourceFile,
        [string]$outputFile
    )

    cl /nologo /std:c++17 /EHsc `
        /Wall /wd4514 /wd4577 /wd4820 /wd5045 `
        /external:W0 /external:I "C:\Programs\boost_1_87_0" /I . `
        $sourceFile /Fo:bin\ /Fe:$outputFile

    & $outputFile
    Write-Output "$outputFile : $LastExitCode"
}

function Compile-And-Run-GCC {
    param (
        [string]$sourceFile,
        [string]$outputFile
    )

    g++ -std=c++17 `
        -Wall -Wextra -pedantic -Werror `
        -isystem "C:\Programs\boost_1_87_0" -I . `
        $sourceFile -o $outputFile

    & $outputFile
    Write-Output "$outputFile : $LastExitCode"
}

function Compile-And-Run-Clang {
    param (
        [string]$sourceFile,
        [string]$outputFile
    )

    clang++ -std=c++17 `
        -Weverything -Werror `
        -Wno-padded `
        -Wno-float-equal `
        -Wno-c++98-compat `
        -Wno-c++98-compat-pedantic `
        -isystem "C:\Programs\boost_1_87_0" -I . `
        $sourceFile -o $outputFile

    & $outputFile
    Write-Output "$outputFile : $LastExitCode"
}

if (-Not (Test-Path -Path "bin")) {
    New-Item -ItemType Directory -Path "bin"
}

Compile-And-Run-MSVC test\TestArithmetic.cpp bin\TestArithmeticMSVC.exe
Compile-And-Run-GCC test\TestArithmetic.cpp bin\TestArithmeticGCC.exe
Compile-And-Run-Clang test\TestArithmetic.cpp bin\TestArithmeticClang.exe

Compile-And-Run-MSVC test\TestFloatingPoint.cpp bin\TestFloatingPointMSVC.exe
Compile-And-Run-GCC test\TestFloatingPoint.cpp bin\TestFloatingPointGCC.exe
Compile-And-Run-Clang test\TestFloatingPoint.cpp bin\TestFloatingPointClang.exe

Compile-And-Run-MSVC test\TestFloatToString.cpp bin\TestFloatToStringMSVC.exe
Compile-And-Run-GCC test\TestFloatToString.cpp bin\TestFloatToStringGCC.exe
Compile-And-Run-Clang test\TestFloatToString.cpp bin\TestFloatToStringClang.exe

Compile-And-Run-MSVC test\TestToHexString.cpp bin\TestToHexStringMSVC.exe
Compile-And-Run-GCC test\TestToHexString.cpp bin\TestToHexStringGCC.exe
Compile-And-Run-Clang test\TestToHexString.cpp bin\TestToHexStringClang.exe
