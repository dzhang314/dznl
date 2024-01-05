$CompilerFlags = @(
    "-std=c++17"
    "-I./"
)

$GccWarningFlags = @(
    "-Wall"
    "-Wextra"
    "-Wfatal-errors"
    "-pedantic"
    "-pedantic-errors"
)

$ClangWarningFlags = @(
    "-Weverything"
    "-Wfatal-errors"
    "-Wno-c++98-compat"
    "-Wno-c++98-compat-pedantic"
    "-Wno-unsafe-buffer-usage"
    "-Wno-float-equal"
    "-Wno-padded"
)

function CompileAndRun($testFile) {
    $testName = (Get-Item $testFile).BaseName
    $outputBase = Join-Path -Path "bin" -ChildPath $testName

    Write-Host $testName"GCC"
    g++ $CompilerFlags $GccWarningFlags $testFile -o $outputBase"GCC"
    if ($LastExitCode -ne 0) { exit $LastExitCode }
    & $outputBase"GCC" -q
    if ($LastExitCode -ne 0) { exit $LastExitCode }

    Write-Host $testName"Clang"
    clang++ $CompilerFlags $ClangWarningFlags $testFile -o $outputBase"Clang"
    if ($LastExitCode -ne 0) { exit $LastExitCode }
    & $outputBase"Clang" -q
    if ($LastExitCode -ne 0) { exit $LastExitCode }

    Write-Host $testName"GCCMut"
    g++ $CompilerFlags $GccWarningFlags -DDZNL_REMOVE_CONST $testFile -o $outputBase"GCCMut"
    if ($LastExitCode -ne 0) { exit $LastExitCode }
    & $outputBase"GCCMut" -q
    if ($LastExitCode -ne 0) { exit $LastExitCode }

    Write-Host $testName"ClangMut"
    clang++ $CompilerFlags $ClangWarningFlags -DDZNL_REMOVE_CONST $testFile -o $outputBase"ClangMut"
    if ($LastExitCode -ne 0) { exit $LastExitCode }
    & $outputBase"ClangMut" -q
    if ($LastExitCode -ne 0) { exit $LastExitCode }
}

Remove-Item -Path "bin" -Recurse -Force
New-Item -Path "bin" -ItemType "directory" -Force | Out-Null

foreach ($file in Get-ChildItem -Path "test" -Filter "*.cpp") {
    CompileAndRun $file.FullName
}
