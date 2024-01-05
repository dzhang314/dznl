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

function CompileAndRun($sourceFile) {

    $outputFileBase = Join-Path -Path "bin" `
        -ChildPath (Get-Item $sourceFile).BaseName

    g++ -std=c++17 $GccWarningFlags `
        -I. $sourceFile -lCatch2Main -lCatch2 `
        -o $outputFileBase"GCC"

    if ($LastExitCode -ne 0) { exit $LastExitCode }

    & $outputFileBase"GCC"

    if ($LastExitCode -ne 0) { exit $LastExitCode }

    clang++ -std=c++17 $ClangWarningFlags `
        -I. $sourceFile -lCatch2Main -lCatch2 `
        -o $outputFileBase"Clang"

    if ($LastExitCode -ne 0) { exit $LastExitCode }

    & $outputFileBase"Clang"

    if ($LastExitCode -ne 0) { exit $LastExitCode }

    g++ -std=c++17 $GccWarningFlags -DDZNL_REMOVE_CONST `
        -I. $sourceFile -lCatch2Main -lCatch2 `
        -o $outputFileBase"GCCMut"

    if ($LastExitCode -ne 0) { exit $LastExitCode }

    & $outputFileBase"GCCMut"

    if ($LastExitCode -ne 0) { exit $LastExitCode }

    clang++ -std=c++17 $ClangWarningFlags -DDZNL_REMOVE_CONST `
        -I. $sourceFile -lCatch2Main -lCatch2 `
        -o $outputFileBase"ClangMut"

    if ($LastExitCode -ne 0) { exit $LastExitCode }

    & $outputFileBase"ClangMut"

    if ($LastExitCode -ne 0) { exit $LastExitCode }

}

Remove-Item -Path "bin" -Recurse -Force
New-Item -Path "bin" -ItemType "directory" -Force

foreach ($file in Get-ChildItem -Path "test" -Filter "*.cpp") {
    CompileAndRun $file.FullName
}
