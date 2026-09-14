$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot
Push-Location -LiteralPath $projectRoot
try {
    python (Join-Path $PSScriptRoot 'verify.py')
    $verificationExit = $LASTEXITCODE
} finally {
    Pop-Location
}
exit $verificationExit
