param(
    [Parameter(Mandatory = $true)][ValidateSet('baseline', 'candidate')][string] $Label,
    [Parameter(Mandatory = $true)][string] $UpstreamProject,
    [Parameter(Mandatory = $true)][string] $ToolchainBin
)

$ErrorActionPreference = 'Stop'
$routeRoot = Split-Path $PSScriptRoot -Parent
$evidenceRoot = Join-Path $routeRoot 'verification/interface-refactor'
$recordRoot = Join-Path $evidenceRoot $Label
New-Item -ItemType Directory -Path $recordRoot -Force | Out-Null
$savedPath = $env:PATH
$savedLeanPath = $env:LEAN_PATH
$env:PATH = $ToolchainBin + [IO.Path]::PathSeparator + $env:PATH
$env:LEAN_PATH = (Join-Path $routeRoot 'lean/.build') + [IO.Path]::PathSeparator + $savedLeanPath
$records = @()
Push-Location $UpstreamProject
try {
    foreach ($name in @('Regression', 'Dependencies')) {
        $source = Join-Path $evidenceRoot ($name + '.lean')
        $output = @(& lake env lean -R $evidenceRoot $source 2>&1)
        $code = $LASTEXITCODE
        [IO.File]::WriteAllText((Join-Path $recordRoot ($name.ToLowerInvariant() + '.log')),
            ($output -join "`n") + "`n", [Text.UTF8Encoding]::new($false))
        $records += [ordered]@{
            source = $name + '.lean'
            sha256 = (Get-FileHash -LiteralPath $source -Algorithm SHA256).Hash.ToLowerInvariant()
            exit_code = $code
        }
        if ($code -ne 0) { throw ($output -join "`n") }
        Write-Output "PASS: $Label $name"
    }
    [IO.File]::WriteAllText((Join-Path $recordRoot 'interface-regressions.json'),
        ([ordered]@{ status = 'passed'; label = $Label; checks = $records } | ConvertTo-Json -Depth 5) + "`n",
        [Text.UTF8Encoding]::new($false))
} finally {
    Pop-Location
    $env:PATH = $savedPath
    $env:LEAN_PATH = $savedLeanPath
}
