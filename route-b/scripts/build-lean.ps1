param(
    [Parameter(Mandatory = $true)][string] $UpstreamProject,
    [Parameter(Mandatory = $true)][string] $ToolchainBin,
    [string] $Module = '',
    [switch] $Incremental
)

$ErrorActionPreference = 'Stop'
$routeRoot = Split-Path $PSScriptRoot -Parent
$researchRoot = Split-Path $routeRoot -Parent
$sourceRoot = Join-Path $routeRoot 'lean'
$fixedLean = Join-Path $researchRoot 'upstream/packing195/lean'
$fixedRoot = Split-Path $fixedLean -Parent
$expectedCommit = '2e91b05b25a4ee931a0490fefcdbb4f253be95c8'
$fixedCommit = (git -C $fixedRoot rev-parse HEAD).Trim()
if ($LASTEXITCODE -ne 0 -or $fixedCommit -ne $expectedCommit) {
    throw 'The upstream submodule is not at the audited commit.'
}
$fixedStatus = @(git -C $fixedRoot status --porcelain --untracked-files=no)
if ($LASTEXITCODE -ne 0 -or $fixedStatus.Count -ne 0) {
    throw 'The fixed upstream source has tracked modifications.'
}
$buildRoot = Join-Path $sourceRoot '.build'
$UpstreamProject = (Resolve-Path -LiteralPath $UpstreamProject).Path
$ToolchainBin = (Resolve-Path -LiteralPath $ToolchainBin).Path

$files = @('StrongEdge.lean', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'lean.ps1')
$files += @(Get-ChildItem -LiteralPath (Join-Path $fixedLean 'StrongEdge') -Filter '*.lean' -Recurse |
    ForEach-Object { [IO.Path]::GetRelativePath($fixedLean, $_.FullName) })
foreach ($relative in $files) {
    $expected = (Get-FileHash -LiteralPath (Join-Path $fixedLean $relative) -Algorithm SHA256).Hash
    $actual = (Get-FileHash -LiteralPath (Join-Path $UpstreamProject $relative) -Algorithm SHA256).Hash
    if ($expected -ne $actual) { throw "Upstream source mismatch: $relative" }
}

$moduleFiles = @{}
Get-ChildItem -LiteralPath (Join-Path $sourceRoot 'StrongEdge19') -Filter '*.lean' -Recurse |
    ForEach-Object {
        $name = [IO.Path]::GetRelativePath($sourceRoot, $_.FullName).Replace('\', '.').Replace('/', '.') -replace '\.lean$', ''
        $moduleFiles[$name] = $_.FullName
    }
if (Test-Path -LiteralPath (Join-Path $sourceRoot 'StrongEdge19.lean')) {
    $moduleFiles['StrongEdge19'] = Join-Path $sourceRoot 'StrongEdge19.lean'
}
$ordered = [Collections.Generic.List[string]]::new()
$visited = @{}
function Add-Module {
    param([string] $Name)
    if ($visited[$Name]) { return }
    if (-not $moduleFiles.ContainsKey($Name)) { throw "Missing module: $Name" }
    $visited[$Name] = $true
    $content = [IO.File]::ReadAllText($moduleFiles[$Name])
    foreach ($match in [regex]::Matches($content, '(?m)^(?:public )?import (StrongEdge19(?:\.[A-Za-z0-9_]+)*)\s*$')) {
        Add-Module $match.Groups[1].Value
    }
    $ordered.Add($Name)
}
if ($Module) { Add-Module $Module }
else { foreach ($name in @($moduleFiles.Keys | Sort-Object)) { Add-Module $name } }

$savedPath = $env:PATH
$savedLeanPath = $env:LEAN_PATH
$env:PATH = $ToolchainBin + [IO.Path]::PathSeparator + $env:PATH
$env:LEAN_PATH = $buildRoot + [IO.Path]::PathSeparator + $savedLeanPath
Push-Location $UpstreamProject
try {
    $leanVersion = ((& lean --version) | Out-String).Trim()
    if ($LASTEXITCODE -ne 0 -or $leanVersion -notmatch 'Lean \(version 4\.35\.0-rc4[, ]') {
        throw "Unexpected Lean compiler: $leanVersion"
    }
    foreach ($name in $ordered) {
        $output = Join-Path $buildRoot ($name.Replace('.', '/') + '.olean')
        if ($Incremental -and (Test-Path -LiteralPath $output)) {
            $stamp = (Get-Item -LiteralPath $output).LastWriteTimeUtc
            $fresh = $stamp -gt (Get-Item -LiteralPath $moduleFiles[$name]).LastWriteTimeUtc
            $content = [IO.File]::ReadAllText($moduleFiles[$name])
            foreach ($match in [regex]::Matches($content, '(?m)^(?:public )?import (StrongEdge19(?:\.[A-Za-z0-9_]+)*)\s*$')) {
                $dep = Join-Path $buildRoot ($match.Groups[1].Value.Replace('.', '/') + '.olean')
                if (-not (Test-Path -LiteralPath $dep) -or (Get-Item -LiteralPath $dep).LastWriteTimeUtc -gt $stamp) {
                    $fresh = $false
                }
            }
            if ($fresh) { Write-Output "Cached $name"; continue }
        }
        New-Item -ItemType Directory -Path (Split-Path $output -Parent) -Force | Out-Null
        Write-Output "Checking $name"
        & lake env lean -R $sourceRoot -o $output $moduleFiles[$name]
        if ($LASTEXITCODE -ne 0) { throw "Lean rejected $name" }
    }
} finally {
    Pop-Location
    $env:PATH = $savedPath
    $env:LEAN_PATH = $savedLeanPath
}
