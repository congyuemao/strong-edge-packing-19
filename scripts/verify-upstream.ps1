param(
    [string] $ProjectDirectory = '',
    [string] $ToolchainBin = ''
)

$ErrorActionPreference = 'Stop'
$researchRoot = Split-Path $PSScriptRoot -Parent
$fixedRoot = Join-Path $researchRoot 'upstream/packing195'
$fixedLean = Join-Path $fixedRoot 'lean'
$recordRoot = Join-Path $researchRoot 'verification'
$expectedCommit = '2e91b05b25a4ee931a0490fefcdbb4f253be95c8'
if (-not $ProjectDirectory) { $ProjectDirectory = $fixedLean }
$ProjectDirectory = (Resolve-Path -LiteralPath $ProjectDirectory).Path
$fixedCommit = (git -C $fixedRoot rev-parse HEAD).Trim()
if ($LASTEXITCODE -ne 0 -or $fixedCommit -ne $expectedCommit) {
    throw 'The upstream submodule is not at the audited commit.'
}
$fixedStatus = @(git -C $fixedRoot status --porcelain --untracked-files=no)
if ($LASTEXITCODE -ne 0 -or $fixedStatus.Count -ne 0) {
    throw 'The fixed upstream source has tracked modifications.'
}

$relativeFiles = @('StrongEdge.lean')
$relativeFiles += @(Get-ChildItem -LiteralPath (Join-Path $fixedLean 'StrongEdge') -Filter '*.lean' -Recurse |
    ForEach-Object { [IO.Path]::GetRelativePath($fixedLean, $_.FullName).Replace('\', '/') })
$relativeFiles += @('lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'lean.ps1')
$relativeFiles = @($relativeFiles | Sort-Object)
if ($relativeFiles.Count -ne 79) { throw 'Unexpected upstream file inventory.' }
$fileRecords = @($relativeFiles | ForEach-Object {
    $fixedHash = (Get-FileHash -LiteralPath (Join-Path $fixedLean $_) -Algorithm SHA256).Hash.ToLowerInvariant()
    $projectHash = (Get-FileHash -LiteralPath (Join-Path $ProjectDirectory $_) -Algorithm SHA256).Hash.ToLowerInvariant()
    if ($fixedHash -ne $projectHash) { throw "Source mismatch: $_" }
    [ordered]@{ path = $_; sha256 = $fixedHash }
})

$savedPath = $env:PATH
$startUtc = [DateTimeOffset]::UtcNow
$utf8 = [Text.UTF8Encoding]::new($false)
New-Item -ItemType Directory -Path $recordRoot -Force | Out-Null
if ($ToolchainBin) { $env:PATH = (Resolve-Path -LiteralPath $ToolchainBin).Path + [IO.Path]::PathSeparator + $env:PATH }

function Invoke-RecordedLake {
    param([string] $LogName, [string[]] $LakeArguments)
    $captured = @(& lake @LakeArguments 2>&1)
    $commandExit = $LASTEXITCODE
    $capturedText = ($captured | ForEach-Object { $_.ToString() }) -join "`n"
    [IO.File]::WriteAllText((Join-Path $recordRoot $LogName), $capturedText + "`n", $utf8)
    if ($commandExit -ne 0) { throw "lake $($LakeArguments -join ' ') failed with exit $commandExit; see $LogName" }
    return [ordered]@{ command = 'lake ' + ($LakeArguments -join ' '); exit_code = $commandExit; log = $LogName }
}

Push-Location $ProjectDirectory
try {
    $leanVersion = ((& lean --version) | Out-String).Trim()
    if ($LASTEXITCODE -ne 0 -or $leanVersion -notmatch 'Lean \(version 4\.35\.0-rc4[, ]') {
        throw "Unexpected Lean compiler: $leanVersion"
    }
    $buildRecord = Invoke-RecordedLake -LogName 'build.log' -LakeArguments @('build')
    $auditRecord = Invoke-RecordedLake -LogName 'audit195-unconditional.log' -LakeArguments @('env', 'lean', 'StrongEdge/Audit195Unconditional.lean')
    $auditText = [IO.File]::ReadAllText((Join-Path $recordRoot $auditRecord.log))
    $axiomMatches = [regex]::Matches($auditText, "'([^']+)' depends on axioms:\s*\[([^\]]*)\]", [Text.RegularExpressions.RegexOptions]::Singleline)
    $emptyMatches = [regex]::Matches($auditText, "'([^']+)' does not depend on any axioms")
    $allowed = @('propext', 'Classical.choice', 'Quot.sound')
    $auditEntries = @($axiomMatches | ForEach-Object {
        $names = @($_.Groups[2].Value -split ',' | ForEach-Object { $_.Trim() } | Where-Object { $_ })
        foreach ($axiomName in $names) {
            if ($axiomName -notin $allowed) { throw "Unexpected axiom: $axiomName" }
        }
        [ordered]@{ declaration = $_.Groups[1].Value; axioms = $names }
    })
    $auditEntries += @($emptyMatches | ForEach-Object { [ordered]@{ declaration = $_.Groups[1].Value; axioms = @() } })
    $expectedNames = @(Get-Content -LiteralPath (Join-Path $fixedLean 'StrongEdge/Audit195Unconditional.lean') |
        Where-Object { $_ -match '^#print axioms ' } | ForEach-Object { $_.Substring(14).Trim() } | Sort-Object)
    $actualNames = @($auditEntries | ForEach-Object { $_.declaration } | Sort-Object)
    if ($actualNames.Count -ne $expectedNames.Count -or @(Compare-Object $expectedNames $actualNames).Count -ne 0) {
        throw 'The output does not match every requested axiom audit declaration.'
    }
    foreach ($entry in $fileRecords) {
        $afterHash = (Get-FileHash -LiteralPath (Join-Path $ProjectDirectory $entry.path) -Algorithm SHA256).Hash.ToLowerInvariant()
        if ($afterHash -ne $entry.sha256) { throw "Source changed during verification: $($entry.path)" }
    }
    $result = [ordered]@{
        status = 'passed'
        upstream_url = 'https://github.com/congyuemao/strong-edge-packing-195'
        upstream_commit = $fixedCommit
        started_utc = $startUtc.ToString('o')
        finished_utc = [DateTimeOffset]::UtcNow.ToString('o')
        project_directory = $ProjectDirectory
        build_mode = 'incremental; existing dependency and project caches may be reused'
        lean_version = $leanVersion
        compared_source_files = $fileRecords.Count
        source_files_unchanged_after_verification = $true
        commands = @($buildRecord, $auditRecord)
        axiom_audit_count = $auditEntries.Count
        allowed_axioms = $allowed
        axiom_audits = $auditEntries
        source_hashes = $fileRecords
        scope = 'Existing 19.5 development only; new paper lemmas in notes/route-b-stage1.md are not formalized.'
    }
    [IO.File]::WriteAllText((Join-Path $recordRoot 'results.json'), ($result | ConvertTo-Json -Depth 8) + "`n", $utf8)
    Write-Output "PASS: $($fileRecords.Count) source files matched; $($auditEntries.Count) axiom audits matched and passed."
} finally {
    Pop-Location
    $env:PATH = $savedPath
}
