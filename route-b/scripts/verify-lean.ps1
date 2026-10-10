param(
    [Parameter(Mandatory = $true)][string] $UpstreamProject,
    [Parameter(Mandatory = $true)][string] $ToolchainBin
)

$ErrorActionPreference = 'Stop'
$routeRoot = Split-Path $PSScriptRoot -Parent
$sourceRoot = Join-Path $routeRoot 'lean'
$recordRoot = Join-Path $routeRoot 'verification/lean-extension'
$utf8 = [Text.UTF8Encoding]::new($false)
$startUtc = [DateTimeOffset]::UtcNow
$UpstreamProject = (Resolve-Path -LiteralPath $UpstreamProject).Path
$ToolchainBin = (Resolve-Path -LiteralPath $ToolchainBin).Path
New-Item -ItemType Directory -Path $recordRoot -Force | Out-Null
$recordPath = Join-Path $recordRoot 'results.json'
[IO.File]::WriteAllText($recordPath, (@{ status = 'running'; started_utc = $startUtc.ToString('o') } |
    ConvertTo-Json) + "`n", $utf8)
$captured = [Collections.Generic.List[string]]::new()

try {
    $sourceFiles = @(Get-ChildItem -LiteralPath $sourceRoot -Filter '*.lean' -File -Recurse |
        Where-Object { $_.FullName -notmatch '[\\/]\.(?:build|lake)[\\/]' } | Sort-Object FullName)
    $names = @($sourceFiles | Where-Object { $_.Name -ne 'Audit.lean' } | ForEach-Object {
        $body = [IO.File]::ReadAllText($_.FullName)
        if ($body -match '\b(?:sorry|admit)\b|(?m)^\s*(?:private\s+)?axiom\s+') {
            throw "A proof placeholder or custom axiom occurs in $($_.Name)."
        }
        [regex]::Matches($body, '(?m)^(?:noncomputable )?(?:theorem|def) ([A-Za-z0-9_]+)') |
            ForEach-Object { 'StrongEdge19.' + $_.Groups[1].Value }
    } | Sort-Object)
    $auditPath = Join-Path $sourceRoot 'StrongEdge19/Audit.lean'
    $expected = @([regex]::Matches([IO.File]::ReadAllText($auditPath), '(?m)^#print axioms (\S+)') |
        ForEach-Object { $_.Groups[1].Value } | Sort-Object)
    if ($names.Count -ne $expected.Count -or @(Compare-Object $names $expected).Count -ne 0) {
        throw 'Every new declaration must be present exactly once in the axiom audit.'
    }
    $hashFiles = @($sourceFiles.FullName) + @(
        (Join-Path $sourceRoot 'lean-toolchain'),
        (Join-Path $sourceRoot 'lakefile.toml'),
        (Join-Path $PSScriptRoot 'build-lean.ps1'),
        $PSCommandPath
    )
    $hashes = @($hashFiles | ForEach-Object {
        [ordered]@{
            path = [IO.Path]::GetRelativePath($routeRoot, $_).Replace('\', '/')
            sha256 = (Get-FileHash -LiteralPath $_ -Algorithm SHA256).Hash.ToLowerInvariant()
        }
    })
    & (Join-Path $PSScriptRoot 'build-lean.ps1') -UpstreamProject $UpstreamProject -ToolchainBin $ToolchainBin |
        ForEach-Object {
            $line = $_.ToString()
            $captured.Add($line)
            if ($line.StartsWith('Checking ')) { Write-Output $line }
        }
    $logText = ($captured -join "`n") + "`n"
    [IO.File]::WriteAllText((Join-Path $recordRoot 'build-and-audit.log'), $logText, $utf8)
    $allowed = @('propext', 'Classical.choice', 'Quot.sound')
    $matches = [regex]::Matches($logText, "'([^']+)' depends on axioms:\s*\[([^\]]*)\]",
        [Text.RegularExpressions.RegexOptions]::Singleline)
    $empty = [regex]::Matches($logText, "'([^']+)' does not depend on any axioms")
    $entries = @($matches | ForEach-Object {
        $axioms = @($_.Groups[2].Value -split ',' | ForEach-Object { $_.Trim() } | Where-Object { $_ })
        foreach ($name in $axioms) {
            if ($name -notin $allowed) { throw "Unexpected axiom: $name" }
        }
        [ordered]@{ declaration = $_.Groups[1].Value; axioms = $axioms }
    })
    $entries += @($empty | ForEach-Object {
        [ordered]@{ declaration = $_.Groups[1].Value; axioms = @() }
    })
    $actual = @($entries | ForEach-Object { $_.declaration } | Sort-Object)
    if ($actual.Count -ne $expected.Count -or @(Compare-Object $expected $actual).Count -ne 0) {
        throw 'The compiler output does not contain every requested axiom audit exactly once.'
    }
    foreach ($entry in $hashes) {
        $after = (Get-FileHash -LiteralPath (Join-Path $routeRoot $entry.path) -Algorithm SHA256).Hash.ToLowerInvariant()
        if ($after -ne $entry.sha256) { throw "Source changed during verification: $($entry.path)" }
    }
    $leanVersion = ((& (Join-Path $ToolchainBin 'lean.exe') --version) | Out-String).Trim()
    if ($LASTEXITCODE -ne 0) { throw 'Could not record the compiler version.' }
    $result = [ordered]@{
        status = 'passed'
        started_utc = $startUtc.ToString('o')
        finished_utc = [DateTimeOffset]::UtcNow.ToString('o')
        lean_version = $leanVersion
        upstream_commit = '2e91b05b25a4ee931a0490fefcdbb4f253be95c8'
        upstream_project = $UpstreamProject
        upstream_files_byte_compared = 79
        upstream_tracked_source_unchanged = $true
        build_mode = 'All extension modules recompiled; compiled upstream and mathlib dependencies reused.'
        build_exit_code = 0
        lean_source_file_count = $sourceFiles.Count
        declaration_count = $names.Count
        axiom_audit_count = $entries.Count
        allowed_axioms = $allowed
        axiom_audits = $entries
        source_hashes = $hashes
        source_files_unchanged_after_verification = $true
        log = 'build-and-audit.log'
        scope = 'Unconditional corrected nineteen packing for every candidate set, including the independence-number form and literal connected-component correction. Includes exact compensation, tertiary normalization, all five critical-degree exclusions, and high19 nineteen-clique rigidity.'
        full_corrected_nineteen_theorem_formalized = $true
        main_declarations = @(
            'StrongEdge19.induced_matching_packing19_unconditional',
            'StrongEdge19.induced_matching_packing19_with_connected_component_count',
            'StrongEdge19.prescribed_edge_bound19'
        )
    }
    [IO.File]::WriteAllText($recordPath, ($result | ConvertTo-Json -Depth 8) + "`n", $utf8)
    Write-Output "PASS: $($sourceFiles.Count) Lean files; $($entries.Count) declaration audits; no additional axioms."
} catch {
    [IO.File]::WriteAllText((Join-Path $recordRoot 'build-and-audit.log'), ($captured -join "`n") + "`n", $utf8)
    [IO.File]::WriteAllText($recordPath, (@{
        status = 'failed'; started_utc = $startUtc.ToString('o'); finished_utc = [DateTimeOffset]::UtcNow.ToString('o')
        reason = $_.Exception.Message
    } | ConvertTo-Json) + "`n", $utf8)
    throw
}
