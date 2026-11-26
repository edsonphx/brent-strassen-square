# Compile one Lean file with the project's LEAN_PATH; report exit code, wall time and the peak
# working set of the `lean` processes it starts.
# Usage: powershell -File scripts/timed_lean.ps1 <file.lean> [<out.olean>]
param([Parameter(Mandatory = $true)][string]$File, [string]$Olean = "")
$env:Path += ";$env:USERPROFILE\.elan\bin"
$root = Split-Path -Parent $PSScriptRoot
Set-Location $root
$largs = @("env", "lean", $File)
if ($Olean) { $largs += @("-o", $Olean) }
$t0 = Get-Date
$sw = [Diagnostics.Stopwatch]::StartNew()
$tag = [guid]::NewGuid().ToString("N")
$p = Start-Process -FilePath "lake" -ArgumentList $largs -NoNewWindow -PassThru `
  -RedirectStandardOutput "$env:TEMP\tl_out_$tag.txt" -RedirectStandardError "$env:TEMP\tl_err_$tag.txt"
$h = $p.Handle  # keep the handle so ExitCode is available
$peak = 0
while (-not $p.HasExited) {
  foreach ($q in (Get-Process lean -ErrorAction SilentlyContinue)) {
    try {
      if ($q.StartTime -ge $t0.AddSeconds(-1) -and $q.PeakWorkingSet64 -gt $peak) { $peak = $q.PeakWorkingSet64 }
    } catch {}
  }
  Start-Sleep -Milliseconds 250
}
$p.WaitForExit()
$sw.Stop()
Get-Content "$env:TEMP\tl_out_$tag.txt", "$env:TEMP\tl_err_$tag.txt" -ErrorAction SilentlyContinue
"{0}`texit={1}`twall_s={2:N1}`tpeak_MB={3:N0}" -f $File, $p.ExitCode, $sw.Elapsed.TotalSeconds, ($peak / 1MB)
