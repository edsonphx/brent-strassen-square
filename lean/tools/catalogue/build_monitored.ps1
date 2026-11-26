# Run `lake build <targets>` and record wall time, the peak total memory of all `lean`
# processes, and the peak working set of each individual `lean` process (by command line).
param([Parameter(Mandatory = $true)][string[]]$Targets, [string]$Log = "build_log.txt")
$env:Path += ";$env:USERPROFILE\.elan\bin"
Set-Location (Split-Path -Parent $PSScriptRoot)
$sw = [Diagnostics.Stopwatch]::StartNew()
$tag = [guid]::NewGuid().ToString("N")
$p = Start-Process -FilePath "lake" -ArgumentList (@("build") + $Targets) -NoNewWindow -PassThru `
  -RedirectStandardOutput "$env:TEMP\bm_out_$tag.txt" -RedirectStandardError "$env:TEMP\bm_err_$tag.txt"
$h = $p.Handle
$peakTotal = 0
$perFile = @{}
while (-not $p.HasExited) {
  $total = 0
  foreach ($q in (Get-CimInstance Win32_Process -Filter "Name='lean.exe'" -ErrorAction SilentlyContinue)) {
    $total += $q.WorkingSetSize
    if ($q.CommandLine -match '([A-Za-z0-9_/\\\.]+\.lean)') {
      $k = $Matches[1]
      $ws = [double]$q.WorkingSetSize
      if (-not $perFile.ContainsKey($k) -or $perFile[$k] -lt $ws) { $perFile[$k] = $ws }
    }
  }
  if ($total -gt $peakTotal) { $peakTotal = $total }
  Start-Sleep -Seconds 2
}
$p.WaitForExit()
$sw.Stop()
$out = @()
$out += Get-Content "$env:TEMP\bm_out_$tag.txt", "$env:TEMP\bm_err_$tag.txt" -ErrorAction SilentlyContinue
$out += ("exit={0} wall_s={1:N0} peak_total_MB={2:N0}" -f $p.ExitCode, $sw.Elapsed.TotalSeconds, ($peakTotal / 1MB))
$out += "per-file peak working set (MB, sampled every 2 s):"
$out += ($perFile.GetEnumerator() | Sort-Object Name | ForEach-Object { "{0}`t{1:N0}" -f $_.Name, ($_.Value / 1MB) })
$out | Set-Content -Path $Log -Encoding utf8
$out | Select-Object -Last 3
