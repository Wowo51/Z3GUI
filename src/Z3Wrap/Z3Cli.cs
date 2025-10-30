//Copyright Warren Harding 2025.
using System;
using System.Diagnostics;
using System.Text;
using System.Threading;
using System.Threading.Tasks;

namespace Z3Wrap;

public static class Z3Cli
{
    public record Result(int ExitCode, string StdOut, string StdErr, bool TimedOut);

    /// <summary>
    /// Runs a Z3 script (SMT-LIB2 text) by piping it to z3's stdin.
    /// Default args use SMT2 mode and stdin: "-smt2 -in".
    /// </summary>
    /// <param name="script">SMT-LIB2 content (e.g., with (check-sat), (get-model), ...)</param>
    /// <param name="z3Path">Path to z3 executable, or null to use "z3" on PATH</param>
    /// <param name="extraArgs">Extra CLI args (default: "-smt2 -in")</param>
    /// <param name="timeoutMs">Kill process if not done within this many ms (0 = no timeout)</param>
    /// <param name="ct">Cancellation token</param>
    public static async Task<Result> RunScriptAsync(
        string script,
        string? z3Path = null,
        string extraArgs = "-smt2 -in",
        int timeoutMs = 0,
        CancellationToken ct = default)
    {
        z3Path ??= "z3";

        var psi = new ProcessStartInfo
        {
            FileName = z3Path,
            Arguments = extraArgs,
            UseShellExecute = false,
            RedirectStandardInput = true,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            CreateNoWindow = true,
            StandardOutputEncoding = Encoding.UTF8,
            StandardErrorEncoding = Encoding.UTF8
        };

        using var proc = new Process { StartInfo = psi, EnableRaisingEvents = true };

        try
        {
            if (!proc.Start())
                return new Result(-1, "", "Failed to start z3 process.", false);

            // Write the script to stdin and close input so Z3 knows it’s done.
            await proc.StandardInput.WriteAsync(script.AsMemory(), ct);
            await proc.StandardInput.FlushAsync();
            proc.StandardInput.Close();

            // Read outputs concurrently.
            var readOutTask = proc.StandardOutput.ReadToEndAsync();
            var readErrTask = proc.StandardError.ReadToEndAsync();

            // Handle timeout/cancellation.
            using var cts = CancellationTokenSource.CreateLinkedTokenSource(ct);
            if (timeoutMs > 0) cts.CancelAfter(timeoutMs);

            try
            {
                await proc.WaitForExitAsync(cts.Token);
            }
            catch (OperationCanceledException)
            {
                TryKill(proc);
                var so = await readOutTask;
                var se = await readErrTask;
                return new Result(-1, so, se.Length == 0 ? "Z3 timed out or was cancelled." : se, TimedOut: true);
            }

            var stdout = await readOutTask;
            var stderr = await readErrTask;
            return new Result(proc.ExitCode, stdout, stderr, TimedOut: false);
        }
        catch (System.ComponentModel.Win32Exception w32)
        {
            // Typically "The system cannot find the file specified" -> z3 not on PATH or path invalid
            return new Result(-1, "", $"Failed to start '{z3Path}': {w32.Message}", false);
        }
        catch (Exception ex)
        {
            return new Result(-1, "", ex.ToString(), false);
        }

        static void TryKill(Process p)
        {
            try { if (!p.HasExited) p.Kill(entireProcessTree: true); } catch { /* ignore */ }
        }
    }
}
