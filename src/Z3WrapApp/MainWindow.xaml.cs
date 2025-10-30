//Copyright Warren Harding 2025.
using Microsoft.Win32;
using System.ComponentModel;
using System.Text;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Data;
using System.Windows.Documents;
using System.Windows.Input;
using System.Windows.Media;
using System.Windows.Media.Imaging;
using System.Windows.Navigation;
using System.Windows.Shapes;
using Z3Wrap;
using System.IO;

namespace Z3WrapApp
{
    /// <summary>
    /// Interaction logic for MainWindow.xaml
    /// </summary>
    public partial class MainWindow : Window, INotifyPropertyChanged
    {
        public event PropertyChangedEventHandler? PropertyChanged;
        private void Raise(string name) => PropertyChanged?.Invoke(this, new PropertyChangedEventArgs(name));

        private CancellationTokenSource? _cts;

        private string _scriptText = DefaultSample();
        public string ScriptText
        {
            get => _scriptText;
            set { _scriptText = value; Raise(nameof(ScriptText)); }
        }

        public MainWindow()
        {
            InitializeComponent();
            DataContext = this;
            TxtInput.Text = ScriptText;
            SetStatus("Ready.");
        }

        private static string DefaultSample() => """
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (> x 3))
        (check-sat)
        (get-model)
        """;

        private void SetStatus(string s) => LblStatus.Text = s;

        private void BtnOpen_Click(object sender, RoutedEventArgs e)
        {
            var dlg = new OpenFileDialog
            {
                Filter = "SMT-LIB2 files (*.smt2)|*.smt2|All files (*.*)|*.*"
            };
            if (dlg.ShowDialog(this) == true)
            {
                ScriptText = File.ReadAllText(dlg.FileName, Encoding.UTF8);
                TxtInput.Text = ScriptText;
                SetStatus($"Loaded: {dlg.FileName}");
            }
        }

        private void BtnSave_Click(object sender, RoutedEventArgs e)
        {
            var dlg = new SaveFileDialog
            {
                Filter = "SMT-LIB2 files (*.smt2)|*.smt2|All files (*.*)|*.*",
                FileName = "script.smt2"
            };
            if (dlg.ShowDialog(this) == true)
            {
                File.WriteAllText(dlg.FileName, TxtInput.Text, Encoding.UTF8);
                SetStatus($"Saved: {dlg.FileName}");
            }
        }

        private async void BtnRun_Click(object sender, RoutedEventArgs e)
        {
            if (_cts is not null)
            {
                SetStatus("Already running.");
                return;
            }

            // Build extra args
            var extra = new StringBuilder("-smt2 -in");
            if (ChkModel.IsChecked == true) extra.Append(" -model");
            if (ChkStats.IsChecked == true) extra.Append(" -stats");
            if (ChkVerbose.IsChecked == true) extra.Append(" -v:10");

            var z3Path = string.IsNullOrWhiteSpace(TxtZ3Path.Text) ? null : TxtZ3Path.Text.Trim();

            if (!int.TryParse(TxtTimeout.Text, out var timeoutMs)) timeoutMs = 10000;

            _cts = new CancellationTokenSource();
            try
            {
                ToggleUi(isRunning: true);
                SetStatus("Running...");
                LblExitCode.Text = "ExitCode: ...";
                LblTimedOut.Text = "TimedOut: ...";
                TxtStdOut.Text = "";
                TxtStdErr.Text = "";

                var script = TxtInput.Text;

                // Run via Z3Wrap
                var res = await Z3Cli.RunScriptAsync(
                    script,
                    z3Path: z3Path,
                    extraArgs: extra.ToString(),
                    timeoutMs: timeoutMs,
                    ct: _cts.Token);

                TxtStdOut.Text = res.StdOut;
                TxtStdErr.Text = res.StdErr;
                LblExitCode.Text = $"ExitCode: {res.ExitCode}";
                LblTimedOut.Text = $"TimedOut: {res.TimedOut}";
                SetStatus(res.TimedOut ? "Timed out." : "Done.");
            }
            catch (OperationCanceledException)
            {
                SetStatus("Cancelled.");
                LblExitCode.Text = "ExitCode: -";
                LblTimedOut.Text = "TimedOut: True";
            }
            catch (Exception ex)
            {
                TxtStdErr.Text = ex.ToString();
                SetStatus("Error.");
            }
            finally
            {
                _cts?.Dispose();
                _cts = null;
                ToggleUi(isRunning: false);
            }
        }

        private void BtnStop_Click(object sender, RoutedEventArgs e)
        {
            _cts?.Cancel();
            SetStatus("Cancelling...");
        }

        private void BtnClear_Click(object sender, RoutedEventArgs e)
        {
            TxtStdOut.Text = "";
            TxtStdErr.Text = "";
            LblExitCode.Text = "ExitCode: -";
            LblTimedOut.Text = "TimedOut: -";
            SetStatus("Cleared.");
        }

        private void ToggleUi(bool isRunning)
        {
            BtnRun.IsEnabled = !isRunning;
            BtnStop.IsEnabled = isRunning;
            BtnOpen.IsEnabled = !isRunning;
            BtnSave.IsEnabled = !isRunning;
            BtnClear.IsEnabled = !isRunning;
            TxtTimeout.IsEnabled = !isRunning;
            TxtZ3Path.IsEnabled = !isRunning;
            ChkModel.IsEnabled = !isRunning;
            ChkStats.IsEnabled = !isRunning;
            ChkVerbose.IsEnabled = !isRunning;
            TxtInput.IsReadOnly = isRunning;
        }
    }
}