import requests
import shlex
import subprocess
import sys
import time


class Connector:
    """A generic connector that implements common methods"""

    def __init__(self, shell_out):
        self.shell_out = shell_out

    def shlog(self, text):
        if not text.startswith("#"):
            q = shlex.quote(text)
            print(f"echo {q}", file=self.shell_out)

        print(text, file=self.shell_out)


class SleepCmd(Connector):
    """A single command that delays by n seconds"""

    def __init__(self, shell_out, sleep_sec):
        super().__init__(shell_out)
        self.sleep_sec = sleep_sec

    def call(self):
        """Call a sleep command"""
        self.shlog("sleep {s}".format(s=self.sleep_sec))
        time.sleep(self.sleep_sec)
        return True


class CosmosCmd(Connector):
    """A single command to be executed via CLI"""

    def __init__(self, shell_out, binary, args, input_lines, timeout_sec=60):
        super().__init__(shell_out)
        self.binary = binary
        self.args = args
        self.input_lines = input_lines
        self.timeout_sec = timeout_sec

    def call(self):
        cmd_args_s = [str(a) for a in self.args]
        args_s = self.binary + cmd_args_s
        shell_cmd = " ".join([shlex.quote(a) for a in args_s])
        self.shlog(shell_cmd)
        with subprocess.Popen(
            self.binary + cmd_args_s,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=sys.stderr,
            text=True,
        ) as proc:
            try:
                for line in self.input_lines:
                    proc.stdin.write(line)
                    proc.stdin.write("\n")
                    proc.stdin.flush()

                outs, errs = proc.communicate(timeout=self.timeout_sec)
                # if code is 0, then the command was executed successfully
                self.shlog(f"# return code: {proc.returncode}")
                if proc.returncode > 0:
                    if errs != None:
                        for e in errs.split("\n"):
                            self.shlog("# " + e)
                        return False
                    else:
                        self.shlog(
                            "# Transaction command was not valid. Execution was aborted on CLI."
                        )
                        return False
                else:
                    for o in outs.split("\n"):
                        self.shlog("# " + o)
                    return outs
            except subprocess.TimeoutExpired:
                self.shlog("echo 'timeout' && exit 1")
                print("Timeout", file=sys.stderr)
                proc.kill()
                outs, errs = proc.communicate()
                return None
