# Cosmos connector. So far, we have been usign CLI.
# We might want to add JSON and GRPC interfaces later.
#
#
#   Copyright 2022 Informal Systems
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.

import requests
import shlex
import subprocess
import sys

from connector import Connector

### A generic CLI Cosmos command

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
        args_s = [self.binary] + cmd_args_s
        shell_cmd = " ".join([shlex.quote(a) for a in args_s])
        self.shlog(shell_cmd)
        with subprocess.Popen([self.binary] + cmd_args_s, \
                              stdin=subprocess.PIPE, \
                              stdout=subprocess.PIPE, \
                              stderr=sys.stderr, \
                              text=True) as proc:
            try:
                for line in self.input_lines:
                    proc.stdin.write(line)
                    proc.stdin.write("\n")
                    proc.stdin.flush()

                outs, errs = proc.communicate(timeout=self.timeout_sec)
                # if code is 0, then the command was executed successfully
                self.shlog(f"# return code: {proc.returncode}")
                if proc.returncode > 0:
                    for e in errs.split('\n'):
                        self.shlog('# ' + e)
                    return False
                else:
                    for o in outs.split('\n'):
                        self.shlog('# ' + o)
                    return ('code: 0' in outs)
            except subprocess.TimeoutExpired:
                self.shlog("echo 'timeout' && exit 1")
                print("Timeout", file=sys.stderr)
                proc.kill()
                outs, errs = proc.communicate()
                return None


### A generic Cosmos query via REST.
### Since the API may change from version to version,
### we should introduce the API version in the future and produce requests
### based on the API version.

class CosmosRest:
    """A single command to be executed via the REST API"""

    def __init__(self, server_url, path, timeout_sec=60):
        self.server_url = server_url
        self.path = path
        self.timeout_sec = timeout_sec

    def call(self):
        """Call a REST endpoint and return the result as JSON"""
        url = self.server_url + self.path
        return requests.get(url, timeout=self.timeout_sec).json()


### Instances of CosmosRest to capture the standard API

class CosmosBalance(CosmosRest):
    """An instance of CosmosRest to query for a balance"""

    def __init__(self, server_url, user_addr, timeout_sec=60):
        path = "/cosmos/bank/v1beta1/balances/{u}".format(u=user_addr) 
        super().__init__(server_url, path, timeout_sec)

