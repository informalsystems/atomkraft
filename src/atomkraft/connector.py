# A generic connector interface
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

import shlex
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

