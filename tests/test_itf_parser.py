# Test itf_parser.py
#
#
# https://apalache.informal.systems/docs/adr/015adr-trace.html
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

import unittest

from frozendict import frozendict

from atomkraft.itf_parser import trace_from_itf_json

class TestItfParser(unittest.TestCase):
    def test_parse_itf(self):
        # json input encoded in python
        root = {
                "vars": [ "a", "b", "c", "d", "e", "f" ],
                "states": [
                    {
                        "a": 1,
                        "b": False,
                        "c": "foo",
                        "d": { "#map": [ ["foo", 1], ["bar", 2] ] },
                        "e": [ 1, 2, 3],
                        "f": { "alice": 10, "bob": 12 }
                    },
                    {
                        "a": 2,
                        "b": True,
                        "c": "bar",
                        "d": { "#map": [ ["foo", 3], ["bar", 4] ] },
                        "e": [ 3, 5],
                        "f": { "alice": 11 }
                    }
                ]
        }
        # convert the trace
        trace = trace_from_itf_json(root)
        # state 0
        self.assertEqual(trace["vars"], ["a", "b", "c", "d", "e", "f"])
        self.assertEqual(trace["states"][0]["a"], 1)
        self.assertEqual(trace["states"][0]["b"], False)
        self.assertEqual(trace["states"][0]["c"], "foo")
        self.assertEqual(trace["states"][0]["d"],
                frozendict({ "foo": 1, "bar": 2 }))
        self.assertEqual(trace["states"][0]["e"], (1, 2, 3))
        self.assertEqual(trace["states"][0]["f"],
                frozendict({ "alice": 10, "bob": 12 }))
        # state 1
        self.assertEqual(trace["states"][1]["a"], 2)
        self.assertEqual(trace["states"][1]["b"], True)
        self.assertEqual(trace["states"][1]["c"], "bar")
        self.assertEqual(trace["states"][1]["d"],
                frozendict({ "foo": 3, "bar": 4 }))
        self.assertEqual(trace["states"][1]["e"], (3, 5))
        self.assertEqual(trace["states"][1]["f"],
                frozendict({ "alice": 11 }))


if __name__ == '__main__':
    unittest.main()

