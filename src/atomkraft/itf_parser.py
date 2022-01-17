# This module contains a parser for traces in the Informal Trace Format:
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

import json
import sys

from frozendict import frozendict

class ItfError(Exception):
    """Parse error is thrown whenever a parse error occurs"""

    def __init__(self, message):
        self.message = message
    

def trace_from_itf_file(filename):
    """Parse a trace from a file in the Informal Trace Format"""

    with open(filename, "r") as f:
        root = json.load(f)
        return trace_from_itf_json(root)


def trace_from_itf_json(root):
    """Parse a trace from a JSON object in the Informal Trace Format"""

    def parse_err(msg):
        raise ItfError(f"JSON error: {msg}")

    def convert(obj):
        if type(obj) == int or type(obj) == str or type(obj) == bool:
            # return the literal as is
            return obj
        elif type(obj) == list:
            # convert to a tuple, so we can put it into a set or a dict
            return tuple([convert(e) for e in obj])
        elif type(obj) == dict:
            keys = obj.keys()
            if "#bigint" in keys:
                return int(obj["#bigint"])
            if "#tup" in keys:
                return tuple([convert(e) for e in obj["#tup"]])
            if "#set" in keys:
                # use a frozenset, so we can put them into a set or a dict
                return frozenset([convert(e) for e in obj["#set"]])
            if "#map" in keys:
                # convert to a frozendict
                return frozendict({
                    convert(k): convert(v) for (k, v) in obj["#map"]
                })
            else:
                # use a frozendict, so we can put it into a set or another dict
                return frozendict({ k: convert(v) for (k, v) in obj.items() })
        else:
            parse_err("Unexpected input: " + str(obj))

    # Compare with the Informal Trace Format, see:
    # https://apalache.informal.systems/docs/adr/015adr-trace.html
    jvars = root.get("vars", None)

    # parse the mandatory fields
    jstates = root.get("states", None)
    if not jvars:
        parse_err("Missing field 'vars'")
    if not jstates:
        parse_err("Missing field 'states'")

    # translate the states into native python
    states = []
    for (no, jstate) in enumerate(jstates):
        # translate the expressions for all variables
        for v in jvars:
            if v not in jstate:
                parse_error(f"State {no} is missing variable {v}")

        state = { k: convert(v) for (k, v) in jstate.items() }
        states.append(state)

    output = { "vars": jvars, "states": states }
    json_params = root.get("params", None)
    if json_params:
        output["params"] = json_params

    return output

