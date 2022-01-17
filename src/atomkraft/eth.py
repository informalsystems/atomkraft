# Etherium connector, tested on communication with Ethermint. This connector is
# designed for running tests. It stores private keys unsafely. Never use it
# with your real accounts!
#
# This connector is using web3py:
# https://web3py.readthedocs.io/en/stable/quickstart.html
#
# This module needs some refactoring, if we want to make an audit library
# out of it.
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

import binascii
import inspect
import json
import math
import sys
import time

from web3 import Web3
from web3.exceptions import ContractLogicError

from atomkraft.connector import Connector

class EthConnector(Connector):
    """Ethereum connector communicates
       with a local Ethereum/Ethermint blockchain."""

    def __init__(self, shell_out, url, accounts, deployer, contract_paths):
        """Construct a connector.

        Arguments:
        - shell_out is a text file output to write the shell commands
        - url is a connection URL, e.g., "http://localhost:8545"
        - accounts is a dictionary that maps usernames to their private keys
        - contract_paths is a dictionary that maps contract names
          to the names of files that contain compiled contracts
        """
        super().__init__(shell_out)
        self._url = url
        self._accounts = accounts
        self._deployer = deployer
        self._contract_paths = contract_paths
        self._contract_addrs = {}
        self._contracts = {}
        # track nonces, otherwise the server will reject our transactions
        self._nonces = { k: 0 for k in accounts.keys() }
        self._provider = Web3(Web3.HTTPProvider(self._url))
        if not self._provider.isConnected():
            raise RuntimeError(f"Failed to connect to: {self._url}")

    def _get_addr(self, username):
        """Get an account address and convert it to EIP-55"""
        return Web3.toChecksumAddress(self._accounts[username]["addr"])

    def prepare(self):
        """Prepare the connector, e.g., deploy the smart contracts"""

        # deploy all contracts that are passed in self._contract_paths
        for (name, contract_setup) in self._contract_paths.items():
            filename = contract_setup["filename"]
            with open(filename, "r") as f:
                json_data = json.load(f)
                abi = json_data['abi']
                if contract_setup["deploy"]:
                    bytecode = Web3.toBytes(hexstr=json_data['bytecode'])
                    deployer = self._deployer
                    data = {
                        'from':                 self._get_addr(deployer),
                        'maxFeePerGas':         1000000000,
                        'maxPriorityFeePerGas': 1000000000
                    }
                    contract = self._provider.eth.contract(abi=abi, bytecode=bytecode)
                    tx_data = contract \
                            .constructor(*contract_setup["ctor_args"]) \
                            .buildTransaction(data)
                    # sign the transaction and send it via send_raw_transaction
                    self.shlog(f'# Deploy contract {name}...')
                    receipt = self.send(deployer, tx_data)
                    contract_address = receipt['contractAddress']
                    self.shlog(f'# ...deployed contract {name} to {contract_address}')
                    self._contract_addrs[name] = contract_address
                    self._contracts[name] = contract
                else:
                    contract_address = contract_setup["contract_address"]
                    contract = self._provider.eth.contract(abi=abi, address=contract_address)
                    self.shlog(f'# Predeployed contract {name} at {contract_address}')
                    self._contract_addrs[name] = contract_address
                    self._contracts[name] = contract


    def balanceOf(self, user, contract_name):
        contract = self._contracts[contract_name]
        user_addr = self._get_addr(user)
        contract_addr = self._contract_addrs[contract_name]
        init_data = {
                "to": contract_addr,
                'maxFeePerGas':         1000000000,
                'maxPriorityFeePerGas': 1000000000
            }
        
        return contract.functions.balanceOf(user_addr).call(init_data)  

    def allowanceOf(self, owner, spender, contract_name):
        contract = self._contracts[contract_name]
        owner_addr = self._get_addr(owner)
        spender_addr = self._get_addr(spender)
        contract_addr = self._contract_addrs[contract_name]
        init_data = {
                "to": contract_addr,
                'maxFeePerGas':         1000000000,
                'maxPriorityFeePerGas': 1000000000
            }

        return contract.functions.allowance(owner_addr,spender_addr).call(init_data)  


    def call(self, user, contract_name, method_name, *args, **kw_args):
        """Execute a contract method in a single transaction signed by 'user'"""
        contract = self._contracts[contract_name]
        user_addr = self._get_addr(user)
        contract_addr = self._contract_addrs[contract_name]
        self.shlog(f"# {user} calls {contract_name}.{method_name}({args}, {kw_args})")
        try:
            init_data = {
                "from": user_addr,
                "to": contract_addr,
                'maxFeePerGas':         1000000000,
                'maxPriorityFeePerGas': 1000000000
            }
            tx_data = contract \
                        .get_function_by_name(method_name)(*args, **kw_args) \
                        .buildTransaction(init_data)
        except TypeError as e:
            print(f"TypeError: Failed {contract_name}.{method_name}({args}, {kw_args})",
                    file=sys.stderr)
            raise e
        except ContractLogicError as e:
            print(f"ContractLogicError: Failed {contract_name}.{method_name}({args}, {kw_args})",
                    file=sys.stderr)
            print(str(e), file=sys.stderr)
            return None
        except ValueError as e:
            print(f"ValueError: Failed {contract_name}.{method_name}({args}, {kw_args})",
                    file=sys.stderr)
            print(str(e), file=sys.stderr)
            return None


        # sign the transaction and send it via send_raw_transaction
        receipt = self.send(user, tx_data)
        return receipt


    def send(self, user, data):
        """Execute a transaction signed by the given user with the data
           provided in 'data'"""
        if user not in self._accounts:
            raise RuntimeError(f"No key stored for the user: {user}")

        key = self._accounts[user]["key"]
        nonce = self._nonces[user]
        ext_data = {
            **data,
            'from': self._get_addr(user),
            'nonce': nonce
        }
        self._nonces[user] = nonce + 1
        self.shlog('# send: ' + str(ext_data))
        signed = self._provider.eth.account.sign_transaction(ext_data, key)
        self.shlog(self._curl(ext_data['nonce'],
                   "eth_sendRawTransaction", signed.rawTransaction))
        tx_hash = self._provider.eth.send_raw_transaction(signed.rawTransaction)
        self.shlog('# ETH tx_hash={h}'.format(h=Web3.toHex(tx_hash)))
        receipt = self._provider.eth.wait_for_transaction_receipt(tx_hash)
        # the produced script waits for a receipt in a while-loop
        curl_receipt = \
            self._curl(ext_data['nonce'], "eth_getTransactionReceipt", tx_hash)
        self.shlog('(while true; do sleep 1; ({r} | grep \'"status":\') && break; done)'.\
                format(r=curl_receipt))
        return receipt

    def _curl(self, nonce, method_name, signed):
        """Produce a request to curl"""

        req = {
	        "jsonrpc": "2.0",
	        "method": method_name,
            "params": [signed.hex()],
            "id": nonce
        }

        return ("curl -s -L -X POST '{u}' -H 'Content-Type: application/json'" + \
            " --data-raw '{d}'").format(u=self._url, d=json.dumps(req))

