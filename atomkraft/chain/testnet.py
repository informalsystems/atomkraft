import glob
import time
from typing import Dict

import click
import numpy as np
import tabulate

from .node import Account, Coin, ConfigPort, Node
from .utils import get_free_ports, update_port


class Testnet:
    def __init__(
        self,
        chain_id,
        n_validator=2,
        n_account=0,
        binary="gaiad",
        denom="uatom",
        prefix="cosmos",
        coin_type=118,
        genesis_config: Dict = {},
        node_config: Dict = {},
        account_balance: int = 10**27,
        validator_balance: int = 10**21,
        overwrite=False,
        keep=False,
        verbose=False,
    ):
        self.chain_id = chain_id
        self.n_validator = n_validator
        self.n_account = n_account
        self.binary = binary
        self.denom = denom
        self.prefix = prefix
        self.coin_type = coin_type
        self.genesis_config = genesis_config
        self.node_config = node_config
        self.account_balance = account_balance
        self.validator_balance = validator_balance
        self.overwrite = overwrite
        self.keep = keep
        self._verbose = verbose

    @staticmethod
    def ports() -> Dict[str, ConfigPort]:
        data = {}

        # config.toml
        data["p2p"] = ConfigPort("P2P", "config/config.toml", "p2p.laddr")
        # data["p2p_ext"] = ConfigPort("P2P External", "config/config.toml", "p2p.external_address")
        data["abci"] = ConfigPort("ABCI", "config/config.toml", "proxy_app")
        data["pprof_laddr"] = ConfigPort(
            "PPROF", "config/config.toml", "rpc.pprof_laddr"
        )
        data["rpc"] = ConfigPort("RPC", "config/config.toml", "rpc.laddr")
        data["prometheus"] = ConfigPort(
            "Prometheus", "config/config.toml", "instrumentation.prometheus_listen_addr"
        )

        # app.toml
        data["lcd"] = ConfigPort("LCD", "config/app.toml", "api.address")
        data["grpc"] = ConfigPort("gRPC", "config/app.toml", "grpc.address")
        data["grpc-web"] = ConfigPort("gRPC", "config/app.toml", "grpc-web.address")
        # dict["rosetta"] = ConfigPort("Rosetta", "config/app.toml", "rosetta.address")
        return data

    def get_validator_port(self, validator_id, port_type):
        return self.validator_nodes[validator_id].get_port(self.ports()[port_type])

    def prepare(self):
        self.validator_nodes = [
            Node(
                f"node-{i}",
                self.chain_id,
                f"node-{i}",
                overwrite=self.overwrite,
                keep=self.keep,
                binary=self.binary,
                denom=self.denom,
                prefix=self.prefix,
            )
            for i in range(self.n_validator)
        ]
        self.validators = [Account(f"validator-{i}") for i in range(self.n_validator)]
        self.accounts = [Account(f"account-{i}") for i in range(self.n_account)]

        for node in self.validator_nodes:
            node.init()

        for (k, v) in self.genesis_config.items():
            self.validator_nodes[0].set("config/genesis.json", v, k)

        for validator in self.validators:
            self.validator_nodes[0].add_account(
                Coin(self.account_balance, self.denom), validator
            )

        for account in self.accounts:
            self.validator_nodes[0].add_account(
                Coin(self.account_balance, self.denom), account
            )

        for i in range(1, len(self.validator_nodes)):
            self.validator_nodes[i].copy_genesis_from(self.validator_nodes[0])

        # very hacky
        all_ports = np.array(
            get_free_ports(len(self.ports()) * (self.n_validator - 1))
        ).reshape((-1, len(self.ports())))

        all_port_data = []

        for (i, node) in enumerate(self.validator_nodes):
            for (config_file, configs) in self.node_config.items():
                for (k, v) in configs.items():
                    node.set(config_file, v, k)

            if i > 0:
                ports = all_ports[i - 1]
                for (j, (key, e_port)) in enumerate(self.ports().items()):
                    node.update(
                        e_port.config_file,
                        lambda x: update_port(x, ports[j]),
                        e_port.property_path,
                    )

            port_data = [node.moniker]
            for (j, e_port) in enumerate(self.ports().values()):
                port_data.append(node.get(e_port.config_file, e_port.property_path))
            all_port_data.append(port_data)

        if self._verbose:
            print(
                tabulate.tabulate(
                    all_port_data,
                    headers=["Moniker"] + [e.title for e in self.ports().values()],
                )
            )

            print(
                tabulate.tabulate(
                    [[validator.address(self.prefix)] for validator in self.validators],
                    headers=["Validators"],
                )
            )

            print(
                tabulate.tabulate(
                    [[account.address(self.prefix)] for account in self.accounts],
                    headers=["Accounts"],
                )
            )

        for (i, node) in enumerate(self.validator_nodes):
            node.add_key(self.validators[i])
            p2p = self.ports()["p2p"]
            node.add_validator(
                Coin(self.validator_balance, self.denom), self.validators[i]
            )

            if i > 0:
                # because this
                # https://github.com/cosmos/cosmos-sdk/blob/88ee7fb2e9303f43c52bd32410901841cad491fb/x/staking/client/cli/tx.go#L599
                gentx_file = glob.glob(f"{node.home_dir}/config/gentx/*json")[0].split(
                    "/", maxsplit=1
                )[-1]
                node_p2p = node.get(p2p.config_file, p2p.property_path).rsplit(
                    ":", maxsplit=1
                )[-1]
                node.update(gentx_file, lambda x: update_port(x, node_p2p), "body.memo")
                node.sign(self.validators[i], f"{node.home_dir}/{gentx_file}")

        for i in range(1, len(self.validator_nodes)):
            for j in range(i):
                self.validator_nodes[i].copy_gentx_from(self.validator_nodes[j])
                self.validator_nodes[j].copy_gentx_from(self.validator_nodes[i])

        for node in self.validator_nodes:
            node.collect_gentx()

    def spinup(self):
        for node in self.validator_nodes:
            node.start()

    def oneshot(self):
        self.prepare()
        self.spinup()

    def teardown(self):
        for node in self.validator_nodes:
            node.close()


@click.command()
def testnet(
    chain_id: str,
    validator: int,
    account: int,
    binary: str,
    denom: str,
    prefix: str,
    coin_type: int,
    overwrite: bool,
    keep: bool,
):
    coin_type = 118

    genesis_config = {
        "app_state.gov.voting_params.voting_period": "600s",
        "app_state.mint.minter.inflation": "0.300000000000000000",
    }

    node_config = {
        "config/app.toml": {
            "api.enable": True,
            "api.swagger": True,
            "api.enabled-unsafe-cors": True,
            "minimum-gas-prices": f"0.10{denom}",
            "rosetta.enable": False,
        },
        "config/config.toml": {
            "instrumentation.prometheus": False,
            "p2p.addr_book_strict": False,
            "p2p.allow_duplicate_ip": True,
        },
    }

    net = Testnet(
        chain_id,
        n_validator=validator,
        n_account=account,
        binary=binary,
        denom=denom,
        prefix=prefix,
        coin_type=coin_type,
        genesis_config=genesis_config,
        node_config=node_config,
        account_balance=10**26,
        validator_balance=10**16,
        overwrite=overwrite,
        keep=keep,
    )

    net.oneshot()
    try:
        time.sleep(600)
    except KeyboardInterrupt:
        print("\ntear-down!")
