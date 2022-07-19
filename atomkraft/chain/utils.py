import asyncio
import json
import socket

import websockets
from jsonrpcclient import responses
from jsonrpcclient.requests import request_json


def get_free_ports(n):
    socks = []
    ports = []
    for _ in range(n):
        sock = socket.socket()
        sock.bind(("", 0))
        ports.append(sock.getsockname()[1])
        socks.append(sock)
    for sock in socks:
        sock.close()
    return ports


def update_port(old, new):
    old_port = old.split(":")[-1]
    return old.replace(old_port, str(new))


class TmEventSubscribe:
    def __init__(self, params):
        self.params = params

    async def _subscribe(self, params):
        self.websocket = await websockets.connect("ws://0.0.0.0:26657/websocket")
        self.query = " AND ".join(
            f"{key} = '{value}'" for (key, value) in params.items()
        )
        req = request_json("subscribe", params={"query": self.query})
        await self.websocket.send(req)

    def __enter__(self):
        self.loop = asyncio.new_event_loop()
        self.loop.run_until_complete(self._subscribe(self.params))
        return self

    async def _wait(self):
        while True:
            msg = responses.to_result(json.loads(await self.websocket.recv()))
            if "query" in msg.result and msg.result["query"] == self.query:
                break

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.loop.run_until_complete(self._wait())
        self.loop.run_until_complete(self.websocket.close())
        self.loop.close()
