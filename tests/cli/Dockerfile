FROM archlinux:base-devel

RUN pacman -Syu --noconfirm --needed git poetry opam java-runtime go jq

RUN opam init -y
RUN opam install mdx -y

RUN git clone --branch v0.45.8 https://github.com/cosmos/cosmos-sdk

WORKDIR /cosmos-sdk
RUN make build
RUN install -Dt "/usr/local/bin" "build/simd"

WORKDIR /
RUN git clone https://github.com/informalsystems/atomkraft

WORKDIR /atomkraft
RUN poetry install -n
RUN poetry run atomkraft model apalache get
RUN poetry run python -m pip install pyflakes==2.4.0 black pylama[all]

WORKDIR /atomkraft/tests/cli
ENTRYPOINT [ "/atomkraft/tests/cli/docker_entrypoint.sh" ]
