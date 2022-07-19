FROM alpine AS build-env

WORKDIR /root
RUN apk add --no-cache jq git yarn
RUN git clone https://github.com/ping-pub/explorer
WORKDIR /root/explorer

RUN cat src/chains/mainnet/cosmos.json \
    | jq '.chain_name="localnet"' \
    | jq '.api=["http://0.0.0.0:1317"]' \
    | jq '.rpc=["http://0.0.0.0:26657"]' \
    | jq '.snapshot_provider=""' \
    | jq '.sdk_version="v0.45.4"' \
    | jq '.coin_type="118"' \
    | jq '.assets[0].base="stake"' \
    | jq '.assets[0].symbol="STAKE"' \
    > localnet.json

RUN rm src/chains/mainnet/*json
RUN mv localnet.json src/chains/mainnet

RUN yarn global add node-gyp && yarn && yarn build

FROM nginx:alpine

COPY --from=build-env /root/explorer/ping.conf /etc/nginx/conf.d/default.conf
COPY --from=build-env /root/explorer/dist /usr/share/nginx/html
