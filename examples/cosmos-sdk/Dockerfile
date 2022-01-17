# This docker image extends the docker image of EVMOS:
# https://github.com/tharsis/evmos/blob/main/Dockerfile
#
# Modified by Informal Systems for the audit purposes.

FROM golang:alpine AS build-env

# Install minimum necessary dependencies
ENV PACKAGES curl make git libc-dev bash gcc linux-headers eudev-dev python3
RUN apk add --no-cache $PACKAGES

# Set working directory for the build
WORKDIR /go/src/github.com/cosmos/cosmos-sdk

# Download and install cosmos-sdk
RUN git clone https://github.com/cosmos/cosmos-sdk /go/src/github.com/cosmos/cosmos-sdk
RUN git checkout v0.44.3
RUN make clean && make build-linux

# Final image
FROM alpine:edge

# Install ca-certificates
RUN apk add --update ca-certificates jq perl
WORKDIR /root

# Copy over binaries from the build-env
COPY --from=build-env /go/src/github.com/cosmos/cosmos-sdk/build/simd /usr/bin/simd

EXPOSE 26656 26657 1317 9090

# setup the genesis file
ADD ./chain-setup /opt/chain
WORKDIR /opt/chain/
RUN /opt/chain/init.sh
