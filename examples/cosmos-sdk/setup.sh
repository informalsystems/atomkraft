#!/usr/bin/env bash

DIR=`dirname $0`
DIR=`cd "$DIR"; pwd`

docker build -t cosmos-image "$DIR"
