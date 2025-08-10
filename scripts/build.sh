#!/bin/bash

# arg1: input file path
# arg2: compiler version
# arg3: Name of the main contract

set -e

function build() {
    mkdir -p tmp/
    mkdir -p tmp/bin/
    mkdir -p tmp/abi/

    EXECUTABLE="./solc_$2"
    SOL=$(basename $1 .sol)

    ./.solc/"$EXECUTABLE" --bin --abi $1 -o tmp/
    cp tmp/$3.bin tmp/bin/$SOL.bin
    cp tmp/$3.abi tmp/abi/$SOL.abi
    rm -rf tmp/*.bin
    rm -rf tmp/*.abi
}

if [ "$#" -ne 3 ]; then
    exit 1
else
    build $1 $2 $3
fi
