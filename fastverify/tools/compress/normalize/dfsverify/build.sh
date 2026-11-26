#!/bin/bash
# build dfsverify (C++17, no dependencies) next to this script
cd "$(dirname "$(readlink -f "$0")")" && g++ -O2 -std=c++17 -pthread -o dfsverify dfsverify.cpp
