#!/bin/bash
exec bash "$(dirname "$0")/gen-bv.sh" "$1" 65535
