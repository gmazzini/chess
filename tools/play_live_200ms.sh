#!/bin/sh
set -e

cd "$(dirname "$0")/.."

gcc -std=c89 -Wall -Wextra -O2 sqchess.c -lm -pthread -o sqchess

SFCHESS_TIMEOUT="${SFCHESS_TIMEOUT:-200}" stdbuf -oL ./play_clean.sh | ./tools/live_board.py
