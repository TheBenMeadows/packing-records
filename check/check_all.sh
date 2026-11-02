#!/bin/sh
# Re-check every submission file against ../cells.csv. Last line: PASS or FAIL.
cd "$(dirname "$0")" && exec python3 check_all.py
