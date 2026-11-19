#!/bin/bash
# Build PackingCube10 with a bounded number of Lean processes for the 41 data files.
# A data file needs up to 28 GB of memory, so `lake build PackingCube10`, which starts one
# process per core, runs out of memory on a machine with less than that per core.
# Run from lean/. PAR (default 1) is the number of data files checked at once.
# Prints one line per batch: the modules, lake's exit code and the seconds it took.
set -uo pipefail
PAR=${PAR:-1}
lake build Packing.Cube10Main || exit 1
fail=0
set -- $(ls Packing/Cube10D[0-9]*.lean | sed 's#Packing/#Packing.#; s#\.lean$##')
while [ $# -gt 0 ]; do
  batch=""
  n=0
  while [ $# -gt 0 ] && [ $n -lt "$PAR" ]; do batch="$batch $1"; shift; n=$((n + 1)); done
  s=$(date +%s)
  lake build $batch > .cube10_build.log 2>&1
  rc=$?
  printf '%s\t%s\t%s\n' "${batch# }" "$rc" "$(( $(date +%s) - s ))"
  if [ $rc -ne 0 ]; then fail=1; tail -20 .cube10_build.log >&2; fi
done
rm -f .cube10_build.log
[ $fail -eq 0 ] || exit 1
lake build PackingCube10
