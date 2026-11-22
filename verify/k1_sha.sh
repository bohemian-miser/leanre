#!/usr/bin/env bash
# K1 (verifier-owned): independent SHA-256 + byte counts of data/solution.ndjson.zst.
# Does NOT read data/solution.ndjson.zst.sha256 or any worker-reported value.
set -u
cd "$(dirname "$0")/.."
F=data/solution.ndjson.zst
EXP_C=61a8938ad5f5e57397c1c0e3b954916af546d9004ade01c3555744a681b05381
EXP_U=5ea74b912147c5c93cc2b6d70cc727cf908df2f62ac6a20480a3fa02f6be244e
EXP_CB=7699933588
EXP_UB=61570595788
[ -f "$F" ] || { echo "MISSING $F"; exit 2; }
date -u +"start %FT%TZ"
CB=$(stat -L -c %s "$F")
C=$(sha256sum "$F" | cut -d' ' -f1)
TMP=$(mktemp)
U=$(zstd -d -c --long=31 "$F" | tee >(wc -c >"$TMP") | sha256sum | cut -d' ' -f1)
sleep 1; UB=$(cat "$TMP"); rm -f "$TMP"
rc=0
chk(){ if [ "$2" = "$3" ]; then echo "PASS $1 $2"; else echo "FAIL $1 measured=$2 expected=$3"; rc=1; fi; }
chk compressed_bytes "$CB" "$EXP_CB"
chk compressed_sha256 "$C" "$EXP_C"
chk uncompressed_bytes "$UB" "$EXP_UB"
chk uncompressed_sha256 "$U" "$EXP_U"
date -u +"end %FT%TZ"
exit $rc
