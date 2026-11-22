#!/usr/bin/env bash
# Verifier-owned: launch the workbench on a spare port and run the headless-Chrome selftest.
# Usage: verify/selftest_workbench.sh [port]   (default 8439; never 8420)
set -u
cd "$(dirname "$0")/.."
PORT="${1:-8439}"
[ "$PORT" = 8420 ] && { echo "refusing port 8420"; exit 2; }
LOG="$(mktemp /tmp/leanre_verify_wb.XXXXXX.log)"
python3 workbench/server.py --port "$PORT" >"$LOG" 2>&1 &
SP=$!
trap 'kill $SP 2>/dev/null' EXIT
for i in $(seq 1 50); do curl -fsS "http://127.0.0.1:$PORT/api/health" >/dev/null 2>&1 && break; sleep 0.2; done
echo "health: $(curl -sS "http://127.0.0.1:$PORT/api/health" | head -c 300)"
PROFILE="$(mktemp -d /tmp/leanre_verify_chrome.XXXXXX)"
DOM="$(timeout 300 google-chrome --headless=new --no-sandbox --disable-gpu --user-data-dir="$PROFILE" \
  --virtual-time-budget=120000 --window-size=1600,1000 --dump-dom "http://127.0.0.1:$PORT/#selftest=1" 2>/dev/null)"
rm -rf "$PROFILE"
echo "$DOM" | python3 -c '
import sys,re,html
d=sys.stdin.read()
m=re.search(r"<[^>]*id=\"selftest\"[^>]*>(.*?)</", d, re.S)
print("SELFTEST NODE:", html.unescape(m.group(1)).strip() if m else "NOT FOUND (dom bytes=%d)"%len(d))
sys.exit(0 if (m and "SELFTEST PASS" in m.group(1)) else 1)'
RC=$?
echo "listening sockets for server pid: $(ss -ltnp 2>/dev/null | grep "pid=$SP" | awk "{print \$4}" | tr "\n" " ")"
echo "server log tail:"; tail -3 "$LOG"
exit $RC
