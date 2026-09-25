#!/usr/bin/env bash
# Reproduce every measured number in the paper's evaluation, capturing each
# experiment's output under results/. Run from anywhere; resolves its own path.
set -euo pipefail

cd "$(dirname "$0")/.."
mkdir -p results

run() {
  local name="$1"; shift
  echo "==================================================================="
  echo "==> $name   ($(date '+%H:%M:%S'))"
  echo "==================================================================="
  # Capture stdout+stderr to the log while still echoing to the console.
  if "$@" 2>&1 | tee "results/${name}.txt"; then :; else
    echo "WARNING: ${name} exited non-zero (see results/${name}.txt)"
  fi
  echo
}

echo "ACP artifact: full reproduction run started $(date)"
echo "Environment: $(rustc --version 2>/dev/null || echo 'rustc not found')"
echo

run "01-tests"          cargo test  --release
run "02-witness-gen"    cargo run -q -p acp-bench   --release
run "03-stark"          cargo run -q -p acp-circuit --release
run "04-absence"        cargo run -q -p acp-absence --release
run "05-integrated"     cargo run -q -p acp --bin acp --release
run "06-detection"      cargo run -q -p acp --bin acp --release -- detect
run "07-scale-one18"    cargo run -q -p acp-circuit --release -- one 18
run "08-scale-shard"    cargo run -q -p acp-circuit --release -- shard 18 16
run "09-comparison"     cargo run -q -p acp --bin acp-compare --release
run "10-bound-circuit"  cargo test -p acp-circuit --release --test bind_measure -- --nocapture --test-threads=1
run "10b-batched-binding" cargo test -p acp-circuit --release --test bind_batch_measure -- --nocapture --test-threads=1
run "11-blind-circuit"  cargo test -p acp-circuit --release --test blind_measure -- --nocapture --test-threads=1
run "12-zk-overhead"   cargo test -p acp-circuit --release --test zk_measure -- --nocapture --test-threads=1
run "13-mono"          cargo test -p acp-circuit --release --test mono_measure -- --nocapture --test-threads=1
run "14-real-oracle"   python3 scripts/validate_real_oracle.py

echo "All experiments finished $(date)."
echo "Per-experiment logs are in: results/"
