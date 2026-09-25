# ACP prototype --- artifact-evaluation entry points.
# Run from this directory (acp-prototype/), e.g.  make smoke  /  make all.

CARGO   ?= cargo
REL     := --release
RESULTS := results

.PHONY: all build test smoke bench-witness bench-stark bench-absence \
        integrate detect scale compare bind bind-batch blind zk mono \
        validate-oracle results-dir clean help

help:
	@echo "ACP prototype targets:"
	@echo "  make build          - compile all crates (release)"
	@echo "  make test           - run all unit/integration tests"
	@echo "  make smoke          - quick kick-the-tires (build + test + detect), ~2-3 min"
	@echo "  make all            - reproduce every measured number into $(RESULTS)/, ~12-15 min"
	@echo "  make bench-witness  - P2: out-of-circuit witness-generation benchmarks"
	@echo "  make bench-stark    - P3: unbound path-hashing sweep"
	@echo "  make bind-batch     - P3: batched bound coverage proof (Table 1)"
	@echo "  make bench-absence  - P4: signed-registry absence oracle (ML-DSA-65)"
	@echo "  make integrate      - P5: integrated prover/verifier + coverage-soundness demo"
	@echo "  make detect         - P8: detection-vs-concealment sweep"
	@echo "  make scale          - P6: single-shot 2^18 + 4-way sharding"
	@echo "  make compare        - P8: shared-core vs ACP comparison baseline"
	@echo "  make bind           - bound single-path circuit (leaf-bound) figures"
	@echo "  make blind          - blind (branch-hiding) circuit figures"
	@echo "  make mono           - VPQM epoch-monotonicity circuit (measured)"
	@echo "  make validate-oracle - offline check of captured live CT/DNSSEC evidence"
	@echo "  make clean          - cargo clean"

build:
	$(CARGO) build $(REL)

test:
	$(CARGO) test $(REL)

smoke: build
	$(CARGO) test $(REL)
	$(CARGO) run -q -p acp --bin acp $(REL) -- detect

bench-witness:
	$(CARGO) run -q -p acp-bench $(REL)

bench-stark:
	$(CARGO) run -q -p acp-circuit $(REL)

bind-batch:
	$(CARGO) test -p acp-circuit $(REL) --test bind_batch_measure -- --nocapture --test-threads=1

bench-absence:
	$(CARGO) run -q -p acp-absence $(REL)

integrate:
	$(CARGO) run -q -p acp --bin acp $(REL)

detect:
	$(CARGO) run -q -p acp --bin acp $(REL) -- detect

scale:
	$(CARGO) run -q -p acp-circuit $(REL) -- one 18
	$(CARGO) run -q -p acp-circuit $(REL) -- shard 18 16

compare:
	$(CARGO) run -q -p acp --bin acp-compare $(REL)

# The bound- and blind-circuit figures live in #[test] harnesses, so they need
# --nocapture to print and --test-threads=1 to avoid CPU contention skewing the
# timings (parallel runs inflate per-proof time roughly 2x).
bind:
	$(CARGO) test -p acp-circuit $(REL) --test bind_measure -- --nocapture --test-threads=1

blind:
	$(CARGO) test -p acp-circuit $(REL) --test blind_measure -- --nocapture --test-threads=1

zk:
	$(CARGO) test -p acp-circuit $(REL) --test zk_measure -- --nocapture --test-threads=1

# VPQM epoch-to-epoch monotonicity circuit (two-tree path opening + status
# ordering).  This is the dominant cost of the full migration relation.
mono:
	$(CARGO) test -p acp-circuit $(REL) --test mono_measure -- --nocapture --test-threads=1

# Offline: verifies the captured real-oracle fixtures in tests/fixtures/
# (live Nimbus2026 CT signed tree head; a DNSSEC NSEC denial-of-existence for
# ietf.org plus its DNSKEY chain link). No network needed.
validate-oracle:
	python3 scripts/validate_real_oracle.py

results-dir:
	mkdir -p $(RESULTS)

all: build results-dir
	./scripts/run_all.sh

clean:
	$(CARGO) clean
