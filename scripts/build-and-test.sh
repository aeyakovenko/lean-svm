#!/usr/bin/env bash
set -euo pipefail

echo "=== 1. Build Lean 4 SDK, compiler, and kernel-check all formal proofs ==="
lake build

echo "=== 2. Compile all Lean 4 programs directly to Solana sBPF ELF64 (.so) ==="
mkdir -p build
lake exe lean-svm build Examples.Noop         Examples.Noop.entrypoint         -o build/noop.so
lake exe lean-svm build Examples.Counter      Examples.Counter.entrypoint      -o build/counter.so
lake exe lean-svm build Examples.Vault        Examples.Vault.entrypoint        -o build/vault.so
lake exe lean-svm build Examples.HashCheck    Examples.HashCheck.entrypoint    -o build/hashcheck.so
lake exe lean-svm build Examples.Amm          Examples.Amm.entrypoint          -o build/amm.so
lake exe lean-svm build Examples.Lending      Examples.Lending.entrypoint      -o build/lending.so
lake exe lean-svm build Examples.DutchAuction Examples.DutchAuction.entrypoint -o build/dutch_auction.so
lake exe lean-svm build Examples.BondingCurve Examples.BondingCurve.entrypoint -o build/bonding_curve.so
lake exe lean-svm build Examples.NatSub       Examples.NatSub.entrypoint       -o build/natsub.so
lake exe lean-svm build Examples.DivZero      Examples.DivZero.entrypoint      -o build/divzero.so

echo "=== 3. Compile hand-rolled #![no_std] Rust baselines (if Solana platform-tools installed) ==="
SOLANA_TOOLS="${SOLANA_TOOLS:-$HOME/.cache/solana/v1.58/platform-tools}"
if [ -x "$SOLANA_TOOLS/rust/bin/rustc" ]; then
  mkdir -p build/rust
  for name in noop counter vault dutch_auction; do
    dir="benchmarks/rust-${name//_/-}"
    "$SOLANA_TOOLS/rust/bin/rustc" \
      --crate-type cdylib --target sbpf-solana-solana \
      -C opt-level=3 -C lto=fat -C panic=abort -C strip=symbols \
      -C linker="$SOLANA_TOOLS/llvm/bin/ld.lld" \
      -C link-arg=--Bdynamic -C link-arg=-shared -C link-arg=--entry=entrypoint \
      -C link-arg=--no-rosegment -C link-arg=-z -C link-arg=notext \
      "$dir/src/lib.rs" -o "build/rust/rust_${name}.so"
  done
fi

echo "=== 4. Execute all programs & benchmarks on real LiteSVM (Agave 3.1.3) ==="
cargo run --manifest-path svm-runner/Cargo.toml --release
