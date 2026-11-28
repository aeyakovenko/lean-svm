# `lean-svm` — Native Lean 4 → Solana sBPF v3 Optimizing Compiler Toolchain

> **⚠️ Educational & Research Purposes Only — Not Audited for Production Use**
>
> This software, compiler toolchain, formal proofs, and example programs are provided **strictly for educational and research purposes**. They have **not** undergone an independent third-party security audit and are **not** intended for production deployment or custody of real user funds. Formal proofs cover only the explicitly stated models and properties and do not guarantee the absence of bugs in unmodeled runtime boundaries, compiler passes, or downstream integrations. Use at your own risk — provided **"AS IS"** without warranty of any kind under the [Apache License 2.0](LICENSE).

`lean-svm` is a **native, zero-dependency Lean 4 to Solana SVM (sBPF) compiler toolchain** that compiles formally verified Lean 4 programs **directly from Lean's monomorphic LCNF IR into minimal Solana sBPF ELF64 (`.so`) bytecode** — with **zero heap allocations**, **no C runtime**, **no LLVM**, and **no external Lean dependencies**.

Write Solana on-chain programs in Lean 4, prove critical invariants (lamport conservation, constant-product $k' \ge k$, LTV solvency, monotonic Dutch price decay, overflow rejection) directly in Lean 4's kernel with zero `sorry` and zero custom axioms, and compile the exact same definitions directly to sBPF binaries that **beat hand-rolled `#![no_std]` Rust (`rustc` + LLVM 22 `-O3`)** on both `.so` object size and Compute Units (CUs).

---

## Benchmarks (Verified on Real LiteSVM `0.18.2` / sBPF v3)

### Head-to-Head: `lean-svm` (Lean 4, sBPF v3) vs Hand-Rolled `#![no_std]` Rust (Solana `rustc 1.95` / LLVM 22 `-O3 -C lto=fat -C strip=symbols`)

All Rust baselines are zero-dependency `#![no_std]` raw-pointer programs (leaner than Anchor and Pinocchio), compiled with Solana platform-tools `v1.58`, and executed on identical transactions in `litesvm`.

| Program | LeanSVM `.so` | Rust `-O3` `.so` | Size Advantage | LeanSVM CUs | Rust `-O3` CUs | Heap |
|---|---:|---:|---:|---:|---:|---:|
| **Noop** | **352 B** | 1,136 B | **3.23× smaller** | **2 CU** | 2 CU | 0 B |
| **Counter** (init / inc / add, owner+size hardened) | **1,256 B** | 1,696 B | **1.35× smaller** | **45 / 50 / 52 CU** | 27 / 32 / 37 CU | 0 B |
| **Vault** (3 accs + owner+alias+32B eq + `sol_log_`) | **2,472 B** | 2,304 B | 0.93× *(hardened)* | **195 CU** | 177 CU | 0 B |
| **DutchAuction** (Token-2022 NFT + Clock + CPI + pinned IDs) | **8,504 B** | 12,984 B | **1.53× smaller** | **3,296 / 4,672 CU** | 3,096 / 4,735 CU | 0 B |

### Full Formally Verified DeFi & NFT Protocol Suite (SPL Token + SPL Token-2022 on LiteSVM)

| Program | Instructions | `.text` | Stack | Heap | `.so` Size | LiteSVM CUs | Formal Lean 4 Proofs |
|---|---:|---:|---:|---:|---:|---|---|
| [`Examples.Noop`](Examples/Noop.lean) | 2 | 16 B | 0 B | 0 B | **352 B** | 2 | `noop_always_succeeds` |
| [`Examples.Counter`](Examples/Counter.lean) | 115 | 920 B | 0 B | 0 B | **1,256 B** | 45 / 50 / 52 | `counter_increment_adds_one`, `counter_increment_overflow_rejected`, `counter_rejects_wrong_owner` |
| [`Examples.Vault`](Examples/Vault.lean) | 181 | 1,448 B | 0 B | 0 B | **2,472 B** | 195 | `vault_transfer_conserves_lamports`, `vault_rejects_insufficient_funds` |
| [`Examples.HashCheck`](Examples/HashCheck.lean) | 100 | 800 B | 56 B | 0 B | **1,936 B** | 413 | `sol_sha256` + `sol_get_clock_sysvar` + `sol_log_` |
| [`Examples.Amm`](Examples/Amm.lean) (SPL + Token-2022) | 1,350 | 10,800 B | 384 B | 0 B | **11,728 B** | init 292, addLiq 4,690, swap 4,690, remLiq 4,708 | `amm_swap_preserves_k`, `amm_swap_never_drains_reserve` |
| [`Examples.Lending`](Examples/Lending.lean) (SPL + Token-2022) | 1,414 | 11,312 B | 384 B | 0 B | **12,368 B** | init 463, dep 1,812, bor 3,498, liq 5,013, rep 3,372 | `lending_repay_monotone`, `lending_healthy_cannot_be_liquidated`, `lending_initObligation_zero_inits_dirty_mem` |
| [`Examples.DutchAuction`](Examples/DutchAuction.lean) (Token-2022 NFT) | 937 | 7,496 B | 384 B | 0 B | **8,504 B** | create 3,296, buyNow 4,672 | `dutchPrice_bounded`, `dutchPrice_monotone` |
| [`Examples.BondingCurve`](Examples/BondingCurve.lean) (Token-2022 Mint/Burn) | 991 | 7,928 B | 304 B | 0 B | **8,888 B** | init 227, buy 4,980, sell 3,701 | `curve_buy_preserves_k`, `curve_sell_bounded_by_reserve` |

*(Note: For CPI programs, ~1,200–4,200 CUs of the transaction total come from the SPL Token / Token-2022 / System Program CPI executions themselves; LeanSVM program compute overhead is typically only ~100–400 CUs.)*

---

## Compiler Architecture

```
Lean 4 Source (.lean) + Kernel-Checked Proofs (Prop)
   │
   ▼  Lean 4 Elaborator & Kernel (erases all proofs, types, universes)
Lean 4 Monomorphic LCNF (`Lean.Compiler.LCNF.monoExt`)
   │
   ▼  LeanSVM.Compiler.Lower
      • Zero-cost erasure of `SvmState` ghost tokens, `Unit`, `Prop`
      • Scalar Replacement of Aggregates (SROA) for structs & slices
      • Unboxed `SvmStep` / `Option` / `Bool` / enums (0 heap objects)
      • Join-point continuation inlining (O(N) code size)
      • Tail-recursive functions → zero-call CFG loops
      • Call-site-count smart auto-outlining into 1-CU sBPF `call` functions
      • Automatic stack argument-packing for `> 5`-arg outlined helpers (up to 12 scalar params)
      • Reusable per-function out-pointer & arg-pack stack slots + high-water-mark frame reuse
   │
   ▼  LeanSVM.Compiler.Optimize (fixed-point SSA pipeline)
      • Copy & constant block-parameter propagation
      • SSA unsigned interval range analysis (`VRange`: safe `ALU32 → ALU64` promotion, redundant low-bit mask elimination, range-proven comparison/branch folding)
      • Constant folding & power-of-2 strength reduction (`mul/div/mod` → `lsh/rsh/and`)
      • Immediate operand folding (`binImm`, `storeImm` → `stdw`/`stw`/`sth`/`stb`) and constant-length `sol_memset_` inline expansion (`≤ 5` stores / `≤ 40 B`)
      • Address-offset & direct `r10` stack load/store folding (`[r10 - off]`)
      • Compare-and-branch fusion & operand flipping (`1 <= r` → `r >= 1`)
      • Local pure-ALU CSE, load-CSE, store-to-load forwarding, DCE, and interprocedural dead-helper elimination (`removeDeadHelpers`)
      • Constant-return AND variable-return exit-block tail-merging (eliminates hot-path error spills!)
      • Balanced O(log2 N) binary-search switch dispatch (`switchDispatchPass`)
   │
   ▼  LeanSVM.Compiler.RegAlloc
      • Loop-aware RPO block ordering + natural loop 10× use weighting
      • SSA constant rematerialization (`Loc.imm`, zero register pressure / zero spills)
      • Exact iterative backward `liveIn`/`liveOut` CFG liveness
      • Coalescing linear-scan allocator over sBPF `r0..r9` (`r6..r9` callee-saved across calls)
      • Lifetime-verified spill-slot recycling (0 stack bytes when no spills or stack buffers)
   │
   ▼  LeanSVM.Compiler.Validate (formally verified Translation Validator)
      • Mandatory post-optimize CFG/call-target/shift-immediate check (`checkProgramCFG`)
      • Mandatory post-RegAlloc allocation & live-range interference certificate (`checkAllocCert`)
      • Certifies frame bounds (`≤ 4096 B`), spill-slot disjointness from user `stackAlloc` buffers,
        `r5` scratch safety, callee-saved call preservation, and pairwise live-range non-interference
   │
   ▼  LeanSVM.Compiler.CodeGen + LeanSVM.SBPF.Peephole
      • Commutative 2-address operand swapping (1 insn instead of 3)
      • Cycle-safe parallel register/stack edge moves + zero-cost no-op edge elision
      • Basic-block register value tracking (`bbValueTrackPass` across constants & stack slots)
      • Branch-over-jump inversion, jump-to-exit forwarding, `mov+ldx` folding, `lddw` shrinking
   │
   ▼  LeanSVM.SBPF.ELF
      • Direct sBPF v3 ELF64 `.so` linker & serializer (`e_flags = 3`, static syscalls, 0 relocations)
      • Zero-copy contiguous RO sections (`Section::Borrowed`); dynamic tables omitted when unused
```

---

## Project Layout

- [`LeanSVM/Types.lean`](LeanSVM/Types.lean) — Zero-copy `Ptr`, `AccountView`, `ByteSlice`, `Err`, and Solana ABI v1 offsets
- [`LeanSVM/Sha256.lean`](LeanSVM/Sha256.lean) — Pure, zero-dependency FIPS 180-4 SHA-256 with kernel-checked NIST test vectors (`""`, `"abc"`, 56B multi-block)
- [`LeanSVM/Runtime.lean`](LeanSVM/Runtime.lean) — Pure functional `SvmState` verification model + `@[noinline]` hardware/syscall intrinsics (exact `sol_memcmp_`, full 40B `sol_get_clock_sysvar`, byte-exact `sol_sha256`, and Agave write-protected `sol_invoke_signed_c` with built-in SPL Token / Token-2022 / System Program CPI handler + universal frame & mutation proofs)
- [`LeanSVM/Input.lean`](LeanSVM/Input.lean) — Demand-driven zero-copy account cursor, inline/auto-outlined 32-byte `pubkeyEq`/`pubkeyCopy`, checked arithmetic
- [`LeanSVM/Math.lean`](LeanSVM/Math.lean) — Overflow-safe 128-bit `mulDiv64` / `mulDiv64Ceil` (fast 64-bit path + shared 128-bit fallback) & Newton `isqrt64`, with kernel-checked exact 128-bit arithmetic + memory-frame specs (`mul128_split_exact`, `div128Loop_exact`, `mulDiv64_ok_spec`, `mulDiv64Ceil_ok_spec`)
- [`LeanSVM/CPI.lean`](LeanSVM/CPI.lean) — Zero-heap stack-allocated `sol_invoke_signed_c` CPIs for **SPL Token**, **SPL Token-2022** (`TransferChecked`, `MintTo`, `Burn`, `InitializeAccount3`), PDA signing, and `SystemProgram` (`Transfer`, PDA-signed `Allocate`, PDA-signed `Assign`), plus formally verified canonical program-ID pinning (`checkSystemProg`, `checkTokenProg`, `checkTokenOr2022Prog`) and dirty-memory zero-initialization (`zeroWords`, `zeroWords_exact`)
- [`LeanSVM/SBPF/`](LeanSVM/SBPF/) — Native sBPF v3 ISA encoder, Murmur3-32 hasher, disassembler, peephole & value-tracking optimizer, and ELF64 `.so` linker
- [`LeanSVM/Compiler/`](LeanSVM/Compiler/) — `IR`, `Lower`, `Optimize`, `RegAlloc`, **`Validate`**, `CodeGen`, `Driver`, and **`Proofs`** (87 kernel-checked compiler soundness theorems)
- [`.agents/skills/svm-security-testing/SKILL.md`](.agents/skills/svm-security-testing/SKILL.md) — Reusable agent & developer security skill covering common SVM vulnerabilities (same-tx account revival, dirty-buffer init, owner/size/discriminator checks, spoofed `noop.so` CPIs, SPL/lamport self-transfer aliasing, share-pool inflation, and LiteSVM + `SvmState.mem` proof patterns)

---

## Formal Compiler Soundness (`LeanSVM/Compiler/Proofs.lean`)

The production compiler passes (`Lower`, `CodeGen`, `RegAlloc`, `Validate`, `Optimize`, `Peephole`, and `ISA`) are directly machine-checked against a formal small-step sBPF machine semantics in [`LeanSVM/Compiler/Proofs.lean`](LeanSVM/Compiler/Proofs.lean) (**87 theorems, 0 `sorry`, 0 custom axioms**, plus 13 syscall/CPI/memory-model theorems in [`LeanSVM/Runtime.lean`](LeanSVM/Runtime.lean) and 4 FIPS 180-4 SHA-256 theorems in [`LeanSVM/Sha256.lean`](LeanSVM/Sha256.lean)):

- **Certified Translation Validator & End-to-End RegAlloc → CodeGen Bridge:** **`checkProgramCFG_sound`**, **`locWellFormed_sound`**, **`locsConflict_false_sound`**, **`vregLocValid_sound`**, **`stmtDstValid_sound`**, **`checkStmtsBackward_sound`**, **`checkAllocCert_stack_frame_sound`**, and **`checkAllocCert_bridges_emitStmt_binOp`** (proves that every `checkAllocCert = true` certificate directly discharges ALL `CodeGen.emitStmt_binOp_sound` register-validity, scratch-disjointness, and non-interference preconditions — removing `RegAlloc` from the TCB!).
- **sBPF v3 ISA Soundness & Trap Preservation:** **`sbpf_opcodes_disjoint`** (proves all ALU/LDX/STX/ST_IMM/NEG64 opcodes pairwise distinct on sBPF v3, ruling out the `0x87` collision), **`neg64_v3_sound`** (`NEG64 (0x87)`, SIMD-0377), **`subImm_to_addImm_sound`** (normalizing `subImm` to `addImm (-imm)` for sBPF v3 SIMD-0174 operand order), **`BinOp.maskShiftImm_sound`**, and **`divMod_hasSideEffect_sound`** (DCE preserves division/modulo-by-zero traps).
- **Exact Solana sBPF `ALU32` Sign-Extension Semantics:** `signExt32U32_toUInt32`, **`evalAlu32SBPF_fixup`** (models real Agave sBPF v3 sign-extension on `add32`/`sub32`/`mul32` and proves the emitted `mov32 d, d` fixup restores exact zero-extended Lean `UInt32` semantics across every `emitStmt` binOp/binImm path).
- **Memory & Stack Disjointness:** `loadBytes_storeBytes_b8_same`, `loadBytes_storeBytes_b1_same`, `loadBytes_storeBytes_b8_nonOverlapping_stack` (proves non-overlapping 8-byte stack-slot invalidation in `bbValueTrackPass`).
- **ISA Encoding & Constant Materialization:** **`pushRawInsn_roundtrip`** (bit-for-bit 8-byte binary encoding/decoding inverse on production `SBPF.pushRawInsn`), `fitsInt32_signExt32`, `fitsUInt32_zeroExt32`, `emitConst64_sound`, `JmpCond.invert_sound`, `CmpOp.toJmpCond_sound`, `CmpOp.invert_sound`, `CmpOp.flip_sound`, `BinOp.isCommutative_sound`.
- **Lowering Fallibility Analysis (Closes Transitive Error-Elision Bugs):** **`mayFailCheck_sound`**, **`mayFailCheck_unknown_failSafe`** (proves transitive `codeMayFail` soundness across arbitrary helper call chains and fail-safe rejection of unknown/external callees).
- **Optimizer, Interval Range Analysis, Inline `memset` & Dead-Helper Soundness:** `log2IfPow2_spec`, `mul64_pow2_eq_lsh64`, `div64_pow2_eq_rsh64`, `mod64_pow2_eq_and64`, `posInt32_imm_ext_eq`, `opt_algebraic_identities`, `add64_combine_imm_sound`, **`VRange.join_sound`**, **`VRange.forMemSize_sound`**, **`VRange.evalBinOp_sound`**, **`VRange.evalBinImm_sound`**, **`VRange.canPromoteAlu32_sound`**, **`VRange.canPromoteAlu32_imm_sound`**, **`VRange.lowBitMask_noop_sound`**, **`VRange.evalCmp?_sound`**, **`planMemsetStores_sound`**, and **`removeDeadHelpers_sound`**.
- **Peephole Rewrite Soundness:** `shrinkInsn_sound`, `peephole_mov_ldx_sound`, `peephole_mov_swap_drop_sound`, `peephole_stx_ldx_b8_same_sound`, `peephole_stx_ldx_b8_diff_sound`, `peephole_add64_combine_sound`, **`overwritesRegWithoutReading_sound`**, **`peephole_fallible_ret_check_sound`**, **`peephole_dead_mov_sound`**, **`peephole_mov32_copy_narrow_sound`**, and **`peephole_redundant_mov32_elim_sound`**.
- **CodeGen Soundness, Cycle-Safe Moves & Zero-Clobber Frame Conditions:** `loadVReg_sound`, `storeVReg_sound`, `emitSingleLocMove_sound`, **`emitParallelLocMoves_regSwap_sound`**, **`emitParallelLocMoves_stackSwap_sound`** (cycle-breaking 2-register and 2-stack-slot swaps directly on production `CodeGen.emitParallelLocMoves`), **`emitStmt_cmp_sound`**, **`emitStmt_binOp_sound`** (all 21 64/32-bit ops with direct `dst` scratch loading across all reg/stack/imm combinations), `emitStmt_binImm_sound`, `emitStmt_constImm_sound`, `emitStmt_mov_sound`, `emitStmt_neg64_sound`, `emitStmt_load_sound`, `emitStmt_store_sound`, `emitStmt_storeImm_sound`, `emitStmt_loadStack_sound`, `emitStmt_storeStack_sound`, `emitStmt_storeStackImm_sound`, `emitStmt_stackAddr_sound`.
- **RegAlloc Scratch Safety:** `funcUsesScratchR5_complete` (proves `r5` is reserved whenever any `.binOp`, `.cmp`, `.store`, or `.brCmp` reloads a `.stack` or rematerialized `.imm` operand into `r5`).
- [`Examples/`](Examples/) — 8 formally verified Solana programs (`Noop`, `Counter`, `Vault`, `HashCheck`, `Amm`, `Lending`, `DutchAuction`, `BondingCurve`)
- [`svm-runner/`](svm-runner/) — Minimal-dependency LiteSVM (`0.18.2` / Agave `4.x`, sBPF v3) end-to-end test & Rust comparison benchmark runner
- [`benchmarks/`](benchmarks/) — Zero-dep `#![no_std]` hand-rolled Rust baseline programs

---

## Quick Start

```bash
# 1. Build SDK, compiler, and verify all Lean 4 formal proofs
lake build

# 2. Compile any Lean 4 entrypoint directly to a Solana sBPF v3 .so binary
lake exe lean-svm build Examples.Amm Examples.Amm.entrypoint -o build/amm.so

# Optional flags:
#   --dump-ir      Print raw and optimized SbfIR
#   --dump-asm     Print generated sBPF v3 assembly

# 3. Run full build + compile + LiteSVM verification & head-to-head Rust benchmarks
./scripts/build-and-test.sh
```

---

## License & Disclaimer

Licensed under the [Apache License, Version 2.0](LICENSE).

This repository is experimental and provided **for educational and research purposes only**. Do not deploy compiled binaries or example programs to mainnet with real funds without thorough independent auditing and end-to-end verification.
