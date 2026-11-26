/-
  Examples.NatSub
  Lean's `Nat.sub` saturates at 0. `lean-svm` lowers `Nat.sub` to a wrapping
  64-bit `sub64`, so `(0 : Nat) - 1` becomes 0xFFFFFFFFFFFFFFFF on-chain.
-/
import LeanSVM

open LeanSVM

namespace Examples.NatSub

def entrypoint (input : Ptr) : SolanaM Unit := do
  let (acc, _ix, _pid) ← Input.parse1 input
  let seed ← AccountView.readDataU64 acc 0
  let n : Nat := seed.toNat
  let m : Nat := n - 1
  let z : UInt64 := m.toUInt64
  AccountView.writeDataU64 acc 8 z
  log64 z seed 0 0 0

end Examples.NatSub
