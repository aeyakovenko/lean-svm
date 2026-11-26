/-
  Examples.DivZero
  Lean's `UInt64.div`/`mod` are total: `x / 0 = 0`, `x % 0 = x`.
  `lean-svm` emits raw `div64`/`mod64`, which trap on Solana (DivideByZero).
-/
import LeanSVM

open LeanSVM

namespace Examples.DivZero

def entrypoint (input : Ptr) : SolanaM Unit := do
  let (acc, _ix, _pid) ← Input.parse1 input
  let d ← AccountView.readDataU64 acc 0
  let q := (1000 : UInt64) / d
  let r := (1000 : UInt64) % d
  let z := q ^^^ r
  AccountView.writeDataU64 acc 8 z
  log64 z d q r 0

end Examples.DivZero
