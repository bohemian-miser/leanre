/-
Copyright (c) 2026 leanre contributors
SPDX-License-Identifier: AGPL-3.0-or-later OR MIT-0
-/
import Bundles

namespace TinyDemo

def doubleStep (n : Nat) : Nat :=
  Nat.succ (Nat.succ n)

def bundleWeight (b : ProofBundle) : Nat :=
  b.coreWeight

theorem core_refl_nat (n : Nat) : Eq n n :=
  Eq.refl n

theorem bundle_weight_refl (n : Nat) :
    Eq (bundleWeight (mkDemoBundle n)) (bundleWeight (mkDemoBundle n)) :=
  core_refl_nat (bundleWeight (mkDemoBundle n))

end TinyDemo
