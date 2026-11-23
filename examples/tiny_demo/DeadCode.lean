/-
Copyright (c) 2026 leanre contributors
SPDX-License-Identifier: AGPL-3.0-or-later OR MIT-0
-/
import Arithmetic

namespace TinyDemo

/-- Unused branch unreachable from `TinyDemo.main_theorem`. -/
def deadHelper (n : Nat) : Nat :=
  doubleStep n

theorem dead_branch_eq (n : Nat) : Eq (deadHelper n) (deadHelper n) :=
  core_refl_nat (deadHelper n)

theorem dead_unused_note_eq (b : ProofBundle) : Eq b.unusedNote b.unusedNote :=
  core_refl_nat b.unusedNote

end TinyDemo
