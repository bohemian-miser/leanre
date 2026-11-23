/-
Copyright (c) 2026 leanre contributors
SPDX-License-Identifier: AGPL-3.0-or-later OR MIT-0
-/

namespace TinyDemo

/-- A 1-constructor structure where `coreWeight` is projected in the live
proof cone, while `unusedNote` is only touched by dead code (1 unread field). -/
structure ProofBundle where
  coreWeight : Nat
  unusedNote : Nat

def mkDemoBundle (n : Nat) : ProofBundle :=
  { coreWeight := n, unusedNote := Nat.zero }

end TinyDemo
