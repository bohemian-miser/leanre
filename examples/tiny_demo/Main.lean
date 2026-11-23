/-
Copyright (c) 2026 leanre contributors
SPDX-License-Identifier: AGPL-3.0-or-later OR MIT-0
-/
import Arithmetic
import Wrappers
import Bundles

namespace TinyDemo

/-- Headline theorem for the zero-toolchain tiny demo. -/
theorem main_theorem (n : Nat) :
    Eq (bundleWeight (mkDemoBundle n)) (bundleWeight (mkDemoBundle n)) :=
  alias_bundle_weight n

end TinyDemo
