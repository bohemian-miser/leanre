/-
Copyright (c) 2026 leanre contributors
SPDX-License-Identifier: AGPL-3.0-or-later OR MIT-0
-/
import Arithmetic

namespace TinyDemo

/-- Forwarding alias wrapper (`value_nodes = 1` in the kernel export). -/
theorem alias_bundle_weight :
    ∀ n : Nat, Eq (bundleWeight (mkDemoBundle n)) (bundleWeight (mkDemoBundle n)) :=
  bundle_weight_refl

end TinyDemo
