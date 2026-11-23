/-
Copyright (c) 2026 David A. Dalrymple. All rights reserved.
Released under MIT OR Apache-2.0 license as described in the file LICENSE.
Authors: dhai (davidad's Humanis AIs)
-/
import Wasserstein

open MeasureTheory
open scoped ENNReal

section
local instance : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩

example : CompleteSpace (WassersteinLp 1 ℝ) := inferInstance
end
