/-
Copyright (c) 2026 David A. Dalrymple. All rights reserved.
Released under MIT OR Apache-2.0 license as described in the file LICENSE.
Authors: dhai (davidad's Humanis AIs)
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Countable Minkowski inequality

The extended `Lᵖ` seminorm of a sum of nonnegative functions is at most the sum of their
seminorms, including when one or both sides are infinite. We pass from finite sums to the
countable sum by monotone convergence for finite exponents, and by a countable
intersection of almost-everywhere bounds for `p = ∞`.
-/

public section

open Filter Finset
open scoped ENNReal

namespace MeasureTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {p : ℝ≥0∞}

/-- The extended `Lᵖ` seminorm preserves suprema of countable, upward directed families of
almost everywhere measurable nonnegative functions. -/
theorem eLpNorm_iSup_ennreal [Countable ι] {f : ι → Ω → ℝ≥0∞}
    (hf : ∀ i, AEMeasurable (f i) μ) (hd : Directed (· ≤ ·) f) :
    eLpNorm (fun x ↦ ⨆ i, f i x) p μ = ⨆ i, eLpNorm (f i) p μ := by
  have hs : AEMeasurable (fun x ↦ ⨆ i, f i x) μ := AEMeasurable.iSup hf
  have hle : (⨆ i, eLpNorm (f i) p μ) ≤ eLpNorm (fun x ↦ ⨆ i, f i x) p μ :=
    iSup_le fun i ↦ eLpNorm_mono_eNorm (hf i).aestronglyMeasurable fun x ↦ by
      simp only [eNorm_eq_self]
      exact le_iSup (fun j ↦ f j x) i
  refine le_antisymm ?_ hle
  rcases eq_or_ne p 0 with rfl | hp₀
  · simp [eLpNorm_exponent_zero, hs.aestronglyMeasurable,
      fun i ↦ (hf i).aestronglyMeasurable]
  rcases eq_or_ne p ∞ with rfl | hp_top
  · simp only [eLpNorm_exponent_top, hs.aestronglyMeasurable,
      fun i ↦ (hf i).aestronglyMeasurable, eLpNormEssSup, eNorm_eq_self]
    refine essSup_le_of_ae_le _ ?_
    filter_upwards [ae_all_iff.2 fun i ↦ ENNReal.ae_le_essSup (μ := μ) (f i)] with x hx
    exact iSup_le fun i ↦ (hx i).trans (le_iSup (fun j ↦ essSup (f j) μ) i)
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp₀ hp_top
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp₀ hp_top hs.aestronglyMeasurable]
  have hnorm (i : ι) := eLpNorm_eq_lintegral_rpow_eNorm_toReal hp₀ hp_top
    (hf i).aestronglyMeasurable
  simp_rw [hnorm, eNorm_eq_self]
  simp_rw [ENNReal.iSup_rpow_of_pos hq (fun i ↦ f i _)]
  rw [lintegral_iSup_directed (fun i ↦ (hf i).pow_const _) ?_,
    ENNReal.iSup_rpow_of_pos (one_div_pos.mpr hq)]
  intro i j
  obtain ⟨k, hik, hjk⟩ := hd i j
  exact ⟨k, fun x ↦ ENNReal.rpow_le_rpow (hik x) hq.le,
    fun x ↦ ENNReal.rpow_le_rpow (hjk x) hq.le⟩

/-- Countable Minkowski inequality for almost everywhere measurable `ℝ≥0∞`-valued functions.
No summability or finiteness hypothesis is required. -/
theorem eLpNorm_tsum_le_ennreal [Countable ι] {f : ι → Ω → ℝ≥0∞}
    (hp : 1 ≤ p) (hf : ∀ i, AEMeasurable (f i) μ) :
    eLpNorm (fun x ↦ ∑' i, f i x) p μ ≤ ∑' i, eLpNorm (f i) p μ := by
  have hd : Directed (· ≤ ·) (fun s : Finset ι ↦ ∑ i ∈ s, f i) := by
    classical
    intro s t
    exact ⟨s ∪ t, sum_le_sum_of_subset subset_union_left,
      sum_le_sum_of_subset subset_union_right⟩
  have hsum : (fun x ↦ ∑' i, f i x) = fun x ↦ ⨆ s : Finset ι, (∑ i ∈ s, f i) x := by
    funext x
    simp only [Finset.sum_apply, tsum_eq_iSup_sum]
  rw [hsum, eLpNorm_iSup_ennreal (fun s ↦ s.aemeasurable_sum fun i _ ↦ hf i) hd]
  exact iSup_le fun s ↦ (eLpNorm_sum_le (μ := μ) (s := s) (f := f) hp).trans (sum_le_tsum s)

end MeasureTheory
