/-
Copyright (c) 2026 David A. Dalrymple. All rights reserved.
Released under MIT OR Apache-2.0 license as described in the file LICENSE.
Authors: dhai (davidad's Humanis AIs)
-/
module

public import Wasserstein.Coupling
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# Gluing measures with a common marginal

Two finite measures on `α × β` and `β × γ` that agree on the `β` marginal extend to a measure on
`α × β × γ`. We disintegrate both measures over `β` and take the product of the conditional
kernels. Only the outer spaces need to be standard Borel.
-/

public section

open Set ProbabilityTheory

namespace MeasureTheory.Measure

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- Finite pair laws with the same middle marginal can be realized on one triple. Neither a
metric nor a standard Borel structure on the middle space is needed. -/
theorem exists_gluing [StandardBorelSpace α] [StandardBorelSpace γ]
    {π₁₂ : Measure (α × β)} {π₂₃ : Measure (β × γ)} [IsFiniteMeasure π₁₂] [IsFiniteMeasure π₂₃]
    (h : π₁₂.snd = π₂₃.fst) :
    ∃ π : Measure (α × β × γ), π.map (fun x ↦ (x.1, x.2.1)) = π₁₂ ∧ π.map Prod.snd = π₂₃ := by
  have hmass : π₁₂ univ = π₂₃ univ := by rw [← snd_univ (ρ := π₁₂), h, fst_univ]
  rcases eq_or_ne π₁₂ 0 with rfl | hne
  · have hzero : π₂₃ = 0 := measure_univ_eq_zero.mp (by simpa using hmass.symm)
    exact ⟨0, by simp, by simp [hzero]⟩
  have hpos₁ : π₁₂ univ ≠ 0 := mt measure_univ_eq_zero.mp hne
  have hpos₃ : π₂₃ univ ≠ 0 := hmass ▸ hpos₁
  obtain ⟨x, _⟩ := nonempty_of_measure_ne_zero hpos₁
  obtain ⟨z, _⟩ := nonempty_of_measure_ne_zero hpos₃
  have : Nonempty α := ⟨x.1⟩
  have : Nonempty γ := ⟨z.2⟩
  let ρ := π₁₂.map Prod.swap
  let κ₁ := ρ.condKernel
  let κ₃ := π₂₃.condKernel
  let μ := π₂₃.fst
  have h₁ : μ ⊗ₘ κ₁ = ρ := by
    change π₂₃.fst ⊗ₘ κ₁ = ρ
    rw [← h, ← fst_map_swap]
    exact ρ.disintegrate κ₁
  have h₃ : μ ⊗ₘ κ₃ = π₂₃ := π₂₃.disintegrate κ₃
  let η := μ ⊗ₘ (κ₁ ×ₖ κ₃)
  have hη₁ : η.map (Prod.map id Prod.fst) = ρ := by
    rw [← compProd_map measurable_fst, ← Kernel.fst_eq, Kernel.fst_prod, h₁]
  have hη₃ : η.map (Prod.map id Prod.snd) = π₂₃ := by
    rw [← compProd_map measurable_snd, ← Kernel.snd_eq, Kernel.snd_prod, h₃]
  let reorder : β × α × γ → α × β × γ := fun x ↦ (x.2.1, x.1, x.2.2)
  have hmeas : Measurable reorder := by fun_prop (disch := simp [reorder])
  refine ⟨η.map reorder, ?_, ?_⟩
  · rw [map_map (by fun_prop) hmeas]
    change η.map (Prod.swap ∘ Prod.map id Prod.fst) = π₁₂
    rw [← map_map (by fun_prop) (by fun_prop), hη₁]
    change (π₁₂.map Prod.swap).map Prod.swap = π₁₂
    rw [map_map (by fun_prop) (by fun_prop)]
    exact map_id
  · rw [map_map measurable_snd hmeas]
    exact hη₃

end MeasureTheory.Measure
