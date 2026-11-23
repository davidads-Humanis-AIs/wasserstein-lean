/-
Copyright (c) 2026 David A. Dalrymple. All rights reserved.
Released under MIT OR Apache-2.0 license as described in the file LICENSE.
Authors: dhai (davidad's Humanis AIs)
-/
module

public import Wasserstein.Distance
public import Wasserstein.Glue

/-!
# The Wasserstein triangle inequality

On a second countable pseudo-extended metric space with its Borel σ-algebra and a standard
Borel structure, finite measures satisfy the triangle inequality for `p ≥ 1`. The proof
glues consecutive plans and applies Minkowski's inequality to the two displacements. The
Lean statement needs only opens measurable and finiteness of the first two measures.
-/

public section

namespace MeasureTheory

open Measure
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] [PseudoEMetricSpace X] [SecondCountableTopology X]
  [OpensMeasurableSpace X] [StandardBorelSpace X]
variable {p : ℝ≥0∞} {μ₁ μ₂ μ₃ : Measure X} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]

/-- Composing two transport plans bounds the direct transport distance by the sum of their costs. -/
theorem wassersteinEDist_le_add_of_isCoupling (hp : 1 ≤ p) {π₁₂ π₂₃ : Measure (X × X)}
    (h₁₂ : IsCoupling π₁₂ μ₁ μ₂) (h₂₃ : IsCoupling π₂₃ μ₂ μ₃) :
    wassersteinEDist p μ₁ μ₃ ≤ transportCost p π₁₂ + transportCost p π₂₃ := by
  have : IsFiniteMeasure π₁₂ := h₁₂.isFiniteMeasure
  have : IsFiniteMeasure π₂₃ := h₂₃.isFiniteMeasure
  obtain ⟨γ, hγ₁₂, hγ₂₃⟩ := exists_gluing (h₁₂.snd_eq.trans h₂₃.fst_eq.symm)
  let f : X × X × X → X := Prod.fst
  let g : X × X × X → X := Prod.fst ∘ Prod.snd
  let h : X × X × X → X := Prod.snd ∘ Prod.snd
  have hf : Measurable f := measurable_fst
  have hg : Measurable g := measurable_fst.comp measurable_snd
  have hh : Measurable h := measurable_snd.comp measurable_snd
  have h₁ : γ.map f = μ₁ := (Measure.fst_map_prodMk hf hg).symm.trans (hγ₁₂ ▸ h₁₂.fst_eq)
  have h₃ : γ.map h = μ₃ := (Measure.snd_map_prodMk hg hh).symm.trans (hγ₂₃ ▸ h₂₃.snd_eq)
  have h₁₃ : IsCoupling (γ.map fun x ↦ (f x, h x)) μ₁ μ₃ :=
    ⟨(Measure.fst_map_prodMk hf hh).trans h₁, (Measure.snd_map_prodMk hf hh).trans h₃⟩
  calc
    wassersteinEDist p μ₁ μ₃ ≤ transportCost p (γ.map fun x ↦ (f x, h x)) :=
      wassersteinEDist_le_of_isCoupling h₁₃
    _ = eLpNorm (fun x ↦ edist (f x) (h x)) p γ := transportCost_map hf.aemeasurable hh.aemeasurable
    _ ≤ eLpNorm (fun x ↦ edist (f x) (g x) + edist (g x) (h x)) p γ :=
      eLpNorm_mono_eNorm (hf.edist hh).aestronglyMeasurable fun x ↦ edist_triangle _ _ _
    _ ≤ eLpNorm (fun x ↦ edist (f x) (g x)) p γ + eLpNorm (fun x ↦ edist (g x) (h x)) p γ :=
      eLpNorm_add_le hp
    _ = transportCost p π₁₂ + transportCost p π₂₃ := by
      rw [← transportCost_map hf.aemeasurable hg.aemeasurable,
        ← transportCost_map hg.aemeasurable hh.aemeasurable]
      change transportCost p (γ.map fun x ↦ (x.1, x.2.1)) + transportCost p (γ.map Prod.snd) = _
      rw [hγ₁₂, hγ₂₃]

/-- The extended Wasserstein distance satisfies the triangle inequality at any exponent
`p ≥ 1`. -/
theorem wassersteinEDist_triangle (hp : 1 ≤ p) :
    wassersteinEDist p μ₁ μ₃ ≤ wassersteinEDist p μ₁ μ₂ + wassersteinEDist p μ₂ μ₃ := by
  unfold wassersteinEDist
  rw [ENNReal.iInf_add]
  simp_rw [ENNReal.add_iInf]
  exact le_iInf fun π₁₂ ↦ le_iInf fun π₂₃ ↦ wassersteinEDist_le_add_of_isCoupling hp π₁₂.2 π₂₃.2

end MeasureTheory
