/-
Copyright (c) 2026 David A. Dalrymple. All rights reserved.
Released under MIT OR Apache-2.0 license as described in the file LICENSE.
Authors: dhai (davidad's Humanis AIs)
-/
module

public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Couplings of measures

A coupling of two measures is a measure on the product whose first and second marginals are
those measures. The two coordinate spaces need not be the same. Couplings are preserved by
swapping coordinates and by mapping each coordinate separately.
-/

public section

open Set

namespace MeasureTheory.Measure

variable {α β γ δ Ω : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ] [MeasurableSpace Ω]

/-- `π` is a coupling of `μ` and `ν` if its two marginals are `μ` and `ν`, respectively. -/
structure IsCoupling (π : Measure (α × β)) (μ : Measure α) (ν : Measure β) : Prop where
  fst_eq : π.fst = μ
  snd_eq : π.snd = ν

namespace IsCoupling

variable {π : Measure (α × β)} {μ : Measure α} {ν : Measure β}

theorem measure_univ_eq_left (h : IsCoupling π μ ν) : π univ = μ univ := by
  rw [← h.fst_eq, fst_univ]

theorem measure_univ_eq_right (h : IsCoupling π μ ν) : π univ = ν univ := by
  rw [← h.snd_eq, snd_univ]

theorem isFiniteMeasure [IsFiniteMeasure μ] (h : IsCoupling π μ ν) : IsFiniteMeasure π :=
  ⟨h.measure_univ_eq_left ▸ measure_lt_top μ univ⟩

theorem isProbabilityMeasure [IsProbabilityMeasure μ] (h : IsCoupling π μ ν) :
    IsProbabilityMeasure π :=
  ⟨h.measure_univ_eq_left.trans measure_univ⟩

/-- Swapping the coordinates exchanges the marginals. -/
theorem swap (h : IsCoupling π μ ν) : IsCoupling (π.map Prod.swap) ν μ :=
  ⟨(fst_map_swap (ρ := π)).trans h.snd_eq, (snd_map_swap (ρ := π)).trans h.fst_eq⟩

/-- Applying separate measurable maps to the coordinates couples the pushforwards. -/
theorem map (h : IsCoupling π μ ν) {f : α → γ} {g : β → δ} (hf : Measurable f) (hg : Measurable g) :
    IsCoupling (π.map (Prod.map f g)) (μ.map f) (ν.map g) := by
  constructor
  · rw [Measure.fst, map_map measurable_fst (hf.prodMap hg),
      show Prod.fst ∘ Prod.map f g = f ∘ Prod.fst from rfl,
      ← map_map hf measurable_fst, ← Measure.fst, h.fst_eq]
  · rw [Measure.snd, map_map measurable_snd (hf.prodMap hg),
      show Prod.snd ∘ Prod.map f g = g ∘ Prod.snd from rfl,
      ← map_map hg measurable_snd, ← Measure.snd, h.snd_eq]

end IsCoupling

/-- The product of two probability measures is a coupling. -/
theorem IsCoupling.prod (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : IsCoupling (μ.prod ν) μ ν :=
  ⟨fst_prod, snd_prod⟩

/-- The joint law of two random variables couples their individual laws. -/
theorem isCoupling_map_prodMk {P : Measure Ω} {f : Ω → α} {g : Ω → β}
    (hf : AEMeasurable f P) (hg : AEMeasurable g P) :
    IsCoupling (P.map fun x ↦ (f x, g x)) (P.map f) (P.map g) :=
  ⟨fst_map_prodMk₀ hf hg, snd_map_prodMk₀ hf hg⟩

/-- The diagonal map couples a measure with itself. -/
theorem IsCoupling.map_diag (μ : Measure α) : IsCoupling (μ.map fun x ↦ (x, x)) μ μ := by
  simpa only [map_id, id_eq] using
    isCoupling_map_prodMk (P := μ) measurable_id.aemeasurable measurable_id.aemeasurable

end MeasureTheory.Measure
