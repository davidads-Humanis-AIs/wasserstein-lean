/-
Copyright (c) 2026 David A. Dalrymple. All rights reserved.
Released under MIT OR Apache-2.0 license as described in the file LICENSE.
Authors: dhai (davidad's Humanis AIs)
-/
module

public import Wasserstein.Space

/-!
# Probability measures of finite moment

For `p ≥ 1` on a metric space with a Borel σ-algebra, a law has a finite moment about
some point if and only if it has a finite moment about every point. If the space is also
second countable and standard Borel, the laws in `WassersteinLp p X` form a finite-distance
component of any point mass in `Wasserstein p X`. The subtype is clopen, and its extended
distance is everywhere finite. The empty space is handled separately.
-/

public section

open Set
open scoped ENNReal NNReal

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X] {p : ℝ≥0∞}

/-- A law has finite `p`-moment if the displacement from some point has finite `Lᵖ` seminorm.
For `p = ∞`, this requires the distance from a fixed point to be almost everywhere
measurable and essentially bounded under the law; measurability holds when opens are measurable. -/
def Wasserstein.HasFiniteMoment [PseudoEMetricSpace X] (μ : Wasserstein p X) : Prop :=
  ∃ a : X, eLpNorm (fun x ↦ edist x a) p μ.toMeasure < ∞

/-- Probability measures of finite `p`-moment on a metric space. -/
abbrev WassersteinLp (p : ℝ≥0∞) (X : Type*) [MeasurableSpace X] [MetricSpace X] :=
  {μ : Wasserstein p X // μ.HasFiniteMoment}

namespace Wasserstein

variable [MetricSpace X]

/-- Unfold the finite-moment condition. -/
theorem hasFiniteMoment_iff (μ : Wasserstein p X) :
    μ.HasFiniteMoment ↔ ∃ a : X, eLpNorm (fun x ↦ edist x a) p μ.toMeasure < ∞ := Iff.rfl

section ReferencePoint

variable [OpensMeasurableSpace X] [Fact (1 ≤ p)]

/-- Any point can serve as the reference point in the finite-moment condition. -/
theorem hasFiniteMoment_iff_edist_dirac_lt_top (μ : Wasserstein p X) (a : X) :
    μ.HasFiniteMoment ↔ edist μ (Wasserstein.dirac (p := p) a) < ∞ := by
  rw [Wasserstein.edist_dirac]
  refine ⟨?_, fun h ↦ ⟨a, h⟩⟩
  rintro ⟨b, hb⟩
  exact eLpNorm_edist_lt_top_of_edist_lt_top Fact.out (edist_lt_top b a) hb

/-- The finite-moment laws are exactly the open ball of infinite radius about a point mass. -/
theorem setOf_hasFiniteMoment_eq_eball_dirac (a : X) :
    {μ : Wasserstein p X | μ.HasFiniteMoment} = Metric.eball (Wasserstein.dirac (p := p) a) ∞ :=
  Set.ext fun μ ↦ hasFiniteMoment_iff_edist_dirac_lt_top μ a

end ReferencePoint

variable [SecondCountableTopology X] [BorelSpace X] [StandardBorelSpace X] [Fact (1 ≤ p)]

/-- For `p ≥ 1`, the finite-moment laws form a clopen subset of the extended space over a
second countable metric space with its Borel σ-algebra and standard Borel structure. -/
theorem isClopen_hasFiniteMoment : IsClopen {μ : Wasserstein p X | μ.HasFiniteMoment} := by
  rcases isEmpty_or_nonempty X with hX | hX
  · have hEmpty : {μ : Wasserstein p X | μ.HasFiniteMoment} = ∅ := by
      ext μ
      simp [Wasserstein.HasFiniteMoment]
    rw [hEmpty]
    exact isClopen_empty
  · obtain ⟨a⟩ := hX
    rw [setOf_hasFiniteMoment_eq_eball_dirac (p := p) a]
    exact Metric.isClopen_eball_top

end Wasserstein

namespace WassersteinLp

variable [MetricSpace X]

/-- Construct a law of finite moment using any one reference point. -/
def ofFiniteMoment (μ : Wasserstein p X) {a : X}
    (h : eLpNorm (fun x ↦ edist x a) p μ.toMeasure < ∞) : WassersteinLp p X := ⟨μ, ⟨a, h⟩⟩

@[simp] theorem ofFiniteMoment_val (μ : Wasserstein p X) {a : X}
    (h : eLpNorm (fun x ↦ edist x a) p μ.toMeasure < ∞) :
    (ofFiniteMoment μ h).1 = μ := by rfl

/-- The underlying probability measure. -/
abbrev toProbabilityMeasure (μ : WassersteinLp p X) : ProbabilityMeasure X :=
  μ.1.toProbabilityMeasure

/-- The underlying measure. -/
abbrev toMeasure (μ : WassersteinLp p X) : Measure X := μ.1.toMeasure

@[ext] theorem ext {μ ν : WassersteinLp p X} (h : μ.toMeasure = ν.toMeasure) : μ = ν :=
  Subtype.ext (Wasserstein.ext h)

/-- The point mass at `a` has finite moment, with reference point `a`. -/
noncomputable def dirac [OpensMeasurableSpace X] (a : X) : WassersteinLp p X :=
  ofFiniteMoment (Wasserstein.dirac (p := p) a) (a := a) (by
    rw [Wasserstein.toMeasure_dirac]
    rcases eq_or_ne p 0 with rfl | hp
    · simp [eLpNorm_exponent_zero measurable_edist_left.aestronglyMeasurable]
    · simp [eLpNorm_dirac _ _ hp])

@[simp] theorem toMeasure_dirac [OpensMeasurableSpace X] (a : X) :
    (dirac (p := p) a).toMeasure = Measure.dirac a := by
  exact Wasserstein.toMeasure_dirac (p := p) a

instance [Nonempty X] [OpensMeasurableSpace X] : Nonempty (WassersteinLp p X) :=
  ‹Nonempty X›.map dirac

theorem edist_def (μ ν : WassersteinLp p X) :
    edist μ ν = wassersteinEDist p μ.toMeasure ν.toMeasure := by rfl

section ReferencePoint

variable [OpensMeasurableSpace X] [Fact (1 ≤ p)]

/-- Finiteness of the displacement seminorm about any reference point. -/
theorem eLpNorm_edist_lt_top (μ : WassersteinLp p X) (a : X) :
    eLpNorm (fun x ↦ edist x a) p μ.toMeasure < ∞ := by
  rw [← Wasserstein.edist_dirac]
  exact (Wasserstein.hasFiniteMoment_iff_edist_dirac_lt_top μ.1 a).1 μ.2

end ReferencePoint

section Finiteness

variable [OpensMeasurableSpace X] [SecondCountableTopology X] [Fact (1 ≤ p)]

theorem edist_lt_top (μ ν : WassersteinLp p X) : edist μ ν < ∞ := by
  obtain ⟨a, hμ⟩ := μ.2
  exact wassersteinEDist_lt_top Fact.out hμ (eLpNorm_edist_lt_top ν a)

end Finiteness

variable [SecondCountableTopology X] [BorelSpace X] [StandardBorelSpace X] [Fact (1 ≤ p)]

noncomputable instance instMetricSpace : MetricSpace (WassersteinLp p X) :=
  EMetricSpace.toMetricSpace fun μ ν ↦ (edist_lt_top μ ν).ne

theorem dist_def (μ ν : WassersteinLp p X) :
    dist μ ν = (wassersteinEDist p μ.toMeasure ν.toMeasure).toReal := by rfl

section Pushforward

variable {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [SecondCountableTopology Y]
  [BorelSpace Y] [StandardBorelSpace Y] {L : ℝ≥0} {f : X → Y}

/-- The Lipschitz pushforward of a finite-moment law again has finite moment. -/
noncomputable def map (hf : LipschitzWith L f) (μ : WassersteinLp p X) : WassersteinLp p Y :=
  ⟨Wasserstein.map hf.continuous.measurable μ.1, by
    obtain ⟨a, ha⟩ := μ.2
    apply (Wasserstein.hasFiniteMoment_iff_edist_dirac_lt_top _ (f a)).2
    have hμ := (Wasserstein.hasFiniteMoment_iff_edist_dirac_lt_top μ.1 a).1 ⟨a, ha⟩
    have h := (Wasserstein.lipschitzWith_map (p := p) hf).edist_le_mul μ.1 (Wasserstein.dirac a)
    rw [Wasserstein.map_dirac hf.continuous.measurable] at h
    exact h.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hμ)⟩

@[simp] theorem toMeasure_map (hf : LipschitzWith L f) (μ : WassersteinLp p X) :
    (map hf μ).toMeasure = μ.toMeasure.map f :=
  Wasserstein.toMeasure_map hf.continuous.measurable μ.1

/-- For `p ≥ 1`, a Lipschitz map between second countable metric spaces with their Borel
σ-algebras and standard Borel structures induces a pushforward with the same Lipschitz bound. -/
theorem lipschitzWith_map (hf : LipschitzWith L f) : LipschitzWith L (map (p := p) hf) :=
  fun μ ν ↦ (Wasserstein.lipschitzWith_map (p := p) hf).edist_le_mul μ.1 ν.1

end Pushforward

end WassersteinLp

end MeasureTheory
