/-
Copyright (c) 2026 David A. Dalrymple. All rights reserved.
Released under MIT OR Apache-2.0 license as described in the file LICENSE.
Authors: dhai (davidad's Humanis AIs)
-/
module

public import Wasserstein.Triangle
public import Mathlib.MeasureTheory.Function.LpSeminorm.Count
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# The extended Wasserstein space

`Wasserstein p X` is a separate type for the probability measures on `X`. It carries the
Wasserstein extended metric, not the weak topology of `ProbabilityMeasure X`. The extended
metric instance requires `p ≥ 1`, an extended metric space with a second countable topology,
its Borel σ-algebra and a standard Borel structure, but not completeness of `X`.
-/

public section

open scoped ENNReal NNReal

namespace MeasureTheory

/-- Probability measures endowed with the extended Wasserstein distance of exponent `p`. -/
@[expose] def Wasserstein (_p : ℝ≥0∞) (X : Type*) [MeasurableSpace X] := ProbabilityMeasure X

namespace Wasserstein

variable {X : Type*} [MeasurableSpace X] {p : ℝ≥0∞}

/-- View a probability measure as an element of the Wasserstein space. -/
def ofProbabilityMeasure (μ : ProbabilityMeasure X) : Wasserstein p X := μ

/-- Forget the Wasserstein metric. -/
def toProbabilityMeasure (μ : Wasserstein p X) : ProbabilityMeasure X := μ

/-- The underlying measure. -/
abbrev toMeasure (μ : Wasserstein p X) : Measure X := μ.toProbabilityMeasure.toMeasure

@[simp] theorem toProbabilityMeasure_ofProbabilityMeasure (μ : ProbabilityMeasure X) :
    (ofProbabilityMeasure (p := p) μ).toProbabilityMeasure = μ := by rfl

@[simp] theorem ofProbabilityMeasure_toProbabilityMeasure (μ : Wasserstein p X) :
    ofProbabilityMeasure μ.toProbabilityMeasure = μ := by rfl

theorem toMeasure_injective : Function.Injective (toMeasure (p := p) (X := X)) :=
  ProbabilityMeasure.toMeasure_injective

@[ext] theorem ext {μ ν : Wasserstein p X} (h : μ.toMeasure = ν.toMeasure) : μ = ν :=
  toMeasure_injective h

/-- The point mass at `a`, viewed as an element of the Wasserstein space. -/
noncomputable def dirac (a : X) : Wasserstein p X :=
  ofProbabilityMeasure ⟨Measure.dirac a, inferInstance⟩

@[simp] theorem toMeasure_dirac (a : X) :
    (dirac (p := p) a).toMeasure = Measure.dirac a := by rfl

instance [Nonempty X] : Nonempty (Wasserstein p X) := ‹Nonempty X›.map dirac

/-- Push a law forward along a measurable map, keeping the same exponent. -/
noncomputable def map {Y : Type*} [MeasurableSpace Y] {f : X → Y} (_hf : Measurable f)
    (μ : Wasserstein p X) : Wasserstein p Y := ofProbabilityMeasure (μ.toProbabilityMeasure.map f)

@[simp] theorem toMeasure_map {Y : Type*} [MeasurableSpace Y] {f : X → Y}
    (hf : Measurable f) (μ : Wasserstein p X) :
    (map hf μ).toMeasure = μ.toMeasure.map f := by rfl

@[simp] theorem map_dirac {Y : Type*} [MeasurableSpace Y] {f : X → Y} (hf : Measurable f)
    (a : X) : map hf (dirac (p := p) a) = dirac (f a) := by
  apply toMeasure_injective
  simp only [toMeasure_map, toMeasure_dirac]
  exact Measure.map_dirac' hf a

section Distance

variable [PseudoEMetricSpace X]

noncomputable instance instEDist : EDist (Wasserstein p X) :=
  ⟨fun μ ν ↦ wassersteinEDist p μ.toMeasure ν.toMeasure⟩

theorem edist_def (μ ν : Wasserstein p X) :
    edist μ ν = wassersteinEDist p μ.toMeasure ν.toMeasure := by rfl

variable [OpensMeasurableSpace X] [MeasurableSingletonClass X]

@[simp] theorem edist_dirac (μ : Wasserstein p X) (a : X) :
    edist μ (dirac a) = eLpNorm (fun x ↦ edist x a) p μ.toMeasure := by
  rw [edist_def, toMeasure_dirac, wassersteinEDist_dirac]

@[simp] theorem edist_dirac_dirac (hp : p ≠ 0) (a b : X) :
    edist (dirac (p := p) a) (dirac b) = edist a b := by
  rw [edist_dirac, toMeasure_dirac, eLpNorm_dirac _ _ hp, eNorm_eq_self]

end Distance

section ExtendedMetric

variable [EMetricSpace X] [SecondCountableTopology X] [BorelSpace X] [StandardBorelSpace X]
  [Fact (1 ≤ p)]

noncomputable instance instEMetricSpace : EMetricSpace (Wasserstein p X) where
  edist_self μ := wassersteinEDist_self p μ.toMeasure
  edist_comm μ ν := wassersteinEDist_comm p μ.toMeasure ν.toMeasure
  edist_triangle μ ν ξ := wassersteinEDist_triangle Fact.out
  eq_of_edist_eq_zero h := ext ((wassersteinEDist_eq_zero_iff (zero_lt_one.trans_le
    (Fact.out : 1 ≤ p)).ne').1 h)

/-- For `p ≥ 1` on a second countable extended metric space with its Borel σ-algebra
and a standard Borel structure, the embedding by point masses preserves distances. -/
theorem isometry_dirac : Isometry (dirac (p := p) (X := X)) :=
  fun a b ↦ edist_dirac_dirac (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' a b

/-- A Lipschitz map induces a Lipschitz pushforward on laws when both base spaces are
second countable extended metric spaces with their Borel σ-algebras and standard Borel
structures, and `p ≥ 1`. -/
theorem lipschitzWith_map {Y : Type*} [EMetricSpace Y] [MeasurableSpace Y]
    [SecondCountableTopology Y] [BorelSpace Y] [StandardBorelSpace Y] {L : ℝ≥0} {f : X → Y}
    (hf : LipschitzWith L f) :
    LipschitzWith L (map (p := p) hf.continuous.measurable) := by
  intro μ ν
  simp only [edist_def, toMeasure_map]
  exact wassersteinEDist_map_le (zero_lt_one.trans_le (Fact.out : 1 ≤ p)) hf _ _

end ExtendedMetric

end Wasserstein

end MeasureTheory
