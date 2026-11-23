/-
Copyright (c) 2026 David A. Dalrymple. All rights reserved.
Released under MIT OR Apache-2.0 license as described in the file LICENSE.
Authors: dhai (davidad's Humanis AIs)
-/
module

import Wasserstein

/-! # Examples exercising the public import -/

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

local instance : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨le_top⟩

example : CompleteSpace (WassersteinLp 1 ℝ) := inferInstance
example : CompleteSpace (WassersteinLp 2 ℝ) := inferInstance
example : CompleteSpace (WassersteinLp ∞ ℝ) := inferInstance
example : CompleteSpace (Wasserstein 1 ℝ) := inferInstance
example : CompleteSpace (Wasserstein ∞ ℝ) := inferInstance

-- (0, 1) is Polish and standard Borel, but its induced metric is not complete.
example : MetricSpace (WassersteinLp 1 (Ioo (0 : ℝ) 1)) := by
  have : PolishSpace (Ioo (0 : ℝ) 1) := isOpen_Ioo.polishSpace
  infer_instance

example : edist (Wasserstein.dirac (p := 2) (0 : ℝ)) (Wasserstein.dirac (p := 2) 1) = 1 := by
  rw [Wasserstein.edist_dirac_dirac (by norm_num)]
  simp

example : LipschitzWith 1 (WassersteinLp.map (p := 2)
    (show LipschitzWith 1 (id : ℝ → ℝ) from LipschitzWith.id)) := WassersteinLp.lipschitzWith_map _

example {X : Type*} [EMetricSpace X] [CompleteSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] : CompleteSpace (Wasserstein ∞ X) := inferInstance

-- No second countability hypothesis on the Lipschitz map's source.
example {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [PseudoEMetricSpace X]
    [PseudoEMetricSpace Y] [OpensMeasurableSpace X] [BorelSpace Y] [SecondCountableTopology Y]
    {f : X → Y} {L : ℝ≥0} (hf : LipschitzWith L f) (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    wassersteinEDist 1 (μ.map f) (ν.map f) ≤ L * wassersteinEDist 1 μ ν :=
  wassersteinEDist_map_le zero_lt_one hf μ ν

-- The constructors preserve the input law.
example {X : Type*} [MeasurableSpace X] (μ : ProbabilityMeasure X) :
    (Wasserstein.ofProbabilityMeasure (p := 1) μ).toProbabilityMeasure = μ := by simp

example {X : Type*} [MeasurableSpace X] [MetricSpace X] (μ : Wasserstein 1 X) (a : X)
    (h : eLpNorm (fun x ↦ edist x a) 1 μ.toMeasure < ∞) :
    (WassersteinLp.ofFiniteMoment μ h).1 = μ := by simp

-- Finite-measure gluing does not require the middle space to be standard Borel.
example {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [StandardBorelSpace A] [StandardBorelSpace C] {π₁ : Measure (A × B)}
    {π₂ : Measure (B × C)} [IsFiniteMeasure π₁] [IsFiniteMeasure π₂]
    (h : π₁.snd = π₂.fst) :
    ∃ π : Measure (A × B × C), π.map (fun x ↦ (x.1, x.2.1)) = π₁ ∧
      π.map Prod.snd = π₂ := Measure.exists_gluing h

-- The chain exposes both the single-time and consecutive-pair laws.
example {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    [∀ n, StandardBorelSpace (X (n + 1))] [∀ n, Nonempty (X (n + 1))]
    (μ : (n : ℕ) → Measure (X n)) [IsProbabilityMeasure (μ 0)]
    (π : (n : ℕ) → Measure (X n × X (n + 1))) [∀ n, IsFiniteMeasure (π n)]
    (hπ : ∀ n, (π n).IsCoupling (μ n) (μ (n + 1))) (n : ℕ) :
    (ProbabilityTheory.Kernel.chainMeasure (μ 0) π).map (fun ω ↦ ω n) = μ n ∧
    (ProbabilityTheory.Kernel.chainMeasure (μ 0) π).map (fun ω ↦ (ω n, ω (n + 1))) = π n :=
  ⟨ProbabilityTheory.Kernel.map_eval_chainMeasure μ π hπ n,
   ProbabilityTheory.Kernel.map_pair_chainMeasure μ π hπ n⟩

example {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {μ : Measure Ω}
    {p : ℝ≥0∞} (hp : 1 ≤ p) {f : ι → Ω → ℝ≥0∞}
    (hf : ∀ i, AEMeasurable (f i) μ) :
    eLpNorm (fun x ↦ ∑' i, f i x) p μ ≤ ∑' i, eLpNorm (f i) p μ :=
  eLpNorm_tsum_le_ennreal hp hf
