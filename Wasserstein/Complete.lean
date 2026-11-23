/-
Copyright (c) 2026 David A. Dalrymple. All rights reserved.
Released under MIT OR Apache-2.0 license as described in the file LICENSE.
Authors: dhai (davidad's Humanis AIs)
-/
module

public import Wasserstein.Chain
public import Wasserstein.Minkowski
public import Wasserstein.FiniteMoment
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Completeness of Wasserstein distance

A rapidly Cauchy sequence of laws admits successive couplings whose transport costs have
finite sum. Realize the couplings as consecutive pairs in one random sequence. Its
increments are almost surely summable, so the sequence has a measurable limit. Countable
Minkowski bounds the cost of coupling each term with the limit by the sum of the later costs.
-/

public section

namespace MeasureTheory

open Measure Filter Set ProbabilityTheory.Kernel
open scoped ENNReal Topology

section RandomSequence

variable {X Ω : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [CompleteSpace X] [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {p : ℝ≥0∞}

/-- A sequence of random variables with summable `Lᵖ` displacements converges almost surely.
The `Lᵖ` displacement to the limit is bounded by the corresponding tail of the sum. -/
theorem exists_measurable_limit_of_summable_steps (hp : 1 ≤ p) {u : ℕ → Ω → X}
    (hu : ∀ n, AEMeasurable (u n) P) {c : ℕ → ℝ≥0∞}
    (hc : ∀ n, eLpNorm (fun ω ↦ edist (u n ω) (u (n + 1) ω)) p P ≤ c n)
    (hsum : (∑' n, c n) ≠ ∞) :
    ∃ v : Ω → X, Measurable v ∧ (∀ᵐ ω ∂P, Tendsto (fun n ↦ u n ω) atTop (𝓝 (v ω))) ∧
      ∀ n, eLpNorm (fun ω ↦ edist (u n ω) (v ω)) p P ≤ ∑' k, c (n + k) := by
  let step (n : ℕ) (ω : Ω) := edist (u n ω) (u (n + 1) ω)
  let tail (n : ℕ) (ω : Ω) := ∑' k, step (n + k) ω
  have hstep (n : ℕ) : AEMeasurable (step n) P := (hu n).edist (hu (n + 1))
  have htail (n : ℕ) : AEMeasurable (tail n) P := AEMeasurable.tsum fun k ↦ hstep (n + k)
  have hbound (n : ℕ) : eLpNorm (tail n) p P ≤ ∑' k, c (n + k) :=
    (eLpNorm_tsum_le_ennreal hp (fun k ↦ hstep (n + k))).trans
      (tsum_le_tsum fun k ↦ hc (n + k))
  have h1 := eLpNorm_le_eLpNorm_of_exponent_le (f := tail 0) (μ := P) hp
  rw [eLpNorm_one_eq_lintegral_eNorm (htail 0).aestronglyMeasurable] at h1
  simp only [eNorm_eq_self] at h1
  have hfinite : (∫⁻ ω, tail 0 ω ∂P) ≠ ∞ :=
    ne_top_of_le_ne_top (by simpa only [zero_add] using hsum) (h1.trans (hbound 0))
  have hconv : ∀ᵐ ω ∂P, ∃ a, Tendsto (fun n ↦ u n ω) atTop (𝓝 a) := by
    filter_upwards [ae_lt_top' (htail 0) hfinite] with ω hω
    have hs : (∑' k, step k ω) ≠ ∞ := by simpa only [tail, zero_add] using hω.ne
    exact cauchySeq_tendsto_of_complete <|
      cauchySeq_of_edist_le_of_tsum_ne_top (fun n ↦ step n ω) (fun _ ↦ le_rfl) hs
  obtain ⟨v, hv, hvlim⟩ := measurable_limit_of_tendsto_metrizable_ae hu hconv
  refine ⟨v, hv, hvlim, fun n ↦ le_trans ?_ (hbound n)⟩
  refine eLpNorm_mono_eNorm_ae ((hu n).edist hv.aemeasurable).aestronglyMeasurable ?_
  filter_upwards [hvlim] with ω hω
  simpa only [eNorm_eq_self] using
    edist_le_tsum_of_edist_le_of_tendsto (fun k ↦ edist (u k ω) (u (k + 1) ω))
      (fun _ ↦ le_rfl) hω n

end RandomSequence

section CoupledSequence

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [CompleteSpace X] {p : ℝ≥0∞}

/-- Successive couplings with summable costs give a limit law at Wasserstein distance at most
the sum of the remaining costs. No moment hypothesis on any law is required. -/
theorem exists_limit_of_summable_couplings (hp : 1 ≤ p) (u : ℕ → ProbabilityMeasure X)
    (π : ℕ → Measure (X × X))
    (hπ : ∀ n, IsCoupling (π n) (u n).toMeasure (u (n + 1)).toMeasure)
    {c : ℕ → ℝ≥0∞} (hc : ∀ n, transportCost p (π n) ≤ c n) (hsum : (∑' n, c n) ≠ ∞) :
    ∃ ν : ProbabilityMeasure X, ∀ n, wassersteinEDist p (u n).toMeasure ν.toMeasure ≤
      ∑' k, c (n + k) := by
  have : Nonempty X := (u 0).nonempty
  have : ∀ _ : ℕ, StandardBorelSpace X := fun _ ↦ inferInstance
  have : ∀ n, IsFiniteMeasure (π n) := fun n ↦ (hπ n).isFiniteMeasure
  let P := chainMeasure (X := fun _ ↦ X) (u 0).toMeasure π
  have hLaws := chainMeasure_marginals (X := fun _ ↦ X)
    (fun n ↦ (u n).toMeasure) π hπ
  have heval (n : ℕ) : P.map (fun ω ↦ ω n) = (u n).toMeasure := hLaws.1 n
  have hpair (n : ℕ) : P.map (fun ω ↦ (ω n, ω (n + 1))) = π n := hLaws.2 n
  have hm (n : ℕ) : AEMeasurable (fun ω : ℕ → X ↦ ω n) P :=
    (measurable_pi_apply n).aemeasurable
  have hnorm (n : ℕ) : eLpNorm (fun ω : ℕ → X ↦ edist (ω n) (ω (n + 1))) p P ≤ c n := by
    rw [← transportCost_map (hm n) (hm (n + 1)), hpair n]
    exact hc n
  obtain ⟨v, hv, -, hcost⟩ := exists_measurable_limit_of_summable_steps hp hm hnorm hsum
  let ν : ProbabilityMeasure X := ⟨P.map v, inferInstance⟩
  refine ⟨ν, fun n ↦ ?_⟩
  have hcoup : IsCoupling (P.map fun ω ↦ (ω n, v ω)) (u n).toMeasure ν.toMeasure := by
    have hpairs := isCoupling_map_prodMk (hm n) hv.aemeasurable
    exact ⟨hpairs.fst_eq.trans (heval n), hpairs.snd_eq⟩
  refine (wassersteinEDist_le_of_isCoupling hcoup).trans ?_
  rw [transportCost_map (hm n) hv.aemeasurable]
  exact hcost n

end CoupledSequence

namespace Wasserstein

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [CompleteSpace X] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The extended Wasserstein space over a complete separable extended metric space with its
Borel σ-algebra is complete. -/
instance instCompleteSpace : CompleteSpace (Wasserstein p X) := by
  let b (n : ℕ) : ℝ≥0∞ := (2⁻¹ : ℝ≥0∞) ^ n
  have hb : (∑' n, b n) ≠ ∞ := by
    dsimp [b]
    rw [ENNReal.tsum_geometric]
    norm_num [ENNReal.one_sub_inv_two]
  refine EMetric.complete_of_convergent_controlled_sequences b
    (fun n ↦ ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) n) fun u hu ↦ ?_
  have hex (n : ℕ) := exists_isCoupling_lt_of_wassersteinEDist_lt
    (show wassersteinEDist p (u n).toMeasure (u (n + 1)).toMeasure < b n from
      hu n n (n + 1) le_rfl (Nat.le_succ n))
  choose π hπ hc using hex
  obtain ⟨ν, hν⟩ := exists_limit_of_summable_couplings Fact.out
    (fun n ↦ (u n).toProbabilityMeasure) π hπ (fun n ↦ (hc n).le) hb
  refine ⟨ofProbabilityMeasure ν, ?_⟩
  rw [EMetric.tendsto_atTop]
  intro ε hε
  have htail : Tendsto (fun n ↦ ∑' k, b (n + k)) atTop (𝓝 0) := by
    simpa only [Nat.add_comm] using ENNReal.tendsto_sum_nat_add b hb
  obtain ⟨N, hN⟩ := eventually_atTop.mp (htail.eventually_lt_const hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [edist_def]
  simpa only [toMeasure, toProbabilityMeasure_ofProbabilityMeasure] using (hν n).trans_lt (hN n hn)

end Wasserstein

namespace WassersteinLp

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [CompleteSpace X] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On a complete separable metric space with its Borel σ-algebra and `p ≥ 1`, the
finite-moment space is a closed subspace of the complete extended Wasserstein space. -/
instance instCompleteSpace : CompleteSpace (WassersteinLp p X) := by
  have : IsClosed {μ : Wasserstein p X | μ.HasFiniteMoment} :=
    (Wasserstein.isClopen_hasFiniteMoment (p := p)).1
  exact IsClosed.completeSpace_coe (s := {μ : Wasserstein p X | μ.HasFiniteMoment})

end WassersteinLp

end MeasureTheory
