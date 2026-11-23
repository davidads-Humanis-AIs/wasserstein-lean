/-
Copyright (c) 2026 David A. Dalrymple. All rights reserved.
Released under MIT OR Apache-2.0 license as described in the file LICENSE.
Authors: dhai (davidad's Humanis AIs)
-/
module

public import Wasserstein.Coupling
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Extended Wasserstein distance

The transport cost of a coupling is the extended `Lᵖ` seminorm of the distance between its
coordinates. The extended Wasserstein distance is the infimum of these costs. This file proves
its basic properties, the formula for transport to a point mass, and its behavior under a
Lipschitz pushforward.
-/

public section

namespace MeasureTheory

open Measure Set Filter Metric
open scoped ENNReal NNReal Topology

variable {X : Type*} [MeasurableSpace X] [PseudoEMetricSpace X]

/-- The `Lᵖ` size of the displacement under a transport plan. For finite positive `p`,
when the displacement is almost everywhere measurable for the plan, this is the `p`-th
root of the integral of its `p`-th power. For example, measurability holds on a second
countable space with its Borel σ-algebra. Otherwise `eLpNorm` returns `∞`. -/
@[expose] noncomputable def transportCost (p : ℝ≥0∞) (π : Measure (X × X)) : ℝ≥0∞ :=
  eLpNorm (fun xy ↦ edist xy.1 xy.2) p π

/-- The infimum of the transport costs of couplings of `μ` and `ν`. For finite positive `p`,
the integral formula for each cost applies when displacement is almost everywhere measurable
for that plan (e.g. on a second countable Borel space); otherwise `eLpNorm` returns `∞`.
The infimum of an empty family of couplings is `∞`. -/
@[expose] noncomputable def wassersteinEDist (p : ℝ≥0∞) (μ ν : Measure X) : ℝ≥0∞ :=
  ⨅ π : {π : Measure (X × X) // IsCoupling π μ ν}, transportCost p π.1

variable {p : ℝ≥0∞} {μ ν : Measure X} {π : Measure (X × X)}

theorem wassersteinEDist_le_of_isCoupling (hπ : IsCoupling π μ ν) :
    wassersteinEDist p μ ν ≤ transportCost p π :=
  iInf_le _ (⟨π, hπ⟩ : {π : Measure (X × X) // IsCoupling π μ ν})

/-- A strict upper bound on the Wasserstein distance gives a plan with cost below that bound. -/
theorem exists_isCoupling_lt_of_wassersteinEDist_lt {c : ℝ≥0∞} (h : wassersteinEDist p μ ν < c) :
    ∃ π : Measure (X × X), IsCoupling π μ ν ∧ transportCost p π < c := by
  obtain ⟨π, hπ⟩ := iInf_lt_iff.mp h
  exact ⟨π.1, π.2, hπ⟩

@[simp] theorem transportCost_map_swap (p : ℝ≥0∞) (π : Measure (X × X)) :
    transportCost p (π.map Prod.swap) = transportCost p π := by
  let e : X × X ≃ᵐ X × X := MeasurableEquiv.prodComm
  change eLpNorm _ p (π.map e) = eLpNorm _ p π
  rw [e.measurableEmbedding.eLpNorm_map_measure]
  exact congrArg (fun f ↦ eLpNorm f p π) (funext fun xy ↦ edist_comm xy.2 xy.1)

theorem wassersteinEDist_comm (p : ℝ≥0∞) (μ ν : Measure X) :
    wassersteinEDist p μ ν = wassersteinEDist p ν μ := by
  have h (a b : Measure X) : wassersteinEDist p a b ≤ wassersteinEDist p b a :=
    le_iInf fun π ↦
      (wassersteinEDist_le_of_isCoupling π.2.swap).trans_eq (transportCost_map_swap _ _)
  exact le_antisymm (h μ ν) (h ν μ)

theorem wassersteinEDist_mono [IsProbabilityMeasure μ] {q : ℝ≥0∞} (hpq : p ≤ q) :
    wassersteinEDist p μ ν ≤ wassersteinEDist q μ ν := by
  refine le_iInf fun π ↦ (wassersteinEDist_le_of_isCoupling π.2).trans ?_
  have : IsProbabilityMeasure π.1 := π.2.isProbabilityMeasure
  exact eLpNorm_le_eLpNorm_of_exponent_le hpq

/-- Self-distance vanishes as long as the zero-displacement set is measurable for the product
σ-algebra. This form does not require second countability. -/
theorem wassersteinEDist_self_of_measurableSet
    (h₀ : MeasurableSet {xy : X × X | edist xy.1 xy.2 = 0})
    (p : ℝ≥0∞) (μ : Measure X) : wassersteinEDist p μ μ = 0 := by
  let diag : X → X × X := fun x ↦ (x, x)
  have hd : Measurable diag := measurable_id.prodMk measurable_id
  have hae : (fun xy : X × X ↦ edist xy.1 xy.2) =ᵐ[μ.map diag] (fun _ ↦ 0) := by
    change ∀ᵐ xy ∂μ.map diag, edist xy.1 xy.2 = 0
    rw [ae_map_iff hd.aemeasurable h₀]
    simp [diag]
  apply le_antisymm ((wassersteinEDist_le_of_isCoupling (IsCoupling.map_diag μ)).trans ?_) zero_le
  change eLpNorm (fun xy : X × X ↦ edist xy.1 xy.2) p (μ.map diag) ≤ 0
  simp [eLpNorm_congr_ae hae]

section MeasurableCost

variable [OpensMeasurableSpace X] [SecondCountableTopology X]

/-- The cost of a pair law is the `Lᵖ` size of the distance between the two random variables. -/
theorem transportCost_map {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f g : Ω → X} (hf : AEMeasurable f P) (hg : AEMeasurable g P) :
    transportCost p (P.map fun ω ↦ (f ω, g ω)) = eLpNorm (fun ω ↦ edist (f ω) (g ω)) p P :=
  eLpNorm_map_measure measurable_edist.aestronglyMeasurable (hf.prodMk hg)

@[simp] theorem wassersteinEDist_self (p : ℝ≥0∞) (μ : Measure X) :
    wassersteinEDist p μ μ = 0 :=
  wassersteinEDist_self_of_measurableSet (measurable_edist (measurableSet_singleton 0)) p μ

/-- The cost of a plan can be bounded by the two displacement seminorms about any common point. -/
theorem transportCost_le_of_moments (hp : 1 ≤ p) (hπ : IsCoupling π μ ν) (a : X) :
    transportCost p π ≤ eLpNorm (fun x ↦ edist x a) p μ + eLpNorm (fun x ↦ edist x a) p ν := by
  have hm : Measurable fun x : X ↦ edist x a := measurable_edist_left
  have hf : eLpNorm (fun xy : X × X ↦ edist xy.1 a) p π = eLpNorm (fun x ↦ edist x a) p μ := by
    rw [← hπ.fst_eq]
    exact (eLpNorm_map_measure hm.aestronglyMeasurable measurable_fst.aemeasurable).symm
  have hg : eLpNorm (fun xy : X × X ↦ edist xy.2 a) p π = eLpNorm (fun x ↦ edist x a) p ν := by
    rw [← hπ.snd_eq]
    exact (eLpNorm_map_measure hm.aestronglyMeasurable measurable_snd.aemeasurable).symm
  calc
    transportCost p π ≤ eLpNorm (fun xy : X × X ↦ edist xy.1 a + edist xy.2 a) p π :=
      eLpNorm_mono_eNorm measurable_edist.aestronglyMeasurable fun xy ↦ by
        simpa only [eNorm_eq_self, edist_comm xy.2 a] using edist_triangle xy.1 a xy.2
    _ ≤ eLpNorm (fun xy : X × X ↦ edist xy.1 a) p π + eLpNorm (fun xy : X × X ↦ edist xy.2 a) p π :=
      eLpNorm_add_le hp
    _ = _ := by rw [hf, hg]

/-- Probability measures with finite displacement seminorms about a common point are a finite
Wasserstein distance apart. -/
theorem wassersteinEDist_lt_top (hp : 1 ≤ p) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a : X} (hμ : eLpNorm (fun x ↦ edist x a) p μ < ∞)
    (hν : eLpNorm (fun x ↦ edist x a) p ν < ∞) : wassersteinEDist p μ ν < ∞ :=
  (wassersteinEDist_le_of_isCoupling (IsCoupling.prod μ ν)).trans_lt <|
    (transportCost_le_of_moments hp (IsCoupling.prod μ ν) a).trans_lt
      (ENNReal.add_lt_top.2 ⟨hμ, hν⟩)

end MeasurableCost

/-- Finiteness of the displacement seminorm is unchanged when the reference point moves a
finite distance. No separability assumption is needed for the base space. -/
theorem eLpNorm_edist_lt_top_of_edist_lt_top [OpensMeasurableSpace X] [IsFiniteMeasure μ]
    (hp : 1 ≤ p) {a b : X} (hab : edist a b < ∞)
    (ha : eLpNorm (fun x ↦ edist x a) p μ < ∞) : eLpNorm (fun x ↦ edist x b) p μ < ∞ := by
  have hconst : eLpNorm (fun _ : X ↦ edist a b) p μ < ∞ := by
    rcases eq_or_ne μ 0 with rfl | hμ
    · simp
    rw [eLpNorm_const (edist a b) (zero_lt_one.trans_le hp).ne' hμ, eNorm_eq_self]
    exact ENNReal.mul_lt_top hab
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) (measure_ne_top μ _))
  have hmeas : Measurable (fun x : X ↦ edist x b) := measurable_edist_left
  calc
    eLpNorm (fun x ↦ edist x b) p μ ≤ eLpNorm (fun x ↦ edist x a + edist a b) p μ :=
      eLpNorm_mono_eNorm hmeas.aestronglyMeasurable fun x ↦ edist_triangle x a b
    _ ≤ eLpNorm (fun x ↦ edist x a) p μ + eLpNorm (fun _ : X ↦ edist a b) p μ :=
      eLpNorm_add_le hp
    _ < ∞ := ENNReal.add_lt_top.2 ⟨ha, hconst⟩

section Dirac

variable [OpensMeasurableSpace X] [MeasurableSingletonClass X]

private theorem transportCost_eq_eLpNorm_of_dirac {a : X}
    (hπ : IsCoupling π μ (Measure.dirac a)) :
    transportCost p π = eLpNorm (fun x ↦ edist x a) p μ := by
  have hae : ∀ᵐ xy ∂π, xy.2 = a := by
    apply ae_of_ae_map (p := fun y ↦ y = a) measurable_snd.aemeasurable
    rw [← Measure.snd, hπ.snd_eq]
    simp
  calc
    transportCost p π = eLpNorm (fun xy : X × X ↦ edist xy.1 a) p π :=
      eLpNorm_congr_ae (hae.mono fun xy hx ↦ by simp [hx])
    _ = _ := by
      rw [← hπ.fst_eq]
      exact (eLpNorm_map_measure measurable_edist_left.aestronglyMeasurable
        measurable_fst.aemeasurable).symm

/-- Transport to a point mass costs exactly the displacement seminorm about that point. -/
@[simp] theorem wassersteinEDist_dirac [IsProbabilityMeasure μ]
    (a : X) : wassersteinEDist p μ (Measure.dirac a) = eLpNorm (fun x ↦ edist x a) p μ := by
  apply le_antisymm
  · exact (wassersteinEDist_le_of_isCoupling (IsCoupling.prod μ (Measure.dirac a))).trans_eq
      (transportCost_eq_eLpNorm_of_dirac (IsCoupling.prod μ (Measure.dirac a)))
  · exact le_iInf fun π ↦ (transportCost_eq_eLpNorm_of_dirac π.2).ge

end Dirac

section Separation

variable [BorelSpace X] [SecondCountableTopology X]

private theorem measure_closed_le_thickening (hp₀ : p ≠ 0) (hp_top : p ≠ ∞)
    (h : wassersteinEDist p μ ν = 0) {F : Set X} (hF : IsClosed F) {δ : ℝ} (hδ : 0 < δ) :
    μ F ≤ ν (thickening δ F) := by
  let q := p.toReal
  have hq : 0 < q := ENNReal.toReal_pos hp₀ hp_top
  have hδq : 0 < ENNReal.ofReal δ ^ q := by positivity
  have hδq_top : ENNReal.ofReal δ ^ q ≠ ∞ := by finiteness
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  have hc_pos : 0 < ((ENNReal.ofReal δ ^ q) * (ε : ℝ≥0∞)) ^ (1 / q) := by positivity
  obtain ⟨π, hπ, hlt⟩ := exists_isCoupling_lt_of_wassersteinEDist_lt (h ▸ hc_pos)
  rw [transportCost, eLpNorm_eq_lintegral_rpow_eNorm_toReal hp₀ hp_top
      measurable_edist.aestronglyMeasurable] at hlt
  simp only [eNorm_eq_self] at hlt
  have hcost := (ENNReal.rpow_lt_rpow_iff (one_div_pos.mpr hq)).mp hlt
  have hbad : π {xy | ENNReal.ofReal δ ≤ edist xy.1 xy.2} ≤ ε := by
    simp_rw [← ENNReal.rpow_le_rpow_iff hq (x := ENNReal.ofReal δ)]
    refine (meas_ge_le_lintegral_div (μ := π) (measurable_edist.pow_const q).aemeasurable
      hδq.ne' hδq_top).trans ?_
    exact ENNReal.div_le_of_le_mul' hcost.le
  have hsub : Prod.fst ⁻¹' F ⊆
      (Prod.snd ⁻¹' thickening δ F) ∪ {xy : X × X | ENNReal.ofReal δ ≤ edist xy.1 xy.2} := by
    intro xy hxy
    rcases lt_or_ge (edist xy.1 xy.2) (ENNReal.ofReal δ) with hlt | hge
    · exact Or.inl ((mem_thickening_iff_exists_edist_lt F xy.2).2 ⟨xy.1, hxy, by rwa [edist_comm]⟩)
    · exact Or.inr hge
  rw [← hπ.fst_eq, Measure.fst_apply hF.measurableSet, ← hπ.snd_eq,
    Measure.snd_apply isOpen_thickening.measurableSet]
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add le_rfl hbad))

private theorem measure_eq_of_wassersteinEDist_eq_zero_of_ne_top
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hp₀ : p ≠ 0) (hp_top : p ≠ ∞) (h : wassersteinEDist p μ ν = 0) : μ = ν := by
  have closed_le {a b : Measure X} [IsFiniteMeasure b] (hab : wassersteinEDist p a b = 0)
      (F : Set X) (hF : IsClosed F) : a F ≤ b F := by
    refine ge_of_tendsto (tendsto_measure_thickening_of_isClosed
      ⟨1, zero_lt_one, measure_ne_top b _⟩ hF) ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact measure_closed_le_thickening hp₀ hp_top hab hF hδ
  have h' : wassersteinEDist p ν μ = 0 := (wassersteinEDist_comm p ν μ).trans h
  refine ext_of_generate_finite {s : Set X | IsClosed s} ?_ isPiSystem_isClosed ?_ ?_
  · rw [BorelSpace.measurable_eq (α := X), borel_eq_generateFrom_isClosed]
  · exact fun F hF ↦ le_antisymm (closed_le h F hF) (closed_le h' F hF)
  · simp

/-- Positive-exponent Wasserstein distance separates Borel probability measures. -/
theorem wassersteinEDist_eq_zero_iff (hp : p ≠ 0)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    wassersteinEDist p μ ν = 0 ↔ μ = ν := by
  refine ⟨fun h ↦ ?_, fun e ↦ e ▸ wassersteinEDist_self p μ⟩
  rcases eq_or_ne p ∞ with rfl | htop
  · have h₁ : wassersteinEDist 1 μ ν = 0 :=
      le_antisymm ((wassersteinEDist_mono le_top).trans_eq h) zero_le
    exact measure_eq_of_wassersteinEDist_eq_zero_of_ne_top one_ne_zero ENNReal.one_ne_top h₁
  · exact measure_eq_of_wassersteinEDist_eq_zero_of_ne_top hp htop h

end Separation

section Pushforward

variable [OpensMeasurableSpace X]
variable {Y : Type*} [MeasurableSpace Y] [PseudoEMetricSpace Y]
  [BorelSpace Y] [SecondCountableTopology Y]

/-- Applying a Lipschitz map to both coordinates multiplies the transport cost by at most its
Lipschitz constant. Measurability of the source displacement is not needed. -/
theorem transportCost_map_le (hp : 0 < p) {L : ℝ≥0} {f : X → Y} (hf : LipschitzWith L f) :
    transportCost p (π.map (Prod.map f f)) ≤ L * transportCost p π := by
  have hfm : Measurable f := hf.continuous.measurable
  have hmeas : Measurable (fun xy : X × X ↦ edist (f xy.1) (f xy.2)) :=
    (hfm.comp measurable_fst).edist (hfm.comp measurable_snd)
  rw [transportCost, eLpNorm_map_measure measurable_edist.aestronglyMeasurable
    (hfm.prodMap hfm).aemeasurable, transportCost, ← eLpNorm_const_mul_ennreal_of_pos hp]
  exact eLpNorm_mono_eNorm hmeas.aestronglyMeasurable fun xy ↦ by
    exact hf.edist_le_mul xy.1 xy.2

/-- Lipschitz pushforward of probability measures is Lipschitz for the extended Wasserstein
distance, with the same Lipschitz constant. -/
theorem wassersteinEDist_map_le (hp : 0 < p) {L : ℝ≥0} {f : X → Y} (hf : LipschitzWith L f)
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    wassersteinEDist p (μ.map f) (ν.map f) ≤ L * wassersteinEDist p μ ν := by
  have hfm : Measurable f := hf.continuous.measurable
  have : Nonempty {π : Measure (X × X) // IsCoupling π μ ν} :=
    ⟨⟨μ.prod ν, IsCoupling.prod μ ν⟩⟩
  unfold wassersteinEDist
  rw [ENNReal.mul_iInf (by simp)]
  exact le_iInf fun π ↦ (wassersteinEDist_le_of_isCoupling (π.2.map hfm hfm)).trans
    (transportCost_map_le hp hf)

end Pushforward

end MeasureTheory
