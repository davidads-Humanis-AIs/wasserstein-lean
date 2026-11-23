/-
Copyright (c) 2026 David A. Dalrymple. All rights reserved.
Released under MIT OR Apache-2.0 license as described in the file LICENSE.
Authors: dhai (davidad's Humanis AIs)
-/
module

public import Wasserstein.Coupling
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Path laws from successive couplings

A sequence of pair laws with matching marginals is realized as the law of a single random
path. The transition at step `n` samples the next coordinate from the conditional kernel of
the `n`-th pair law. The coordinate spaces may depend on time.
-/

public section

open ProbabilityTheory

namespace MeasureTheory.Measure

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- Mapping the first coordinate of a composition-product with a pulled-back kernel gives
composition-product with the original kernel and the pushed-forward first marginal. -/
theorem map_compProd_comap (μ : Measure α) [IsFiniteMeasure μ] {f : α → β} (hf : Measurable f)
    (κ : Kernel β γ) [IsFiniteKernel κ] :
    (μ ⊗ₘ κ.comap f hf).map (Prod.map f id) = (μ.map f) ⊗ₘ κ := by
  refine ext_prod fun {s t} hs ht ↦ ?_
  have hpre : (Prod.map f id) ⁻¹' (s ×ˢ t) = (f ⁻¹' s) ×ˢ t := by ext; simp
  rw [map_apply (hf.prodMap measurable_id) (hs.prod ht), hpre,
    compProd_apply_prod (hf hs) ht, compProd_apply_prod hs ht,
    setLIntegral_map hs (Kernel.measurable_coe κ ht) hf]
  exact setLIntegral_congr_fun (hf hs) fun _ _ ↦ by rw [Kernel.comap_apply]

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

open Finset Function MeasureTheory MeasurableSpace Preorder

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]

/-- The coordinate at time zero under the path law has the initial law. -/
theorem trajMeasure_map_eval_zero (μ₀ : Measure (X 0))
    (κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))) [∀ n, IsMarkovKernel (κ n)] :
    (trajMeasure μ₀ κ).map (fun ω ↦ ω 0) = μ₀ := by
  let e := MeasurableEquiv.piUnique (fun i : Iic 0 ↦ X i)
  let f : (Π i : Iic 0, X i) → X 0 := fun xs ↦ xs ⟨0, mem_Iic.mpr le_rfl⟩
  have hf : Measurable f := measurable_pi_apply _
  have hf₀ : f ∘ e.symm = id := funext fun a ↦ e.apply_symm_apply a
  have h₀ : (trajMeasure μ₀ κ).map (frestrictLe 0) = μ₀.map e.symm := by
    rw [trajMeasure, Measure.map_comp _ _ (measurable_frestrictLe 0),
      traj_map_frestrictLe, partialTraj_self, Measure.id_comp]
  calc
    (trajMeasure μ₀ κ).map (fun ω ↦ ω 0) = ((trajMeasure μ₀ κ).map (frestrictLe 0)).map f :=
      (Measure.map_map hf (measurable_frestrictLe 0)).symm
    _ = μ₀ := by rw [h₀, Measure.map_map hf e.symm.measurable, hf₀, Measure.map_id]

variable [∀ n, StandardBorelSpace (X (n + 1))] [∀ n, Nonempty (X (n + 1))]

/-- At step `n`, use the conditional law of the next coordinate given the current coordinate. -/
noncomputable def chainKernel (π : (n : ℕ) → Measure (X n × X (n + 1)))
    [∀ n, IsFiniteMeasure (π n)] (n : ℕ) : Kernel (Π i : Iic n, X i) (X (n + 1)) :=
  (π n).condKernel.comap (fun ω ↦ ω ⟨n, mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

instance (π : (n : ℕ) → Measure (X n × X (n + 1))) [∀ n, IsFiniteMeasure (π n)] (n : ℕ) :
    IsMarkovKernel (chainKernel π n) := by
  unfold chainKernel
  infer_instance

/-- Start at `μ₀` and iterate the transitions obtained from the prescribed pair laws. -/
noncomputable def chainMeasure (μ₀ : Measure (X 0)) (π : (n : ℕ) → Measure (X n × X (n + 1)))
    [∀ n, IsFiniteMeasure (π n)] : Measure (Π n, X n) :=
  trajMeasure μ₀ (chainKernel π)

instance (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (π : (n : ℕ) → Measure (X n × X (n + 1))) [∀ n, IsFiniteMeasure (π n)] :
    IsProbabilityMeasure (chainMeasure μ₀ π) := by
  unfold chainMeasure
  infer_instance

private theorem chainMeasure_map_pair (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (π : (n : ℕ) → Measure (X n × X (n + 1))) [∀ n, IsFiniteMeasure (π n)] {n : ℕ}
    (hn : (chainMeasure μ₀ π).map (fun ω ↦ ω n) = (π n).fst) :
    (chainMeasure μ₀ π).map (fun ω ↦ (ω n, ω (n + 1))) = π n := by
  let f : (Π i : Iic n, X i) → X n := fun xs ↦ xs ⟨n, mem_Iic.mpr le_rfl⟩
  have hf : Measurable f := measurable_pi_apply _
  let P := chainMeasure μ₀ π
  have hpair : (P.map (frestrictLe n)) ⊗ₘ chainKernel π n =
      P.map (fun ω ↦ (frestrictLe n ω, ω (n + 1))) :=
    map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
  have heval : (P.map (frestrictLe n)).map f = (π n).fst :=
    (Measure.map_map hf (measurable_frestrictLe n)).trans hn
  have hm : Measurable (fun ω : (∀ i, X i) ↦ (frestrictLe n ω, ω (n + 1))) :=
    (measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1))
  calc
    P.map (fun ω ↦ (ω n, ω (n + 1))) =
        (P.map (fun ω ↦ (frestrictLe n ω, ω (n + 1)))).map (Prod.map f id) :=
      (Measure.map_map (hf.prodMap measurable_id) hm).symm
    _ = ((P.map (frestrictLe n)) ⊗ₘ chainKernel π n).map (Prod.map f id) := by rw [hpair]
    _ = (π n).fst ⊗ₘ (π n).condKernel := by
      rw [chainKernel, Measure.map_compProd_comap _ hf, heval]
    _ = π n := (π n).disintegrate (π n).condKernel

/-- The one-point marginal at time `n` of the chain is the prescribed measure. -/
theorem map_eval_chainMeasure (μ : (n : ℕ) → Measure (X n)) [IsProbabilityMeasure (μ 0)]
    (π : (n : ℕ) → Measure (X n × X (n + 1))) [∀ n, IsFiniteMeasure (π n)]
    (hπ : ∀ n, Measure.IsCoupling (π n) (μ n) (μ (n + 1))) (n : ℕ) :
    (chainMeasure (μ 0) π).map (fun ω ↦ ω n) = μ n := by
  induction n with
  | zero => exact trajMeasure_map_eval_zero _ _
  | succ n ih =>
    have hpair := chainMeasure_map_pair (μ 0) π (ih.trans (hπ n).fst_eq.symm)
    have hs := Measure.snd_map_prodMk (μ := chainMeasure (μ 0) π)
      (measurable_pi_apply n) (measurable_pi_apply (n + 1))
    exact hs.symm.trans (hpair ▸ (hπ n).snd_eq)

/-- The consecutive-pair marginal of the chain is the prescribed coupling. -/
theorem map_pair_chainMeasure (μ : (n : ℕ) → Measure (X n)) [IsProbabilityMeasure (μ 0)]
    (π : (n : ℕ) → Measure (X n × X (n + 1))) [∀ n, IsFiniteMeasure (π n)]
    (hπ : ∀ n, Measure.IsCoupling (π n) (μ n) (μ (n + 1))) (n : ℕ) :
    (chainMeasure (μ 0) π).map (fun ω ↦ (ω n, ω (n + 1))) = π n :=
  chainMeasure_map_pair (μ 0) π ((map_eval_chainMeasure μ π hπ n).trans (hπ n).fst_eq.symm)

/-- The chain has the prescribed one-point and consecutive-pair marginals. -/
theorem chainMeasure_marginals (μ : (n : ℕ) → Measure (X n)) [IsProbabilityMeasure (μ 0)]
    (π : (n : ℕ) → Measure (X n × X (n + 1))) [∀ n, IsFiniteMeasure (π n)]
    (hπ : ∀ n, Measure.IsCoupling (π n) (μ n) (μ (n + 1))) :
    (∀ n, (chainMeasure (μ 0) π).map (fun ω ↦ ω n) = μ n) ∧
      ∀ n, (chainMeasure (μ 0) π).map (fun ω ↦ (ω n, ω (n + 1))) = π n :=
  ⟨map_eval_chainMeasure μ π hπ, map_pair_chainMeasure μ π hπ⟩

end ProbabilityTheory.Kernel
