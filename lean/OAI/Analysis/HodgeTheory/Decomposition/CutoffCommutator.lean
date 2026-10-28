import OAI.Analysis.HodgeTheory.Decomposition.SupportedOperator
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # Cutoff Commutator -/

namespace OAI.Analysis.HodgeTheory.Decomposition.CutoffCommutator.Constructions

noncomputable section

/-! The commutator of an actual first-order operator with a real smooth
cutoff is an explicit order-zero operator. -/

open scoped BigOperators ContDiff

variable {E F G ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [Fintype ι]

def firstOrderCutoffCoefficient (C : ι → E → F →L[ℝ] G)
    (directions : ι → E) (f : E → ℝ) (x : E) : F →L[ℝ] G :=
  ∑ i, (fderiv ℝ f x (directions i)) • C i x

theorem localFirstOrderValue_real_smul
    (C : ι → E → F →L[ℝ] G) (Z : E → F →L[ℝ] G) (directions : ι → E)
    (f : E → ℝ) (u : E → F) (x : E)
    (hf : DifferentiableAt ℝ f x) (hu : DifferentiableAt ℝ u x) :
    SupportedOperator.Constructions.localFirstOrderValue C Z directions (fun y => f y • u y) x =
      f x • SupportedOperator.Constructions.localFirstOrderValue C Z directions u x +
        firstOrderCutoffCoefficient C directions f x (u x) := by
  rw [SupportedOperator.Constructions.localFirstOrderValue, fderiv_fun_smul hf hu]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply, map_add, map_smul,
    Finset.sum_add_distrib, ← Finset.smul_sum, firstOrderCutoffCoefficient, sum_apply, SupportedOperator.Constructions.localFirstOrderValue,
    smul_add]
  abel

theorem firstOrderCutoffCoefficient_norm_bound
    (C : ι → E → F →L[ℝ] G) (directions : ι → E) (f : E → ℝ) (x : E)
    (A B : ℝ) (hA : 0 ≤ A)
    (hC : ∀ i, ‖C i x‖ ≤ A) (hf : ∀ i, ‖fderiv ℝ f x (directions i)‖ ≤ B) :
    ‖firstOrderCutoffCoefficient C directions f x‖ ≤ Fintype.card ι * (B * A) := by
  calc
    _ ≤ ∑ i, ‖(fderiv ℝ f x (directions i)) • C i x‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, B * A := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_left (hC i) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (hf i) hA)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem firstOrderCutoffCoefficient_smooth
    (C : ι → E → F →L[ℝ] G) (directions : ι → E) (f : E → ℝ)
    {U : Set E} (hU : IsOpen U)
    (hC : ∀ i, ContDiffOn ℝ ∞ (C i) U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (firstOrderCutoffCoefficient C directions f) U := by
  apply ContDiffOn.sum
  intro i _
  have hd : ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x (directions i)) U := by
    intro x hx
    exact (((hf.contDiffAt (hU.mem_nhds hx)).fderiv_right (by simp)).clm_apply
      contDiffAt_const).contDiffWithinAt
  exact hd.smul (hC i)

theorem firstOrderCutoffCoefficient_bounded
    (C : ι → E → F →L[ℝ] G) (directions : ι → E) (f : E → ℝ)
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hC : ∀ i, ContDiffOn ℝ ∞ (C i) U) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K, ‖firstOrderCutoffCoefficient C directions f x‖ ≤ B := by
  obtain ⟨B, hB⟩ := hK.bddAbove_image
    (((firstOrderCutoffCoefficient_smooth C directions f hU hC hf).continuousOn.mono hKU).norm)
  exact ⟨max B 0, le_max_right _ _, fun x hx => (hB ⟨x, hx, rfl⟩).trans (le_max_left _ _)⟩

end

end OAI.Analysis.HodgeTheory.Decomposition.CutoffCommutator.Constructions
