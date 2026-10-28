import OAI.Analysis.PDE.Schauder.Calculus.Schauder.AffineHolder
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Unnormalize

/-! The sharp-exponent local C²→C²,α theorem for arbitrary positive definite real coefficients. -/

noncomputable section
open Set Metric Matrix
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

theorem posDef_congruence_of_inverse {m : ℕ}
    (P Q A : Matrix (Fin m) (Fin m) ℝ) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hA : A.PosDef) : (Q * A * Q.transpose).PosDef := by
  have hQ : IsUnit Q := ⟨⟨Q, P, hQP, hPQ⟩, rfl⟩
  have hs : star Q = Q.transpose := by ext i j; rfl
  simpa only [hs] using (hQ.posDef_star_right_conjugate_iff (x := A)).mpr hA

theorem elliptic_pointwise_schauder {m : ℕ} (hm : 3 ≤ m) {α ρ : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hρ : 0 < ρ)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (F : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 2 u)
    (x₀ : EuclideanSpace ℝ (Fin m))
    (hPD : ∀ x ∈ ball x₀ ρ, (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x).PosDef)
    (heq : ∀ x ∈ ball x₀ ρ, nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A) u x = OAI.Analysis.Normed.Function.Holder.HolderMap.value F x) :
    ∃ s > 0, ∃ C > 0, ∀ x ∈ ball x₀ s, ∀ y ∈ ball x₀ s,
      ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ C * ‖x - y‖ ^ α := by
  have hA₀ : (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x₀).PosDef := hPD x₀ (by simpa using hρ)
  obtain ⟨L, P, Q, hP, hQ, hPQ, hQP, hQA⟩ := exists_normalization_matrices _ hA₀
  let φ := fun y : EuclideanSpace ℝ (Fin m) => x₀ + L y
  let ρ' := ρ / (‖L.toContinuousLinearMap‖ + 1)
  have hρ' : 0 < ρ' := div_pos hρ (by positivity)
  have hnear (y : EuclideanSpace ℝ (Fin m)) (hy : y ∈ ball 0 ρ') : φ y ∈ ball x₀ ρ := by
    have hy' : ‖y‖ < ρ' := by simpa only [mem_ball, dist_zero_right] using hy
    change ‖x₀ + L y - x₀‖ < ρ
    rw [add_sub_cancel_left]
    calc
      _ ≤ ‖L.toContinuousLinearMap‖ * ‖y‖ := L.toContinuousLinearMap.le_opNorm y
      _ ≤ (‖L.toContinuousLinearMap‖ + 1) * ‖y‖ := by nlinarith [norm_nonneg y]
      _ < (‖L.toContinuousLinearMap‖ + 1) * ρ' :=
        mul_lt_mul_of_pos_left hy' (by positivity)
      _ = ρ := by dsimp only [ρ']; field_simp
  let A' := OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (matrixCongruenceCLM Q)
    (holderLinearAffinePullback hα.le A x₀ L.toContinuousLinearMap)
  let F' := holderLinearAffinePullback hα.le F x₀ L.toContinuousLinearMap
  let v := fun y => u (φ y)
  have hv : ContDiff ℝ 2 v := hu.comp (contDiff_const.add L.contDiff)
  have hAval (y) : OAI.Analysis.Normed.Function.Holder.HolderMap.value A' y = Q * OAI.Analysis.Normed.Function.Holder.HolderMap.value A (φ y) * Q.transpose := rfl
  have hFval (y) : OAI.Analysis.Normed.Function.Holder.HolderMap.value F' y = OAI.Analysis.Normed.Function.Holder.HolderMap.value F (φ y) := rfl
  have hAzero : OAI.Analysis.Normed.Function.Holder.HolderMap.value A' 0 = 1 := by
    rw [hAval]
    change Q * OAI.Analysis.Normed.Function.Holder.HolderMap.value A (x₀ + L 0) * Q.transpose = 1
    simpa only [map_zero, add_zero] using hQA
  have hAPD (y) (hy : y ∈ ball 0 ρ') : (OAI.Analysis.Normed.Function.Holder.HolderMap.value A' y).PosDef := by
    rw [hAval]
    exact posDef_congruence_of_inverse P Q _ hPQ hQP (hPD _ (hnear y hy))
  have hveq (y) (hy : y ∈ ball 0 ρ') :
      nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A') v y = OAI.Analysis.Normed.Function.Holder.HolderMap.value F' y := by
    have h := nondivergence_conjugated_affine (OAI.Analysis.Normed.Function.Holder.HolderMap.value A) u hu P Q hPQ x₀ y
    have htransport : nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A') v y =
        nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A) u (φ y) := by
      change nondivergenceOperator (fun z => Q * OAI.Analysis.Normed.Function.Holder.HolderMap.value A (x₀ + L z) * Q.transpose)
        (fun z => u (x₀ + L z)) y = nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A) u (x₀ + L y)
      simpa only [hP] using! h
    rw [htransport, hFval, heq _ (hnear y hy)]
  obtain ⟨s, hs, C, hC, hh⟩ := normalized_pointwise_schauder hm hα hα1 hρ'
    A' F' v hv 0 hAzero hAPD hveq
  exact hessian_holder_of_affine u hu L x₀ hs hα.le hC hh

end OAI.Analysis.PDE.Schauder
