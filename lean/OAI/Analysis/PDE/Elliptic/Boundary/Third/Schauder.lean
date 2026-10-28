import OAI.Analysis.PDE.Elliptic.Boundary.Third.Tensor
import OAI.Analysis.PDE.Elliptic.Boundary.CommutatorHolder

/-! Closing the normal component of the third-order Schauder estimate.
The full tensor bound is linear in the tangential Hessian bounds and the
known normal differentiated source. -/

noncomputable section
open Set
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet

variable {I : Type*} [Fintype I] [DecidableEq I]

local instance thirdSchauderFirstGroup : NormedAddCommGroup
    (EuclideanSpace ℝ I →L[ℝ] ℝ) := inferInstance
local instance thirdSchauderFirstSpace : NormedSpace ℝ
    (EuclideanSpace ℝ I →L[ℝ] ℝ) := inferInstance
local instance thirdSchauderSecondGroup : NormedAddCommGroup
    (EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I →L[ℝ] ℝ) := inferInstance
local instance thirdSchauderSecondSpace : NormedSpace ℝ
    (EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I →L[ℝ] ℝ) := inferInstance

theorem third_holder_of_tangent_and_equation
    {S : Set (EuclideanSpace ℝ I)} {α : ℝ} (hα : 0 ≤ α)
    {u : EuclideanSpace ℝ I → ℝ} (hu : ContDiff ℝ 3 u) (k : I)
    (a : EuclideanSpace ℝ I → Matrix I I ℝ)
    (A : I × I → OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α) (R : OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α)
    (B : I → OAI.Analysis.Normed.Function.Holder.HolderMap S (EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I →L[ℝ] ℝ) α)
    (hA : ∀ p (x : S), OAI.Analysis.Normed.Function.Holder.HolderMap.value (A p) x = a x p.1 p.2)
    (hB : ∀ i, i ≠ k → ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value (B i) x =
      fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1))) x)
    {M μ : ℝ} (hM : 0 ≤ M) (hμ : 0 < μ)
    (hBn : ∀ i, i ≠ k → ‖B i‖ ≤ M) (hpos : ∀ x : S, μ ≤ a x k k)
    (heq : ∀ x : S, OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator a
      (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single k 1)) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value R x) :
    let N := 2 * (μ⁻¹ + (μ*μ)⁻¹ * ‖A (k,k)‖) *
      (‖R‖ + ∑ p ∈ (Finset.univ : Finset (I × I)).erase (k,k), 2 * ‖A p‖ * M)
    ∀ x y : S,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x-fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y‖ ≤
        (Fintype.card I : ℝ)^3 * (M+N) * ‖(x : EuclideanSpace ℝ I)-y‖^α := by
  classical
  dsimp only
  let T (p : I × I) : OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α :=
    holderEvaluate (holderEvaluate (B (if p.1 = k then p.2 else p.1))
      (EuclideanSpace.single (if p.1 = k then k else p.2) 1)) (EuclideanSpace.single k 1)
  have hT (p) (hp : p ≠ (k,k)) (x : S) :
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (T p) x = tangentThirdEntry u k p.1 p.2 x := by
    have hi := tangentThirdEntry_uses_tangent k p.1 p.2 hp
    simp only [T, value_holderEvaluate, hB _ hi, tangentThirdEntry]
    split_ifs <;> rfl
  have hTn (p) (hp : p ≠ (k,k)) : ‖T p‖ ≤ M := by
    apply (holderEvaluate_norm_le _ (by simp)).trans
    apply (holderEvaluate_norm_le _ (by simp)).trans
    exact hBn _ (tangentThirdEntry_uses_tangent k p.1 p.2 hp)
  obtain ⟨H, hH, hHn⟩ := exists_pure_normal_third_holder hα hu k a A T R hA hT hμ hpos heq
  let N := 2 * (μ⁻¹ + (μ*μ)⁻¹ * ‖A (k,k)‖) *
    (‖R‖ + ∑ p ∈ (Finset.univ : Finset (I × I)).erase (k,k), 2 * ‖A p‖ * M)
  have hHn' : ‖H‖ ≤ N := by
    apply hHn.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro p hp
    exact mul_le_mul_of_nonneg_left (hTn p (Finset.mem_erase.mp hp).1) (by positivity)
  have hN : 0 ≤ N := (norm_nonneg H).trans hHn'
  intro x y
  have ht (i) (hi : i ≠ k) :
      ‖fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1))) x -
        fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1))) y‖ ≤
        M * ‖(x : EuclideanSpace ℝ I)-y‖^α := by
    rw [← hB i hi x, ← hB i hi y]
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le (B i) x y).trans (by
      simpa only [Subtype.dist_eq, dist_eq_norm] using
        mul_le_mul_of_nonneg_right (hBn i hi) (Real.rpow_nonneg (dist_nonneg (x := x) (y := y)) α))
  have hn : |fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single k 1))) x
        (EuclideanSpace.single k 1) (EuclideanSpace.single k 1) -
      fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single k 1))) y
        (EuclideanSpace.single k 1) (EuclideanSpace.single k 1)| ≤
      N * ‖(x : EuclideanSpace ℝ I)-y‖^α := by
    rw [← hH x, ← hH y, ← Real.norm_eq_abs]
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le H x y).trans (by
      simpa only [Subtype.dist_eq, dist_eq_norm] using
        mul_le_mul_of_nonneg_right hHn' (Real.rpow_nonneg (dist_nonneg (x := x) (y := y)) α))
  have hh := third_difference_le_of_tangential_and_normal hu k x y
    (mul_nonneg hM (Real.rpow_nonneg (norm_nonneg _) _))
    (mul_nonneg hN (Real.rpow_nonneg (norm_nonneg _) _)) ht hn
  convert hh using 1 ; ring

end OAI.Analysis.PDE.Elliptic
