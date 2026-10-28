import OAI.Analysis.PDE.Elliptic.RankOneFrame

open InnerProductSpace
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def traceRight (H : E →L[ℝ] E) : (E →L[ℝ] E) →ₗ[ℝ] ℝ where
  toFun T := LinearMap.trace ℝ E (T.comp H).toLinearMap
  map_add' T U := by
    change LinearMap.trace ℝ E
      (T.toLinearMap.comp H.toLinearMap + U.toLinearMap.comp H.toLinearMap) = _
    exact map_add _ _ _
  map_smul' c T := by
    change LinearMap.trace ℝ E (c • T.toLinearMap.comp H.toLinearMap) = _
    exact map_smul _ _ _

theorem traceRight_rankOne (H : E →L[ℝ] E) (u v : E) :
    traceRight H (rankOne ℝ u v) = inner ℝ v (H u) := by
  change LinearMap.trace ℝ E ((rankOne ℝ u v).toLinearMap * H.toLinearMap) = _
  rw [LinearMap.trace_mul_comm]
  have heq : H.comp (rankOne ℝ u v) = rankOne ℝ (H u) v := by
    ext x
    simp [rankOne_apply]
  change LinearMap.trace ℝ E (H.comp (rankOne ℝ u v)).toLinearMap = _
  rw [heq, trace_rankOne]

/-- The symmetric trace representative of a real linear functional on
endomorphisms. It is constructed explicitly, without a spectral assumption. -/
def symmetricTraceDual {I : Type*} [Fintype I]
    (b : OrthonormalBasis I ℝ E) (L : (E →L[ℝ] E) →ₗ[ℝ] ℝ) : E →L[ℝ] E :=
  ∑ j, ∑ i, (L (rankOne ℝ (b i) (b j)) / 2) •
    (rankOne ℝ (b j) (b i) + rankOne ℝ (b i) (b j))

omit [FiniteDimensional ℝ E] in
theorem symmetricTraceDual_isSymmetric {I : Type*} [Fintype I]
    (b : OrthonormalBasis I ℝ E) (L : (E →L[ℝ] E) →ₗ[ℝ] ℝ) :
    (symmetricTraceDual b L).toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ (symmetricTraceDual b L x) y =
    inner ℝ x (symmetricTraceDual b L y)
  simp only [symmetricTraceDual, sum_apply, sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  simp only [smul_apply, add_apply,
    rankOne_apply, inner_smul_left, inner_smul_right, inner_add_left,
    inner_add_right, starRingEnd_apply, star_trivial]
  rw [real_inner_comm x (b j), real_inner_comm x (b i)]
  ring

theorem symmetricTraceDual_represents {I : Type*} [Fintype I]
    (b : OrthonormalBasis I ℝ E) (L : (E →L[ℝ] E) →ₗ[ℝ] ℝ)
    (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric) :
    traceRight H (symmetricTraceDual b L) = L H := by
  conv_rhs => rw [operator_rankOne_double_basis b H]
  simp only [symmetricTraceDual, map_sum, map_smul, map_add,
    traceRight_rankOne, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  have hs : inner ℝ (b j) (H (b i)) = inner ℝ (b i) (H (b j)) := by
    exact (hH (b j) (b i)).symm.trans (real_inner_comm _ _)
  rw [hs]
  ring

/-- In particular the representative has exactly the given rank-one symbol. -/
theorem symmetricTraceDual_symbol {I : Type*} [Fintype I]
    (b : OrthonormalBasis I ℝ E) (L : (E →L[ℝ] E) →ₗ[ℝ] ℝ) (v : E) :
    inner ℝ v (symmetricTraceDual b L v) = L (rankOne ℝ v v) := by
  have hr : (rankOne ℝ v v).toLinearMap.IsSymmetric := by
    intro x y
    simp only [ContinuousLinearMap.coe_coe, rankOne_apply,
      inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
    rw [real_inner_comm x v]
    ring
  have h := symmetricTraceDual_represents b L (rankOne ℝ v v) hr
  have hc : traceRight (rankOne ℝ v v) (symmetricTraceDual b L) =
      traceRight (symmetricTraceDual b L) (rankOne ℝ v v) := by
    change LinearMap.trace ℝ E
      ((symmetricTraceDual b L).toLinearMap * (rankOne ℝ v v).toLinearMap) =
      LinearMap.trace ℝ E
        ((rankOne ℝ v v).toLinearMap * (symmetricTraceDual b L).toLinearMap)
    rw [LinearMap.trace_mul_comm]
  rw [hc, traceRight_rankOne] at h
  exact h

end OAI.Analysis.PDE.Elliptic
