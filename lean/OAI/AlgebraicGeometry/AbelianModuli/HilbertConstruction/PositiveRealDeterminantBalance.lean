import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CenteredDeterminantWeights
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.InteriorPositiveCoefficientRelation

/-! # Positive Real Determinant Balance -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PositiveRealDeterminantBalance

noncomputable section

/-! Sparse configurations have strictly positive real weights on their
nonvanishing determinants for which all labeled-point degrees agree. -/
open scoped BigOperators Classical
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem centered_relation_has_equal_coordinate_sums {κ : Type v} [Fintype κ] {m : ℕ}
    (hm : 0 < m) (v : κ → Fin m → ℝ) (c : κ → ℝ)
    (h : ∑ k, c k • ZeroSumCoordinateProjection.zeroSumProjectionTo hm (v k) = 0) :
    ∀ i j, (∑ k, c k * v k i) = ∑ k, c k * v k j := by
  have hi (i : Fin m) : (∑ k, c k * v k i) =
      ∑ k, c k * ((∑ j, v k j) / m) := by
    let ev : ZeroSumCoordinateProjection.zeroSumCoordinates m →ₗ[ℝ] ℝ :=
      (LinearMap.proj i).comp (ZeroSumCoordinateProjection.zeroSumCoordinates m).subtype
    have he := congrArg ev h
    rw [map_sum, map_zero] at he
    simp_rw [map_smul, smul_eq_mul] at he
    change (∑ k, c k * (v k i - (∑ j, v k j) / m)) = 0 at he
    simp_rw [mul_sub, Finset.sum_sub_distrib] at he
    exact sub_eq_zero.mp he
  intro i j
  exact (hi i).trans (hi j).symm

private theorem positive_balanced_of_interior {κ : Type u} [Fintype κ] {m : ℕ}
    (hm : 0 < m) (v : κ → Fin m → ℝ)
    (hz : (0 : ZeroSumCoordinateProjection.zeroSumCoordinates m) ∈ interior (convexHull ℝ (Set.range (fun k => ZeroSumCoordinateProjection.zeroSumProjectionTo hm (v k))))) :
    ∃ c : κ → ℝ, (∀ k, 0 < c k) ∧ ∀ i j, (∑ k, c k * v k i) = ∑ k, c k * v k j := by
  obtain ⟨c, hc, hrel⟩ := InteriorPositiveCoefficientRelation.exists_positive_coefficients_sum_zero_of_interior
    (fun k => ZeroSumCoordinateProjection.zeroSumProjectionTo hm (v k)) hz
  exact ⟨c, hc, centered_relation_has_equal_coordinate_sums hm v c hrel⟩

theorem sparseConfiguration_positive_real_balanced_determinants
    {K : Type u} [Field K] {r m : ℕ}
    (v : Fin m → Fin r → K) (hv : ∀ i, v i ≠ 0) (hr : 2 ≤ r) (hm : 2 ≤ m)
    (hs : ∀ W : Submodule K (Fin r → K), W ≠ ⊤ →
      r * (Finset.univ.filter (fun i => v i ∈ W)).card < m) :
    ∃ c : CenteredDeterminantWeights.nonzeroDeterminantLabels v → ℝ, (∀ σ, 0 < c σ) ∧
      ∀ i j, (∑ σ, c σ * (DeterminantBlockDegrees.labeledDeterminantWeight σ.val i : ℝ)) =
        ∑ σ, c σ * (DeterminantBlockDegrees.labeledDeterminantWeight σ.val j : ℝ) := by
  exact positive_balanced_of_interior (by omega)
    (fun σ : CenteredDeterminantWeights.nonzeroDeterminantLabels v => CenteredDeterminantWeights.determinantIncidenceVector σ.val)
    (CenteredDeterminantWeights.centeredDeterminantWeights_zero_interior v hv hr hm hs)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PositiveRealDeterminantBalance
