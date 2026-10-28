import OAI.Analysis.HodgeTheory.Decomposition.LocalCoefficientOperators
import Mathlib.Algebra.Order.Chebyshev

/-! # Freezing Error -/

namespace OAI.Analysis.HodgeTheory.Decomposition.FreezingError.Constructions

noncomputable section

/-! Quantitative comparison of the true local codifferential with its frozen
principal coefficients. -/

open scoped _root_.Topology BigOperators

section Bound

variable {E F G ι : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem firstOrder_freezing_error
    (C : ι → E → F →L[ℝ] G) (Z : E → F →L[ℝ] G)
    (directions : ι → E) (u : E → F) (x z : E) (ε M : ℝ)
    (hC : ∀ i, ‖C i x - C i z‖ ≤ ε) (hZ : ‖Z x‖ ≤ M) :
    ‖((∑ i, C i x (fderiv ℝ u x (directions i))) + Z x (u x)) -
      ∑ i, C i z (fderiv ℝ u x (directions i))‖ ≤
        ε * (∑ i, ‖fderiv ℝ u x (directions i)‖) + M * ‖u x‖ := by
  have heq : ((∑ i, C i x (fderiv ℝ u x (directions i))) + Z x (u x)) -
      ∑ i, C i z (fderiv ℝ u x (directions i)) =
      (∑ i, (C i x - C i z) (fderiv ℝ u x (directions i))) + Z x (u x) := by
    simp only [sub_apply, Finset.sum_sub_distrib]
    abel
  rw [heq]
  calc
    _ ≤ ‖∑ i, (C i x - C i z) (fderiv ℝ u x (directions i))‖ + ‖Z x (u x)‖ := norm_add_le _ _
    _ ≤ (∑ i, ε * ‖fderiv ℝ u x (directions i)‖) + M * ‖u x‖ := by
      apply add_le_add
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro i _
        exact ((C i x - C i z).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hC i) (norm_nonneg _))
      · exact ((Z x).le_opNorm _).trans (mul_le_mul_of_nonneg_right hZ (norm_nonneg _))
    _ = _ := by rw [Finset.mul_sum]

theorem firstOrder_freezing_error_sq
    (C : ι → E → F →L[ℝ] G) (Z : E → F →L[ℝ] G)
    (directions : ι → E) (u : E → F) (x z : E) (ε M : ℝ) (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hC : ∀ i, ‖C i x - C i z‖ ≤ ε) (hZ : ‖Z x‖ ≤ M) :
    ‖((∑ i, C i x (fderiv ℝ u x (directions i))) + Z x (u x)) -
      ∑ i, C i z (fderiv ℝ u x (directions i))‖ ^ 2 ≤
        2 * ε ^ 2 * Fintype.card ι * (∑ i, ‖fderiv ℝ u x (directions i)‖ ^ 2) +
          2 * M ^ 2 * ‖u x‖ ^ 2 := by
  have h := firstOrder_freezing_error C Z directions u x z ε M hC hZ
  have hsum := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun i : ι => ‖fderiv ℝ u x (directions i)‖)
  simp only [Finset.card_univ] at hsum
  have hn : 0 ≤ ε * (∑ i, ‖fderiv ℝ u x (directions i)‖) + M * ‖u x‖ :=
    add_nonneg (mul_nonneg hε (Finset.sum_nonneg (fun _ _ => norm_nonneg _))) (mul_nonneg hM (norm_nonneg _))
  have hsquared := (sq_le_sq₀ (norm_nonneg _) hn).mpr h
  have hweighted := mul_le_mul_of_nonneg_left hsum (sq_nonneg ε)
  nlinarith [sq_nonneg (ε * (∑ i, ‖fderiv ℝ u x (directions i)‖) - M * ‖u x‖)]

end Bound

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)

/-- The actual principal coefficients can be made uniformly close to their frozen values on a chart neighborhood. -/
theorem projectivePrincipalCoefficient_near
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V), IsOpen U ∧ z ∈ U ∧ U ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e ∧
      ∀ y ∈ U, ∀ i : AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V,
        ‖LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i y - LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i z‖ < ε := by
  have hi (i : AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) : ∀ᶠ y in 𝓝 z,
      ‖LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i y - LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i z‖ < ε := by
    have hc := ((LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient_smooth V e n he i).continuousOn.continuousAt
      ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).eventually
        (Metric.ball_mem_nhds (LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i z) hε)
    simpa only [Metric.mem_ball, dist_eq_norm] using hc
  have hall : ∀ᶠ y in 𝓝 z, ∀ i : AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V,
      ‖LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i y - LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i z‖ < ε :=
    Filter.eventually_all.mpr hi
  obtain ⟨U, hU, hUopen, hzU⟩ := mem_nhds_iff.mp
    (Filter.inter_mem ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz) hall)
  exact ⟨U, hUopen, hzU, fun y hy => (hU hy).1, fun y hy => (hU hy).2⟩

end

end OAI.Analysis.HodgeTheory.Decomposition.FreezingError.Constructions
