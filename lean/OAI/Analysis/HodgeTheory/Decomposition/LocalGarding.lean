import OAI.Analysis.HodgeTheory.Decomposition.FrozenGradient
import OAI.Analysis.HodgeTheory.Decomposition.IntegratedFreezing
import OAI.Analysis.HodgeTheory.Decomposition.LocalSchwartzDelta

/-! # Local Garding -/

namespace OAI.Analysis.HodgeTheory.Decomposition.LocalGarding.Constructions

noncomputable section

/-! A genuine local first-order Gårding estimate for projective Hodge forms.
The coefficient error is absorbed on a sufficiently small chart ball. -/

open _root_.MeasureTheory LineDeriv _root_.Metric
open scoped SchwartzMap BigOperators

theorem absorb_firstOrder_energy {G D T N L q b : ℝ}
    (hG : 0 ≤ G) (hD : 0 ≤ D) (hT : 0 ≤ T) (hN : 0 ≤ N)
    (hL : 0 ≤ L) (hb : 0 ≤ b) (hsmall : L * q ≤ 1 / 2)
    (h : G ≤ L * (D + (2 * T + q * G + b * N))) :
    G ≤ (4 * L + 2 * L * b + 1) * (D + T + N) := by
  have hsmallG := mul_le_mul_of_nonneg_right hsmall hG
  have hhalf : G ≤ 2 * L * D + 4 * L * T + 2 * L * b * N := by
    nlinarith only [h, hsmallG]
  let C := 4 * L + 2 * L * b + 1
  have hCD : 2 * L ≤ C := by dsimp [C]; nlinarith [mul_nonneg hL hb]
  have hCT : 4 * L ≤ C := by dsimp [C]; nlinarith [mul_nonneg hL hb]
  have hCN : 2 * L * b ≤ C := by dsimp [C]; linarith
  calc
    G ≤ 2 * L * D + 4 * L * T + 2 * L * b * N := hhalf
    _ ≤ C * D + C * T + C * N := add_le_add
      (add_le_add (mul_le_mul_of_nonneg_right hCD hD) (mul_le_mul_of_nonneg_right hCT hT))
      (mul_le_mul_of_nonneg_right hCN hN)
    _ = _ := by dsimp only [C]; ring

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)

theorem projectiveLocal_garding
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ r : ℝ, 0 < r ∧ closedBall z r ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ (a : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)))
          (ha : HasCompactSupport a) (_hs : tsupport a ⊆ closedBall z r),
          ∀ hU : tsupport a ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e,
          (∑ i : AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V,
            ∫ x, ‖∂_{stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) i} a x‖ ^ 2) ≤
            C * ((∫ x, ‖FrozenFourier.Constructions.projectiveFrozenD V (n + 1) a x‖ ^ 2) +
              (∫ x, ‖LocalSchwartzDelta.Constructions.projectiveLocalDeltaSchwartz V e n he a ha hU x‖ ^ 2) +
              ∫ x, ‖a x‖ ^ 2) := by
  obtain ⟨L, hL, hfreeze⟩ := FrozenGradient.Constructions.projectiveFrozen_gradient_estimate V e n he z hz
  obtain ⟨t, ht, htbound⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1 / 2)
    (4 * L * Fintype.card (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V))
  let ε := Real.sqrt t
  have hε : 0 < ε := Real.sqrt_pos.mpr ht
  have hεsq : ε ^ 2 = t := Real.sq_sqrt ht.le
  obtain ⟨U, hUopen, hzU, hUchart, hnear⟩ := FreezingError.Constructions.projectivePrincipalCoefficient_near V e n he z hz ε hε
  obtain ⟨s, hs, hball⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hzU)
  let r := s / 2
  have hr : 0 < r := half_pos hs
  have hclosed : closedBall z r ⊆ U :=
    (closedBall_subset_ball (by dsimp only [r]; linarith : r < s)).trans hball
  have hchart : closedBall z r ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := hclosed.trans hUchart
  obtain ⟨M, hM, hMbound⟩ := LocalCoefficientOperators.Constructions.projectiveAdjointZeroCoefficient_bounded V e n he
    (isCompact_closedBall z r) hchart
  let C := 4 * L + 2 * L * (4 * M ^ 2) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨r, hr, hchart, C, hC, fun a ha hsupport hdomain => ?_⟩
  let v := LocalSchwartzDelta.Constructions.projectiveLocalDeltaSchwartz V e n he a ha hdomain
  let w := FrozenFourier.Constructions.projectiveFrozenDelta V e n he z hz a
  have herror := IntegratedFreezing.Constructions.integrated_firstOrder_freezing
    (LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n) (LocalCoefficientOperators.Constructions.projectiveAdjointZeroCoefficient V e n)
    (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) a v w z ε M hε.le hM
    (LocalSchwartzDelta.Constructions.projectiveLocalDeltaSchwartz_apply V e n he a ha hdomain)
    (LocalSchwartzDelta.Constructions.projectiveFrozenDelta_apply V e n he z hz a)
    (fun x hx i => (hnear x (hclosed (hsupport hx)) i).le)
    (fun x hx => hMbound x (hsupport hx))
  have hcombined := (hfreeze a).trans (mul_le_mul_of_nonneg_left
    (add_le_add (le_refl (∫ x, ‖FrozenFourier.Constructions.projectiveFrozenD V (n + 1) a x‖ ^ 2)) herror) hL.le)
  have hsmall : L * (4 * ε ^ 2 * Fintype.card (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V)) ≤ 1 / 2 := by
    rw [hεsq]
    nlinarith only [htbound]
  exact absorb_firstOrder_energy
    (Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)))
    (integral_nonneg (fun _ => sq_nonneg _))
    (integral_nonneg (fun _ => sq_nonneg _))
    (integral_nonneg (fun _ => sq_nonneg _)) hL.le (by positivity) hsmall hcombined

end

end OAI.Analysis.HodgeTheory.Decomposition.LocalGarding.Constructions
