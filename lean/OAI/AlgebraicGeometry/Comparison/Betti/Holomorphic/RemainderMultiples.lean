import OAI.AlgebraicGeometry.Comparison.Betti.EntireMonomialDivision

/-! # Remainder Multiples -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.RemainderMultiples.Weierstrass

noncomputable section

/-! The actual holomorphic contour remainder vanishes on polynomial
multiples. This identifies the boundary terms in twisted Laurent splitting. -/

open _root_.Complex Set _root_.Metric _root_.Polynomial

open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder

theorem kernelCoeff_entire (d : ℕ) (P : Polynomial ℂ) (k : ℕ) :
    Differentiable ℂ (fun z => ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.kernelCoeff d P z k) := by
  unfold ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.kernelCoeff
  apply Differentiable.fun_sum
  intro j _
  exact (differentiable_id.pow (j - (k + 1))).mul_const (P.coeff j)

theorem remainderPolynomial_multiple_zero (d : ℕ) (P : Polynomial ℂ) (b : ℂ → ℂ)
    (hb : DifferentiableOn ℂ b (closedBall 0 1))
    (hP : ∀ z ∈ sphere 0 1, P.eval z ≠ 0) :
    ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.remainderPolynomial d P (fun z => P.eval z * b z) 0 1 = 0 := by
  ext k
  rw [ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.remainderPolynomial_coeff]
  split_ifs with hk
  · unfold ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.remainderCoeff
    have he : (∮ z in C(0, 1), (P.eval z * b z) / P.eval z * ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.kernelCoeff d P z k) =
        ∮ z in C(0, 1), b z * ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.kernelCoeff d P z k := by
      apply circleIntegral.integral_congr (by norm_num : 0 ≤ (1 : ℝ))
      intro z hz
      change (P.eval z * b z) / P.eval z * ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.kernelCoeff d P z k = b z * ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.kernelCoeff d P z k
      rw [mul_div_cancel_left₀ _ (hP z hz)]
    have hd : DifferentiableOn ℂ (fun z => b z * ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.kernelCoeff d P z k) (closedBall 0 1) :=
      hb.fun_mul (kernelCoeff_entire d P k).differentiableOn
    have hi : (∮ z in C(0, 1), b z * ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.kernelCoeff d P z k) = 0 :=
      (hd.mono closure_ball_subset_closedBall).diffContOnCl.circleIntegral_eq_zero (by norm_num)
    rw [he, hi, mul_zero]
    rfl
  · rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.RemainderMultiples.Weierstrass
