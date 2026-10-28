import OAI.AlgebraicGeometry.ComplexMultiplication.CM.Polarization

/-! # Rational Bilinear Conjugation -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalBilinearConjugation.CM.Construction

noncomputable section

/-! Scalar extension of an arbitrary rational alternating form is
compatible with coefficient conjugation and has a real Hodge self-pairing. -/

open scoped TensorProduct

variable {U : Type*} [AddCommGroup U] [Module ℚ U]

theorem rationalBilinear_baseChange_conjugate (B : LinearMap.BilinForm ℚ U)
    (u v : WeightOne.CM.Complexification U) :
    star (B.baseChange ℂ u v) =
      B.baseChange ℂ (WeightOne.CM.coefficientConjugation U u) (WeightOne.CM.coefficientConjugation U v) := by
  induction u using TensorProduct.inductionOn with
  | tmul z x =>
      induction v using TensorProduct.inductionOn with
      | tmul w y =>
          simp only [LinearMap.BilinForm.baseChange_tmul, WeightOne.CM.coefficientConjugation_tmul,
            star_smul, star_trivial, star_mul]
          congr 1
          exact mul_comm _ _
      | add v w hv hw => simp [hv, hw]
  | add u v hu hv => simp [hu, hv]

theorem rationalAlternating_baseChange_skew (B : LinearMap.BilinForm ℚ U) (hB : B.IsAlt)
    (u v : WeightOne.CM.Complexification U) : B.baseChange ℂ u v = -B.baseChange ℂ v u := by
  induction u using TensorProduct.inductionOn with
  | tmul z x =>
      induction v using TensorProduct.inductionOn with
      | tmul w y =>
          simp only [LinearMap.BilinForm.baseChange_tmul]
          rw [← hB.neg_eq x y, neg_smul, neg_neg, mul_comm]
      | add v w hv hw => simp [hv, hw, add_comm]
  | add u v hu hv => simp [hu, hv, add_comm]

theorem rationalAlternating_hodge_self_real (B : LinearMap.BilinForm ℚ U) (hB : B.IsAlt)
    (u : WeightOne.CM.Complexification U) :
    (Complex.I * B.baseChange ℂ u (WeightOne.CM.coefficientConjugation U u)).im = 0 := by
  have hc := rationalBilinear_baseChange_conjugate B u (WeightOne.CM.coefficientConjugation U u)
  rw [WeightOne.CM.coefficientConjugation_involutive] at hc
  have hs := hc.trans (rationalAlternating_baseChange_skew B hB (WeightOne.CM.coefficientConjugation U u) u)
  have hr := congrArg Complex.re hs
  simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at hr
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
  linarith

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalBilinearConjugation.CM.Construction
