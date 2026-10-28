import OAI.RepresentationTheory.Theta.Adelic.QuadraticNormCharacter
import OAI.RepresentationTheory.Weil.Local.RealLevi

/-! # Real Norm Gaussian -/

namespace OAI.RepresentationTheory.Theta.Adelic.RealNormGaussian

noncomputable section

/-! The norm criterion and its Gaussian identity at a real nonsplit
quadratic place. -/

open scoped Classical

open OAI.RepresentationTheory.Weil.Local.RealLevi.Construction
open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareQuotient OAI.RepresentationTheory.Theta.Adelic.QuadraticNormCharacter

theorem real_normRange_iff (d : ℝ) (hd : d < 0) (a : ℝˣ) :
    a ∈ (QuadraticNormSquareQuotient.normUnits d).range ↔ 0 < a.val := by
  constructor
  · rintro ⟨b, hb⟩
    have he := congrArg Units.val hb
    change QuadraticAlgebra.norm b.val = a.val at he
    rw [QuadraticNormChart.Compact.quadratic_norm] at he
    have hn : 0 ≤ a.val := by nlinarith [sq_nonneg b.val.re, sq_nonneg b.val.im]
    exact lt_of_le_of_ne hn a.ne_zero.symm
  · intro ha
    let r : ℝˣ := Units.mk0 (Real.sqrt a.val) (Real.sqrt_pos.mpr ha).ne'
    refine ⟨QuadraticNormSquareQuotient.scalarUnits d r, ?_⟩
    rw [QuadraticNormSquareQuotient.normUnits_scalar]
    apply Units.ext
    exact Real.sq_sqrt ha.le

theorem normSign_real (d : ℝ) (hd : d < 0) (a : ℝˣ) :
    QuadraticNormCharacter.normSign d a = if 0 < a.val then 1 else -1 := by
  unfold QuadraticNormCharacter.normSign
  rw [real_normRange_iff d hd]

theorem real_gaussian_square_neg (c : ℝ) (hc : c ≠ 0) :
    Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex ℝ (Weil.Local.Gaussian.Construction.realCharacter c) (-1) ^ 2 = -Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex ℝ (Weil.Local.Gaussian.Construction.realCharacter c) 1 ^ 2 := by
  have hs (a : ℝ) (ha : a ≠ 0) :
      Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex ℝ (Weil.Local.Gaussian.Construction.realCharacter c) a ^ 2 = Weil.Local.FunctionsMetaplectic.Construction.phase (Complex.I / ((c : ℂ) * a)) := by
    rw [Weil.Local.Gaussian.Construction.gaussianIndex_real_eq c a hc ha, Weil.Local.Gaussian.Construction.phase_pow]
    congr 1
    simp [one_div]
  rw [hs (-1) (by norm_num), hs 1 one_ne_zero]
  have he : Complex.I / ((c : ℂ) * (-1 : ℝ)) = -(Complex.I / ((c : ℂ) * (1 : ℝ))) := by
    push_cast
    ring
  rw [he]
  simp [Weil.Local.FunctionsMetaplectic.Construction.phase, norm_neg]

theorem real_norm_character_gaussian_identity
    (d : ℝ) (hd : d < 0) (c : ℝ) (hc : c ≠ 0) (a : ℝˣ) :
    (QuadraticNormCharacter.normSign d a : ℂ) *
        (Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex ℝ (Weil.Local.Gaussian.Construction.realCharacter c) 2 * Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex ℝ (Weil.Local.Gaussian.Construction.realCharacter c) (-2 * d)) =
      Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex ℝ (Weil.Local.Gaussian.Construction.realCharacter c) (2 * a.val) *
        Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex ℝ (Weil.Local.Gaussian.Construction.realCharacter c) (-2 * d * a.val) := by
  rw [normSign_real d hd,
    Weil.Local.RealLevi.Construction.gaussianIndex_real_positive_argument c hc 2 (by norm_num),
    Weil.Local.RealLevi.Construction.gaussianIndex_real_positive_argument c hc (-2 * d) (by nlinarith)]
  rcases lt_or_gt_of_ne a.ne_zero with ha | ha
  · rw [ite_eq_right (not_lt_of_gt ha), Circle.coe_neg, Circle.coe_one,
      Weil.Local.RealLevi.Construction.gaussianIndex_real_negative_argument c hc (2 * a.val) (by nlinarith),
      Weil.Local.RealLevi.Construction.gaussianIndex_real_negative_argument c hc (-2 * d * a.val) (mul_neg_of_pos_of_neg (by nlinarith) ha)]
    simp only [← pow_two]
    rw [real_gaussian_square_neg c hc]
    ring
  · rw [ite_eq_left ha, Circle.coe_one,
      Weil.Local.RealLevi.Construction.gaussianIndex_real_positive_argument c hc (2 * a.val) (by positivity),
      Weil.Local.RealLevi.Construction.gaussianIndex_real_positive_argument c hc (-2 * d * a.val) (mul_pos (by nlinarith) ha), one_mul]

theorem norm_character_gaussian_identity
    (d : ℝ) (hd : d ≠ 0) (c : ℝ) (hc : c ≠ 0) (a : ℝˣ) :
    (QuadraticNormCharacter.normSign d a : ℂ) *
        (Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex ℝ (Weil.Local.Gaussian.Construction.realCharacter c) 2 * Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex ℝ (Weil.Local.Gaussian.Construction.realCharacter c) (-2 * d)) =
      Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex ℝ (Weil.Local.Gaussian.Construction.realCharacter c) (2 * a.val) *
        Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex ℝ (Weil.Local.Gaussian.Construction.realCharacter c) (-2 * d * a.val) := by
  rcases lt_or_gt_of_ne hd with hd | hd
  · exact real_norm_character_gaussian_identity d hd c hc a
  · have hsq : IsSquare d := ⟨Real.sqrt d, by rw [← pow_two, Real.sq_sqrt hd.le]⟩
    rw [QuadraticNormCharacter.normSign_split d hd.ne' hsq a, Circle.coe_one, one_mul,
      Weil.Local.RealLevi.Construction.gaussianIndex_real_positive_argument c hc 2 (by norm_num),
      Weil.Local.RealLevi.Construction.gaussianIndex_real_negative_argument c hc (-2 * d) (by nlinarith)]
    rcases lt_or_gt_of_ne a.ne_zero with ha | ha
    · rw [Weil.Local.RealLevi.Construction.gaussianIndex_real_negative_argument c hc (2 * a.val) (by nlinarith),
        Weil.Local.RealLevi.Construction.gaussianIndex_real_positive_argument c hc (-2 * d * a.val)
          (mul_pos_of_neg_of_neg (by nlinarith) ha), mul_comm]
    · rw [Weil.Local.RealLevi.Construction.gaussianIndex_real_positive_argument c hc (2 * a.val) (by positivity),
        Weil.Local.RealLevi.Construction.gaussianIndex_real_negative_argument c hc (-2 * d * a.val)
          (mul_neg_of_neg_of_pos (by nlinarith) ha)]

end

end OAI.RepresentationTheory.Theta.Adelic.RealNormGaussian
