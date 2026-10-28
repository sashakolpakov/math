import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.PeriodSpace

/-! # Riemann Form -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.RiemannForm.CM.Abelian

noncomputable section

/-! The positive Hermitian form induced on the generic antiholomorphic period space. -/

open scoped TensorProduct

variable {U : Type*} [AddCommGroup U] [Module ℚ U]

theorem rationalBilin_conjugation (Q : LinearMap.BilinForm ℚ U)
    (x y : ComplexMultiplication.WeightOne.CM.Complexification U) :
    Q.baseChange ℂ (ComplexMultiplication.WeightOne.CM.coefficientConjugation U x) (ComplexMultiplication.WeightOne.CM.coefficientConjugation U y) =
      star (Q.baseChange ℂ x y) := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz, star_add]
  | tmul a u =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz, star_add]
    | tmul b v => simp

theorem rationalAlternating_complex_skew (Q : LinearMap.BilinForm ℚ U)
    (hQ : Q.IsAlt) (x y : ComplexMultiplication.WeightOne.CM.Complexification U) :
    Q.baseChange ℂ x y = -Q.baseChange ℂ y x := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz, neg_add]
  | tmul a u =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, LinearMap.add_apply, hy, hz, neg_add]
    | tmul b v =>
      rw [LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul,
        ← LinearMap.IsAlt.neg hQ u v]
      simp [mul_comm]

variable {H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U} (P : ComplexMultiplication.CM.Polarization.WeightOnePolarization H)

theorem antiholomorphic_isotropic (x y : H.antiholomorphic) :
    P.form.baseChange ℂ (x : ComplexMultiplication.WeightOne.CM.Complexification U) y = 0 := by
  have hz := P.holomorphic_isotropic
    (ComplexMultiplication.WeightOne.CM.coefficientConjugation U x) (PeriodSpace.CM.Abelian.conjugate_antiholomorphic_mem H x)
    (ComplexMultiplication.WeightOne.CM.coefficientConjugation U y) (PeriodSpace.CM.Abelian.conjugate_antiholomorphic_mem H y)
  rw [rationalBilin_conjugation] at hz
  exact star_eq_zero.mp hz

/-- The factor `2 I` makes the imaginary part equal to the original real alternating form. -/
def periodHermitian : H.antiholomorphic →ₗ⋆[ℂ] H.antiholomorphic →ₗ[ℂ] ℂ where
  toFun x :=
    { toFun := fun y => 2 * Complex.I *
        P.form.baseChange ℂ (ComplexMultiplication.WeightOne.CM.coefficientConjugation U (x : ComplexMultiplication.WeightOne.CM.Complexification U)) y
      map_add' := by intro y z; simp [mul_add]
      map_smul' := by intro a y; simp [mul_left_comm] }
  map_add' := by intro x y; ext z; simp [mul_add]
  map_smul' := by
    intro a x
    ext y
    simp [PeriodSpace.CM.Abelian.coefficientConjugation_complex_smul, mul_left_comm]

theorem periodHermitian_apply (x y : H.antiholomorphic) :
    periodHermitian P x y = 2 * Complex.I *
      P.form.baseChange ℂ (ComplexMultiplication.WeightOne.CM.coefficientConjugation U (x : ComplexMultiplication.WeightOne.CM.Complexification U)) y := rfl

theorem periodHermitian_symm (x y : H.antiholomorphic) :
    periodHermitian P y x = star (periodHermitian P x y) := by
  rw [periodHermitian_apply, periodHermitian_apply, star_mul,
    ← rationalBilin_conjugation, ComplexMultiplication.WeightOne.CM.coefficientConjugation_involutive]
  rw [rationalAlternating_complex_skew P.form P.alternating
    (x : ComplexMultiplication.WeightOne.CM.Complexification U) (ComplexMultiplication.WeightOne.CM.coefficientConjugation U y)]
  simp [mul_comm]

theorem periodHermitian_positive (x : H.antiholomorphic) (hx : x ≠ 0) :
    0 < (periodHermitian P x x).re := by
  have hcx : ComplexMultiplication.WeightOne.CM.coefficientConjugation U (x : ComplexMultiplication.WeightOne.CM.Complexification U) ≠ 0 := by
    intro hz
    apply hx
    apply Subtype.ext
    change (x : ComplexMultiplication.WeightOne.CM.Complexification U) = 0
    have he := congrArg (ComplexMultiplication.WeightOne.CM.coefficientConjugation U) hz
    simpa only [ComplexMultiplication.WeightOne.CM.coefficientConjugation_involutive, map_zero] using he
  have hp := P.hodge_positive (ComplexMultiplication.WeightOne.CM.coefficientConjugation U x)
    (PeriodSpace.CM.Abelian.conjugate_antiholomorphic_mem H x) hcx
  rw [ComplexMultiplication.WeightOne.CM.coefficientConjugation_involutive] at hp
  change 0 < (2 * Complex.I * P.form.baseChange ℂ (ComplexMultiplication.WeightOne.CM.coefficientConjugation U x) x).re
  norm_num [Complex.mul_re, Complex.mul_im] at hp ⊢
  linarith

theorem periodHermitian_imaginary (x y : H.antiholomorphic) :
    ((periodHermitian P x y).im : ℂ) =
      P.form.baseChange ℂ
        ((x : ComplexMultiplication.WeightOne.CM.Complexification U) + ComplexMultiplication.WeightOne.CM.coefficientConjugation U x)
        ((y : ComplexMultiplication.WeightOne.CM.Complexification U) + ComplexMultiplication.WeightOne.CM.coefficientConjugation U y) := by
  simp only [map_add, LinearMap.add_apply]
  rw [antiholomorphic_isotropic P x y,
    P.holomorphic_isotropic _ (PeriodSpace.CM.Abelian.conjugate_antiholomorphic_mem H x)
      _ (PeriodSpace.CM.Abelian.conjugate_antiholomorphic_mem H y), zero_add, add_zero]
  have hc : P.form.baseChange ℂ (x : ComplexMultiplication.WeightOne.CM.Complexification U) (ComplexMultiplication.WeightOne.CM.coefficientConjugation U y) =
      star (P.form.baseChange ℂ (ComplexMultiplication.WeightOne.CM.coefficientConjugation U x) y) := by
    simpa only [ComplexMultiplication.WeightOne.CM.coefficientConjugation_involutive] using
      rationalBilin_conjugation P.form (ComplexMultiplication.WeightOne.CM.coefficientConjugation U x) y
  rw [hc, periodHermitian_apply]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  ring

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.RiemannForm.CM.Abelian
