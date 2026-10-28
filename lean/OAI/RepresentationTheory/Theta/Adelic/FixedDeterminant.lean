import OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareQuotient
import OAI.RepresentationTheory.Weil.AdelicSplitting.Normalization

/-! # Fixed Determinant -/

namespace OAI.RepresentationTheory.Theta.Adelic.FixedDeterminant

noncomputable section

/-! Hermitian determinants and delta-normalized skew-Hermitian determinants
are actual scalar units, with their nonzero scalar given by the real coefficient. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.Normalization.Construction OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareQuotient

variable {k : Type} [Field k] [CharZero k] (d : k)

theorem fixed_im_zero (z : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) (hz : star z = z) : z.im = 0 := by
  have hi : -z.im = z.im := congrArg QuadraticAlgebra.im hz
  linear_combination -(1 / 2 : k) * hi

theorem fixedUnit_re_ne_zero (z : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ) (hz : star z = z) : z.val.re ≠ 0 := by
  intro hr
  apply z.ne_zero
  have hi := fixed_im_zero d z.val (congrArg Units.val hz)
  ext <;> simp [hr, hi]

def scalarReUnit (z : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ) (hz : star z = z) : kˣ :=
  Units.mk0 z.val.re (fixedUnit_re_ne_zero d z hz)

theorem scalarUnits_scalarReUnit (z : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ) (hz : star z = z) :
    QuadraticNormSquareQuotient.scalarUnits d (scalarReUnit d z hz) = z := by
  apply Units.ext
  ext
  · rfl
  · exact (fixed_im_zero d z.val (congrArg Units.val hz)).symm

omit [CharZero k] in
theorem hermitian_det_fixed {I : Type} [Fintype I] [DecidableEq I]
    (A : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) (hA : A.val.conjTranspose = A.val) :
    star (Matrix.GeneralLinearGroup.det A) = Matrix.GeneralLinearGroup.det A := by
  apply Units.ext
  change star A.val.det = A.val.det
  rw [← Matrix.det_conjTranspose, hA]

omit [CharZero k] in
theorem skew_det_fixed (hd : d ≠ 0) {n : ℕ}
    (K : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) (hK : K.val.conjTranspose = -K.val) :
    star ((Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd)⁻¹ ^ n * Matrix.GeneralLinearGroup.det K) =
      (Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd)⁻¹ ^ n * Matrix.GeneralLinearGroup.det K := by
  have hδ : star (Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd) = -Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd := by
    apply Units.ext
    ext <;> simp [Weil.AdelicSplitting.Normalization.Construction.deltaUnit]
  have hdet : star (Matrix.GeneralLinearGroup.det K) = (-1) ^ n * Matrix.GeneralLinearGroup.det K := by
    apply Units.ext
    change star K.val.det = (-1 : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) ^ n * K.val.det
    rw [← Matrix.det_conjTranspose, hK, Matrix.det_neg, Fintype.card_fin]
  have hnegδ : -(Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd)⁻¹ = (-1 : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ) * (Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd)⁻¹ := by simp
  rw [star_mul, star_pow, star_inv, hδ, hdet, inv_neg, hnegδ, mul_pow]
  have hsign : (-1 : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ) ^ n * (-1) ^ n = 1 := by
    rw [← mul_pow]
    simp
  rw [mul_mul_mul_comm, hsign, one_mul]
  exact mul_comm _ _

end

end OAI.RepresentationTheory.Theta.Adelic.FixedDeterminant
