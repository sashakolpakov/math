import OAI.RepresentationTheory.Weil.Local.FourierTools

/-! # Linear Substitution -/

namespace OAI.RepresentationTheory.Weil.Local.LinearSubstitution.Construction

noncomputable section

/-! Coordinate substitutions on the Bruhat space, normalized by Haar measure. -/

open _root_.MeasureTheory
open scoped NNReal

def positionLinearEquiv {k : Type} [Field k] {n : ℕ}
    (A : FunctionsMetaplectic.Construction.GeneralLinear k n) : FunctionsMetaplectic.Construction.Position k n ≃ₗ[k] FunctionsMetaplectic.Construction.Position k n :=
  (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv

theorem positionLinearEquiv_apply {k : Type} [Field k] {n : ℕ}
    (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (x : FunctionsMetaplectic.Construction.Position k n) :
    positionLinearEquiv A x = Matrix.mulVec (A : Matrix (Fin n) (Fin n) k) x := rfl

def positionAddEquiv {k : Type} [NormedField k] {n : ℕ}
    (A : FunctionsMetaplectic.Construction.GeneralLinear k n) : FunctionsMetaplectic.Construction.Position k n ≃ₜ+ FunctionsMetaplectic.Construction.Position k n where
  __ := (positionLinearEquiv A).toAddEquiv
  continuous_toFun := by
    change Continuous (fun x => Matrix.mulVec (A : Matrix (Fin n) (Fin n) k) x)
    unfold Matrix.mulVec
    fun_prop
  continuous_invFun := by
    change Continuous (fun x => Matrix.mulVec (↑(A⁻¹) : Matrix (Fin n) (Fin n) k) x)
    unfold Matrix.mulVec
    fun_prop

def testSubstitution {k : Type} [NormedField k] {n : ℕ}
    (A : FunctionsMetaplectic.Construction.GeneralLinear k n) : FunctionsMetaplectic.Construction.schwartzBruhat k n ≃ₗ[ℂ] FunctionsMetaplectic.Construction.schwartzBruhat k n :=
  FunctionsMetaplectic.Construction.schwartzBruhat_coordinateEquiv (positionAddEquiv A⁻¹)

theorem testSubstitution_apply {k : Type} [NormedField k] {n : ℕ}
    (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n) :
    (testSubstitution A f).val x =
      f.val (Matrix.mulVec (↑(A⁻¹) : Matrix (Fin n) (Fin n) k) x) := rfl

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}

/-- The Jacobian of a coordinate change is defined by its effect on Haar
measure; it is not an assumed determinant formula. -/
def coordinateJacobian (e : FunctionsMetaplectic.Construction.Position k n ≃ₜ+ FunctionsMetaplectic.Construction.Position k n) : ℝ :=
  addEquivAddHaarChar e

theorem coordinateJacobian_pos (e : FunctionsMetaplectic.Construction.Position k n ≃ₜ+ FunctionsMetaplectic.Construction.Position k n) :
    0 < coordinateJacobian e := addEquivAddHaarChar_pos e

theorem integral_comp_coordinate_inverse
    (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (e : FunctionsMetaplectic.Construction.Position k n ≃ₜ+ FunctionsMetaplectic.Construction.Position k n) (f : FunctionsMetaplectic.Construction.Position k n → ℝ) :
    (∫ x, f (e.symm x) ∂μ) = coordinateJacobian e * ∫ x, f x ∂μ := by
  let em := e.toHomeomorph.toMeasurableEquiv
  calc
    _ = ∫ x, f x ∂(μ.map em.symm) := (integral_map_equiv em.symm f).symm
    _ = ∫ x, f x ∂(μ.comap em) := by rw [em.map_symm]
    _ = coordinateJacobian e * ∫ x, f x ∂μ := by
      exact integral_comap_eq_addEquivAddHaarChar_smul μ e

def coordinateScale (e : FunctionsMetaplectic.Construction.Position k n ≃ₜ+ FunctionsMetaplectic.Construction.Position k n) : ℝ :=
  (Real.sqrt (coordinateJacobian e))⁻¹

theorem coordinateScale_pos (e : FunctionsMetaplectic.Construction.Position k n ≃ₜ+ FunctionsMetaplectic.Construction.Position k n) :
    0 < coordinateScale e := inv_pos.mpr (Real.sqrt_pos.mpr (coordinateJacobian_pos e))

theorem coordinateScale_sq_jacobian (e : FunctionsMetaplectic.Construction.Position k n ≃ₜ+ FunctionsMetaplectic.Construction.Position k n) :
    coordinateScale e ^ 2 * coordinateJacobian e = 1 := by
  rw [coordinateScale, inv_pow, Real.sq_sqrt (coordinateJacobian_pos e).le]
  exact inv_mul_cancel₀ (coordinateJacobian_pos e).ne'

def coordinateScaleUnit (e : FunctionsMetaplectic.Construction.Position k n ≃ₜ+ FunctionsMetaplectic.Construction.Position k n) : ℂˣ :=
  Units.mk0 (coordinateScale e : ℂ) (Complex.ofReal_ne_zero.mpr (coordinateScale_pos e).ne')

def normalizedCoordinate (e : FunctionsMetaplectic.Construction.Position k n ≃ₜ+ FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.schwartzBruhat k n ≃ₗ[ℂ] FunctionsMetaplectic.Construction.schwartzBruhat k n :=
  (FunctionsMetaplectic.Construction.schwartzBruhat_coordinateEquiv e.symm).trans (LinearEquiv.smulOfUnit (coordinateScaleUnit e))

theorem normalizedCoordinate_apply (e : FunctionsMetaplectic.Construction.Position k n ≃ₜ+ FunctionsMetaplectic.Construction.Position k n)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n) :
    (normalizedCoordinate e f).val x = (coordinateScale e : ℂ) * f.val (e.symm x) := rfl

theorem normalizedCoordinate_unitary
    (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (e : FunctionsMetaplectic.Construction.Position k n ≃ₜ+ FunctionsMetaplectic.Construction.Position k n) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    (∫ x, ‖(normalizedCoordinate e f).val x‖ ^ 2 ∂μ) = ∫ x, ‖f.val x‖ ^ 2 ∂μ := by
  simp only [normalizedCoordinate_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (coordinateScale_pos e), mul_pow]
  rw [integral_const_mul,
    integral_comp_coordinate_inverse μ e (fun x => ‖f.val x‖ ^ 2)]
  rw [← mul_assoc, coordinateScale_sq_jacobian, one_mul]

theorem normalizedCoordinate_l2Energy
    (e : FunctionsMetaplectic.Construction.Position k n ≃ₜ+ FunctionsMetaplectic.Construction.Position k n) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    FunctionsMetaplectic.Construction.l2Energy k n (normalizedCoordinate e f) = FunctionsMetaplectic.Construction.l2Energy k n f :=
  normalizedCoordinate_unitary
    (Measure.pi (fun _ : Fin n => (Measure.addHaar : Measure k))) e f

end

end OAI.RepresentationTheory.Weil.Local.LinearSubstitution.Construction
