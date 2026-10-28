import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.PolynomialCoordinates
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Frame Determinants -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Determinant criteria for changing frames in Grassmannian quotient charts. -/

universe u v

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V] {k : ℕ}

/-- Over any commutative ring, a square matrix is bijective precisely when its determinant is a unit. -/
theorem Grassmann.FrameDeterminants.matrix_bijective_iff_isUnit_det (M : Matrix (Fin k) (Fin k) R) :
    Function.Bijective M.mulVec ↔ IsUnit M.det := by
  constructor
  · intro h
    exact M.isUnit_iff_isUnit_det.mp (Matrix.mulVec_surjective_iff_isUnit.mp h.surjective)
  · intro h
    have hu := M.isUnit_iff_isUnit_det.mpr h
    exact ⟨Matrix.mulVec_injective_of_isUnit hu, Matrix.mulVec_surjective_iff_isUnit.mpr hu⟩

/-- The matrix of a proposed new frame, expressed in the existing quotient frame. -/
def Quotient.Charts.QuotientChart.frameMatrix (c : Quotient.Charts.QuotientChart R (Fin k → R) V)
    (a : (Fin k → R) →ₗ[R] ((Fin k → R) × V)) : Matrix (Fin k) (Fin k) R :=
  LinearMap.toMatrix' (c.frame.symm.toLinearMap.comp (c.val.mkQ.comp a))

/-- The frame matrix is the sum of the first component and the coordinate image of the second. -/
theorem Quotient.Charts.QuotientChart.frameMatrix_mulVec (c : Quotient.Charts.QuotientChart R (Fin k → R) V)
    (a : (Fin k → R) →ₗ[R] ((Fin k → R) × V)) (x : Fin k → R) :
    (c.frameMatrix a).mulVec x = (a x).1 + c.coordinates (a x).2 := by
  have he : (c.frameMatrix a).mulVecLin = c.frame.symm.toLinearMap.comp (c.val.mkQ.comp a) :=
    LinearMap.toMatrix'.symm_apply_apply _
  exact (LinearMap.congr_fun he x).trans (c.frame_symm_mkQ (a x).1 (a x).2)

/-- A proposed new frame is a basis of the quotient exactly on the unit-determinant locus. -/
theorem Quotient.Charts.QuotientChart.frame_bijective_iff_isUnit_det (c : Quotient.Charts.QuotientChart R (Fin k → R) V)
    (a : (Fin k → R) →ₗ[R] ((Fin k → R) × V)) :
    Function.Bijective (c.val.mkQ.comp a) ↔ IsUnit (c.frameMatrix a).det := by
  have he : (c.frameMatrix a).mulVecLin = c.frame.symm.toLinearMap.comp (c.val.mkQ.comp a) :=
    LinearMap.toMatrix'.symm_apply_apply _
  have hbij : Function.Bijective (c.frameMatrix a).mulVec ↔
      Function.Bijective (c.val.mkQ.comp a) := by
    change Function.Bijective ((c.frameMatrix a).mulVecLin) ↔ _
    rw [he]
    exact EquivLike.comp_bijective (c.val.mkQ.comp a) c.frame.symm
  exact hbij.symm.trans (Grassmann.FrameDeterminants.matrix_bijective_iff_isUnit_det _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
