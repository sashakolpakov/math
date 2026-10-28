import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! # Coordinate Transform -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.CoordinateTransform

noncomputable section

/-! A linear change of point coordinates induces the contragredient
change of section coefficients. The actual dual pairing fixes the
transpose convention used by the projective-coordinate action. -/
universe u v
variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι]

def pointCoordinateDualTransform (T : (ι → R) ≃ₗ[R] (ι → R)) :
    Module.Dual R (ι →₀ R) ≃ₗ[R] Module.Dual R (ι →₀ R) :=
  (Finsupp.llift R R R ι).symm.trans (T.trans (Finsupp.llift R R R ι))

def pointCoordinateCoefficientTransform (T : (ι → R) ≃ₗ[R] (ι → R)) :
    (ι →₀ R) ≃ₗ[R] (ι →₀ R) :=
  (Module.evalEquiv R (ι →₀ R)).trans
    ((pointCoordinateDualTransform T).dualMap.trans (Module.evalEquiv R (ι →₀ R)).symm)

theorem pointCoordinateCoefficientTransform_pairing
    (T : (ι → R) ≃ₗ[R] (ι → R)) (φ : Module.Dual R (ι →₀ R)) (a : ι →₀ R) :
    φ (pointCoordinateCoefficientTransform T a) = pointCoordinateDualTransform T φ a := by
  change φ ((Module.evalEquiv R (ι →₀ R)).symm
    ((pointCoordinateDualTransform T).dualMap (Module.evalEquiv R (ι →₀ R) a))) = _
  rw [Module.apply_evalEquiv_symm_apply]
  rfl

theorem pointCoordinateCoefficientTransform_values
    (T : (ι → R) ≃ₗ[R] (ι → R)) (v : ι → R) (i : ι) :
    (Finsupp.llift R R R ι v)
      (pointCoordinateCoefficientTransform T (Finsupp.single i 1)) = T v i := by
  rw [pointCoordinateCoefficientTransform_pairing]
  change (Finsupp.llift R R R ι
    (T ((Finsupp.llift R R R ι).symm (Finsupp.llift R R R ι v)))) (Finsupp.single i 1) = _
  rw [LinearEquiv.symm_apply_apply]
  exact congrFun ((Finsupp.llift R R R ι).symm_apply_apply (T v)) i

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.CoordinateTransform
