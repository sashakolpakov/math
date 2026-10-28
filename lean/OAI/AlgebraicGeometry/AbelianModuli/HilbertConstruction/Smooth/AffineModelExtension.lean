import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineModels

/-! # Affine Model Extension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth

noncomputable section

/-! A smooth affine model extends to any larger finite coefficient subalgebra. -/

open TensorProduct

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

def AffineModels.SmoothAffineModel.extend (M : AffineModels.SmoothAffineModel R A) (D : Subalgebra ℤ R) [Algebra.FiniteType ℤ D]
    (h : M.coefficients ≤ D) : AffineModels.SmoothAffineModel R A := by
  let : Algebra M.coefficients D := (Subalgebra.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower M.coefficients D R := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact {
    coefficients := D
    finiteType := inferInstance
    algebra := CommAlgCat.of D (D ⊗[M.coefficients] M.algebra)
    smooth := inferInstance
    recovery := M.recovery.trans
      (Algebra.TensorProduct.cancelBaseChange M.coefficients D R R M.algebra).symm }

@[simp] theorem AffineModels.SmoothAffineModel.extend_coefficients (M : AffineModels.SmoothAffineModel R A) (D : Subalgebra ℤ R)
    [Algebra.FiniteType ℤ D] (h : M.coefficients ≤ D) : (M.extend D h).coefficients = D := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth
