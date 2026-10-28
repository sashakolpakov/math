import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Resolution

/-! # Tensor Regular -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.TensorRegular

noncomputable section

/-! Tensoring a regular parameter action with a projective module
preserves injectivity. This verifies termwise regularity for the
tensor resolution used to compute intersection Tor. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R] (r : R)

theorem tensor (M F : ModuleCat.{u} R) [Module.Flat R F] (hM : IsSMulRegular M r) :
    IsSMulRegular (M ⊗[R] F) r := by
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := F)
    (LinearMap.lsmul R M r) hM
  have he : (LinearMap.lsmul R M r).rTensor F = LinearMap.lsmul R (M ⊗[R] F) r := by
    change (r • (LinearMap.id : M →ₗ[R] M)).rTensor F =
      r • (LinearMap.id : M ⊗[R] F →ₗ[R] M ⊗[R] F)
    rw [LinearMap.rTensor_smul, LinearMap.rTensor_id]
  rwa [he] at h

theorem resolution (M N : ModuleCat.{u} R) (hM : IsSMulRegular M r)
    (P : ProjectiveResolution N) (i : ℕ) :
    IsSMulRegular
      ((((tensorLeft M).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).X i) r := by
  let : Module.Projective R (P.complex.X i) := inferInstance
  let : Module.Flat R (P.complex.X i) := inferInstance
  exact tensor R r M (P.complex.X i) hM

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.TensorRegular
