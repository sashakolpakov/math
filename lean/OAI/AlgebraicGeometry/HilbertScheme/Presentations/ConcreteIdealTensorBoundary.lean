import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.Boundary
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.Obstruction

/-! # Concrete Ideal Tensor Boundary -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ConcreteIdealTensorBoundary

noncomputable section

/-! The presentation boundary starts from the same multiplication
kernel used by the finite coefficient descent construction. -/

open TensorProduct

universe u v w t
variable {B : Type u} [CommRing B]
variable (M : Type t) [AddCommGroup M] [Module B M]

theorem idealTensorMultiplication_ker_eq (I : Ideal B) :
    (IdealTensor.Obstruction.idealTensorMultiplication B B M I).ker = (I.subtype.lTensor M).ker := by
  ext x
  change TensorProduct.rid B M (I.subtype.lTensor M x) = 0 ↔ I.subtype.lTensor M x = 0
  exact map_eq_zero_iff _ (TensorProduct.rid B M).injective

def idealTensorMultiplicationKernelEquiv (I : Ideal B) :
    (IdealTensor.Obstruction.idealTensorMultiplication B B M I).ker ≃ₗ[B] (I.subtype.lTensor M).ker :=
  LinearEquiv.ofEq _ _ (idealTensorMultiplication_ker_eq M I)

variable {M}
variable {K : Type v} [AddCommGroup K] [Module B K]
variable {F : Type w} [AddCommGroup F] [Module B F]
variable (f : K →ₗ[B] F) (g : F →ₗ[B] M)
variable (hf : Function.Injective f) (hex : Function.Exact f g) (hg : Function.Surjective g)
variable (I : Ideal B)

def actualIdealTensorBoundary : (IdealTensor.Obstruction.idealTensorMultiplication B B M I).ker →ₗ[B] K ⊗[B] (B ⧸ I) :=
  (IdealTensor.Boundary.idealTensorBoundary f g hf hex hg I).comp (idealTensorMultiplicationKernelEquiv M I).toLinearMap

theorem actualIdealTensorBoundary_eq_of_lift
    (x : (IdealTensor.Obstruction.idealTensorMultiplication B B M I).ker)
    (y : F ⊗[B] I) (hy : g.rTensor I y = x.val)
    (z : K) (hz : f z = IdealTensor.Obstruction.idealTensorMultiplication B B F I y) :
    actualIdealTensorBoundary f g hf hex hg I x = z ⊗ₜ[B] (1 : B ⧸ I) := by
  have hzt : f.rTensor B (z ⊗ₜ[B] (1 : B)) = I.subtype.lTensor F y := by
    apply (TensorProduct.rid B F).injective
    simpa only [LinearMap.rTensor_tmul, TensorProduct.rid_tmul, one_smul] using! hz
  have h := IdealTensor.Boundary.idealTensorBoundary_eq f g hf hex hg I
    (idealTensorMultiplicationKernelEquiv M I x) y hy (z ⊗ₜ[B] (1 : B)) hzt
  simpa only [actualIdealTensorBoundary, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearMap.lTensor_tmul, Submodule.mkQ_apply] using! h

def actualIdealTensorBoundaryEquiv [Module.Flat B F] :
    (IdealTensor.Obstruction.idealTensorMultiplication B B M I).ker ≃ₗ[B] (f.rTensor (B ⧸ I)).ker :=
  (idealTensorMultiplicationKernelEquiv M I).trans (IdealTensor.Boundary.idealTensorBoundaryEquiv f g hf hex hg I)

theorem actualIdealTensorBoundary_exact :
    Function.Exact (actualIdealTensorBoundary f g hf hex hg I) (f.rTensor (B ⧸ I)) := by
  intro y
  rw [IdealTensor.Boundary.idealTensorBoundary_exact f g hf hex hg I]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨(idealTensorMultiplicationKernelEquiv M I).symm x, ?_⟩
    simpa only [actualIdealTensorBoundary, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply] using hx
  · rintro ⟨x, hx⟩
    exact ⟨idealTensorMultiplicationKernelEquiv M I x, hx⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ConcreteIdealTensorBoundary
