import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Tensor Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.TensorMaps

noncomputable section

/-! Coefficient extension maps on tensor algebras are injective when the modeled algebra is flat. -/

open TensorProduct

universe u

variable {C R B : Type u} [CommRing C] [CommRing R] [CommRing B] [Algebra C R] [Algebra C B]

def coefficientTensorMap (D : Subalgebra C R) : D ⊗[C] B →ₐ[C] R ⊗[C] B :=
  Algebra.TensorProduct.map D.val (AlgHom.id C B)

def coefficientTensorInclusion {D E : Subalgebra C R} (h : D ≤ E) :
    D ⊗[C] B →ₐ[C] E ⊗[C] B :=
  Algebra.TensorProduct.map (Subalgebra.inclusion h) (AlgHom.id C B)

theorem coefficientTensorMap_toLinearMap (D : Subalgebra C R) :
    (coefficientTensorMap (B := B) D).toLinearMap = LinearMap.rTensor B D.val.toLinearMap := by
  ext d b
  rfl

theorem coefficientTensorMap_injective (D : Subalgebra C R) [Module.Flat C B] :
    Function.Injective (coefficientTensorMap (B := B) D) := by
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := B) D.val.toLinearMap
    Subtype.val_injective
  exact (congrArg (fun f : D ⊗[C] B →ₗ[C] R ⊗[C] B => Function.Injective f)
    (coefficientTensorMap_toLinearMap (B := B) D)).mpr h

theorem coefficientTensorMap_comp_inclusion {D E : Subalgebra C R} (h : D ≤ E) :
    (coefficientTensorMap (B := B) E).comp (coefficientTensorInclusion h) = coefficientTensorMap D := by
  apply Algebra.TensorProduct.ext
  · ext d
    rfl
  · ext b
    rfl

theorem coefficientTensorMap_range_mono {D E : Subalgebra C R} (h : D ≤ E) :
    (coefficientTensorMap (B := B) D).range ≤ (coefficientTensorMap (B := B) E).range := by
  rintro x ⟨y, rfl⟩
  exact ⟨coefficientTensorInclusion h y, DFunLike.congr_fun (coefficientTensorMap_comp_inclusion h) y⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.TensorMaps
