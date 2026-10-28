import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.Obstruction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorCokernelInjectivity

/-! # Presentation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.Presentation

noncomputable section

/-! For a flat presentation, the ideal-tensor flatness obstruction is
equivalent to injectivity of the relation module after quotient base change. -/

open TensorProduct

universe u v w
variable {B : Type u} [CommRing B]
variable {F : Type v} [AddCommGroup F] [Module B F] [Module.Flat B F]
variable {M : Type w} [AddCommGroup M] [Module B M]

theorem presentation_tensor_quotient_injective_iff (q : F →ₗ[B] M)
    (hq : Function.Surjective q) (I : Ideal B) :
    Function.Injective (q.ker.subtype.lTensor (B ⧸ I)) ↔
      Function.Injective (Obstruction.idealTensorMultiplication B B M I) := by
  rw [q.ker.subtype.lTensor_inj_iff_rTensor_inj (B ⧸ I)]
  have he := TensorCokernelInjectivity.tensor_cokernel_injective_iff q.ker.subtype q I.subtype I.mkQ
    q.ker.subtype_injective q.exact_subtype_ker_map hq
    I.subtype_injective (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective
  rw [he]
  constructor
  · intro h
    exact (TensorProduct.rid B M).injective.comp h
  · intro h x y hxy
    apply h
    exact congrArg (TensorProduct.rid B M) hxy

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.Presentation
