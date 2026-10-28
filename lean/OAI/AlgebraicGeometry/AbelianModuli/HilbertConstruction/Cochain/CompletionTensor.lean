import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.HeadCompletion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompletionTensor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorFunctor

/-! # Completion Tensor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.CompletionTensor.CochainCompletionTensor

noncomputable section

/-! The cochain completion is a quasi-isomorphism after arbitrary tensor base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u v

variable {R : Type u} [CommRing R]
variable (C : CochainComplex (ModuleCat.{v} R) ℕ)
variable {F : Type v} [AddCommGroup F] [Module R F] (v : F →ₗ[R] C.X 1)
variable (A : Type v) [AddCommGroup A] [Module R A]
variable [Module.Flat R (C.X 1)] (h : Function.Surjective ((C.d 0 1).hom.coprod v))

abbrev original := HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex A (HeadCompletion.CochainHeadCompletion.complex C v)
abbrev replaced := HeadCompletion.CochainHeadCompletion.complex (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex A C) (v.lTensor A)

def component : ∀ n, (original C v A).X n ≅ (replaced C v A).X n
  | 0 => (CompletionTensor.CompletionTensorKernel.completionIso (C.d 0 1).hom v A h).toModuleIso
  | 1 => Iso.refl _
  | _ + 2 => Iso.refl _

def iso : original C v A ≅ replaced C v A :=
  HomologicalComplex.Hom.isoOfComponents (component C v A h) (by
    intro i j hij
    change i + 1 = j at hij
    subst j
    rcases i with _ | _ | n
    · change ModuleCat.ofHom ((CokernelCompletion.CokernelCompletionKernel.projection
          ((C.d 0 1).hom.lTensor A) (v.lTensor A)).comp
          (CompletionTensor.CompletionTensorKernel.completionIso (C.d 0 1).hom v A h).toLinearMap) =
        ModuleCat.ofHom ((CokernelCompletion.CokernelCompletionKernel.projection (C.d 0 1).hom v).lTensor A)
      exact ModuleCat.hom_ext (CompletionTensor.CompletionTensorKernel.projection_comp (C.d 0 1).hom v A h)
    · apply ModuleCat.hom_ext
      apply TensorProduct.ext
      ext a x
      rfl
    · exact (Category.id_comp ((replaced C v A).d (n + 2) (n + 3))).trans
        ((HeadCompletion.CochainHeadCompletion.d_succ_succ (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex A C) (v.lTensor A) n).trans
          ((congrArg (fun f : C.X (n + 2) ⟶ C.X (n + 3) => (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor A).map f)
            (HeadCompletion.CochainHeadCompletion.d_succ_succ C v n)).symm.trans
              (Category.comp_id ((original C v A).d (n + 2) (n + 3))).symm)))

theorem comparison :
    HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map A (HeadCompletion.CochainHeadCompletion.comparison C v) =
      (iso C v A h).hom ≫
        HeadCompletion.CochainHeadCompletion.comparison (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex A C) (v.lTensor A) := by
  ext n : 1
  rcases n with _ | _ | n
  · apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext a x
    change ((C.d 0 1).hom.coprod v).ker at x
    change a ⊗ₜ[R] (-x.val.1) =
      -(CompletionTensor.CompletionTensorKernel.completionIso (C.d 0 1).hom v A h (a ⊗ₜ[R] x)).val.1
    rw [CompletionTensor.CompletionTensorKernel.completionIso_tmul, TensorProduct.tmul_neg]
  · apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext a x
    rfl
  · apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext a x
    rfl

include h in
theorem quasiIso : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map A (HeadCompletion.CochainHeadCompletion.comparison C v)) := by
  have : QuasiIso
      (HeadCompletion.CochainHeadCompletion.comparison (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex A C) (v.lTensor A)) :=
    HeadCompletion.CochainHeadCompletion.quasiIso _ _
      (CompletionTensor.CompletionTensorKernel.tensor_surjective (C.d 0 1).hom v A h)
  rw [comparison C v A h]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.CompletionTensor.CochainCompletionTensor
