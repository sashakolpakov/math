import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CochainHeadOne
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CompletionTensor
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleTensor

/-! # Cochain Completion -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CochainCompletion

noncomputable section

/-! The cochain completion is a quasi-isomorphism after arbitrary tensor base change. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u v

namespace Construction.CochainCompletionTensor

variable {R : Type u} [CommRing R]
variable (C : CochainComplex (ModuleCat.{v} R) ℕ)
variable {F : Type v} [AddCommGroup F] [Module R F] (v : F →ₗ[R] C.X 1)
variable (A : Type v) [AddCommGroup A] [Module R A]
variable [Module.Flat R (C.X 1)] (h : Function.Surjective ((C.d 0 1).hom.coprod v))

abbrev original := ModuleTensor.Construction.ModuleTensorFunctor.complex A (CochainHeadOne.Construction.CochainHeadCompletion.complex C v)
abbrev replaced := CochainHeadOne.Construction.CochainHeadCompletion.complex (ModuleTensor.Construction.ModuleTensorFunctor.complex A C) (v.lTensor A)

def component : ∀ n, (original C v A).X n ≅ (replaced C v A).X n
  | 0 => (CompletionTensor.Construction.CompletionTensorKernel.completionIso (C.d 0 1).hom v A h).toModuleIso
  | 1 => Iso.refl _
  | _ + 2 => Iso.refl _

def iso : original C v A ≅ replaced C v A :=
  HomologicalComplex.Hom.isoOfComponents (component C v A h) (by
    intro i j hij
    change i + 1 = j at hij
    subst j
    rcases i with _ | _ | n
    · change (component C v A h 0).hom ≫ (replaced C v A).d 0 1 =
        (original C v A).d 0 1 ≫ (component C v A h 1).hom
      change (component C v A h 0).hom ≫ (replaced C v A).d 0 1 =
        (original C v A).d 0 1 ≫ 𝟙 _
      rw [Category.comp_id, CochainHeadOne.Construction.CochainHeadCompletion.d_zero]
      change _ = ModuleCat.ofHom (((CochainHeadOne.Construction.CochainHeadCompletion.complex C v).d 0 1).hom.lTensor A)
      rw [CochainHeadOne.Construction.CochainHeadCompletion.d_zero]
      exact ModuleCat.hom_ext (CompletionTensor.Construction.CompletionTensorKernel.projection_comp (C.d 0 1).hom v A h)
    · change 𝟙 _ ≫ (replaced C v A).d 1 2 = (original C v A).d 1 2 ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id, CochainHeadOne.Construction.CochainHeadCompletion.d_one]
      change _ = ModuleCat.ofHom (((CochainHeadOne.Construction.CochainHeadCompletion.complex C v).d 1 2).hom.lTensor A)
      rw [CochainHeadOne.Construction.CochainHeadCompletion.d_one]
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      ext a x
      rfl
    · change 𝟙 _ ≫ (replaced C v A).d (n + 2) (n + 3) =
        (original C v A).d (n + 2) (n + 3) ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id, CochainHeadOne.Construction.CochainHeadCompletion.d_succ_succ]
      change _ = ModuleCat.ofHom
        (((CochainHeadOne.Construction.CochainHeadCompletion.complex C v).d (n + 2) (n + 3)).hom.lTensor A)
      rw [CochainHeadOne.Construction.CochainHeadCompletion.d_succ_succ]
      rfl)

theorem comparison :
    ModuleTensor.Construction.ModuleTensorFunctor.map A (CochainHeadOne.Construction.CochainHeadCompletion.comparison C v) =
      (iso C v A h).hom ≫
        CochainHeadOne.Construction.CochainHeadCompletion.comparison (ModuleTensor.Construction.ModuleTensorFunctor.complex A C) (v.lTensor A) := by
  ext n : 1
  rcases n with _ | _ | n
  · apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext a x
    change a ⊗ₜ[R] (-x.val.1) =
      -(CompletionTensor.Construction.CompletionTensorKernel.completionIso (C.d 0 1).hom v A h (a ⊗ₜ[R] x)).val.1
    rw [CompletionTensor.Construction.CompletionTensorKernel.completionIso_tmul, TensorProduct.tmul_neg]
  · apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext a x
    rfl
  · apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext a x
    rfl

include h in
theorem quasiIso : QuasiIso (ModuleTensor.Construction.ModuleTensorFunctor.map A (CochainHeadOne.Construction.CochainHeadCompletion.comparison C v)) := by
  have : QuasiIso
      (CochainHeadOne.Construction.CochainHeadCompletion.comparison (ModuleTensor.Construction.ModuleTensorFunctor.complex A C) (v.lTensor A)) :=
    CochainHeadOne.Construction.CochainHeadCompletion.quasiIso _ _
      (CompletionTensor.Construction.CompletionTensorKernel.tensor_surjective (C.d 0 1).hom v A h)
  rw [comparison C v A h]
  infer_instance

end Construction.CochainCompletionTensor

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CochainCompletion
