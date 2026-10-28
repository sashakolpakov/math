import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Localization Tensor Equiv -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LocalizationTensorEquiv

noncomputable section

/-! Tensor coordinates identify a localized module and its subsequent
coefficient fibers with the original tensor module, naturally in maps. -/

open scoped TensorProduct

variable {R : Type} [CommRing R] (S : Submonoid R)

def localizationTensorEquiv (M : Type) [AddCommGroup M] [Module R M] :
    Localization S ⊗[R] M ≃ₗ[Localization S] LocalizedModule S M :=
  (LocalizedModule.isBaseChange S M).equiv

theorem localizationTensorEquiv_tmul {M : Type} [AddCommGroup M] [Module R M]
    (a : Localization S) (m : M) :
    localizationTensorEquiv S M (a ⊗ₜ[R] m) = a • LocalizedModule.mkLinearMap S M m :=
  (LocalizedModule.isBaseChange S M).equiv_tmul a m

variable (B : Type) [CommRing B] [Algebra R B] [Algebra (Localization S) B]
  [IsScalarTower R (Localization S) B]

def localizationCoefficientEquiv (M : Type) [AddCommGroup M] [Module R M] :
    B ⊗[R] M ≃ₗ[B] B ⊗[Localization S] LocalizedModule S M :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization S) B B M).symm.trans
    (LinearEquiv.baseChange (Localization S) B _ _ (localizationTensorEquiv S M))

theorem localizationCoefficientEquiv_tmul {M : Type} [AddCommGroup M] [Module R M]
    (b : B) (m : M) :
    localizationCoefficientEquiv S B M (b ⊗ₜ[R] m) =
      b ⊗ₜ[Localization S] LocalizedModule.mkLinearMap S M m := by
  rw [localizationCoefficientEquiv, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    LinearEquiv.baseChange_tmul, localizationTensorEquiv_tmul, one_smul]

theorem localizationCoefficientEquiv_natural
    {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    (localizationCoefficientEquiv S B N).toLinearMap.comp (f.baseChange B) =
      ((LocalizedModule.map S f).baseChange B).comp
        (localizationCoefficientEquiv S B M).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro b m
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul,
    localizationCoefficientEquiv_tmul, LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk]

theorem localization_tensor_injective
    {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Injective (f.lTensor B)) :
    Function.Injective ((LocalizedModule.map S f).lTensor B) := by
  let eM := localizationCoefficientEquiv S B M
  let eN := localizationCoefficientEquiv S B N
  intro x y hxy
  obtain ⟨x, rfl⟩ := eM.surjective x
  obtain ⟨y, rfl⟩ := eM.surjective y
  have hx := LinearMap.congr_fun (localizationCoefficientEquiv_natural S B f) x
  have hy := LinearMap.congr_fun (localizationCoefficientEquiv_natural S B f) y
  exact congrArg eM (hf (eN.injective (hx.trans (hxy.trans hy.symm))))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LocalizationTensorEquiv
