import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.BaseChangeComplex
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.Localization.BaseChange

/-! # Localization Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.LocalizationExactness

noncomputable section

/-! Exactness of a module short complex is detected by its explicit
tensor-product localizations at maximal ideals. -/
open _root_.CategoryTheory
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R]

theorem tensorLocalizationMap_eq {M N : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (I : Ideal R) [I.IsPrime] (f : M →ₗ[R] N) :
    IsLocalizedModule.map I.primeCompl
      (TensorProduct.mk R (Localization.AtPrime I) M 1)
      (TensorProduct.mk R (Localization.AtPrime I) N 1) f =
        (f.baseChange (Localization.AtPrime I)).restrictScalars R := by
  apply IsLocalizedModule.linearMap_ext I.primeCompl
    (TensorProduct.mk R (Localization.AtPrime I) M 1)
    (TensorProduct.mk R (Localization.AtPrime I) N 1)
  ext x
  exact (IsLocalizedModule.map_apply I.primeCompl
    (TensorProduct.mk R (Localization.AtPrime I) M 1)
    (TensorProduct.mk R (Localization.AtPrime I) N 1) f x).trans rfl

theorem shortComplex_exact_of_tensor_localizations (C : ShortComplex (ModuleCat.{u} R))
    (h : ∀ (I : Ideal R) [I.IsMaximal],
      (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R (Localization.AtPrime I) C).Exact) : C.Exact := by
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact C).mpr
  apply exact_of_isLocalized_maximal
    (fun (I : Ideal R) (_ : I.IsMaximal) => Localization.AtPrime I ⊗[R] C.X₁)
    (fun (I : Ideal R) (_ : I.IsMaximal) => TensorProduct.mk R (Localization.AtPrime I) C.X₁ 1)
    (fun (I : Ideal R) (_ : I.IsMaximal) => Localization.AtPrime I ⊗[R] C.X₂)
    (fun (I : Ideal R) (_ : I.IsMaximal) => TensorProduct.mk R (Localization.AtPrime I) C.X₂ 1)
    (fun (I : Ideal R) (_ : I.IsMaximal) => Localization.AtPrime I ⊗[R] C.X₃)
    (fun (I : Ideal R) (_ : I.IsMaximal) => TensorProduct.mk R (Localization.AtPrime I) C.X₃ 1)
    C.f.hom C.g.hom
  intro I _
  rw [tensorLocalizationMap_eq, tensorLocalizationMap_eq]
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (h I)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.LocalizationExactness
