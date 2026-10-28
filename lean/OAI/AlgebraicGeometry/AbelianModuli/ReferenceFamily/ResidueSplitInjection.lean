import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.SplitInjection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LocalizationTensorEquiv
import Mathlib.RingTheory.LocalRing.Module

/-! # Residue Split Injection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ResidueSplitInjection

noncomputable section

/-! A map between finite projective modules has a global left inverse
when it is injective after tensoring with every maximal residue field. -/

theorem split_injective_of_residue_fields
    {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N)
    (H : ∀ (P : Ideal R) (_ : P.IsMaximal),
      Function.Injective (f.lTensor (IsLocalRing.ResidueField (Localization.AtPrime P)))) :
    ∃ g : N →ₗ[R] M, g.comp f = LinearMap.id := by
  let : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  let : Module.FinitePresentation R N := Module.finitePresentation_of_projective R N
  apply Local.SplitInjection.split_injective_of_localization_maximal f
  intro P hP
  let : Module.Free (Localization.AtPrime P) (LocalizedModule P.primeCompl N) :=
    Module.free_of_flat_of_isLocalRing
  apply (IsLocalRing.split_injective_iff_lTensor_residueField_injective
    (LocalizedModule.map P.primeCompl f)).mpr
  exact LocalizationTensorEquiv.localization_tensor_injective P.primeCompl
    (IsLocalRing.ResidueField (Localization.AtPrime P)) f (H P hP)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ResidueSplitInjection
