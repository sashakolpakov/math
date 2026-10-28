import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.LocalizationModels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalTensorMapDescent

/-! # Principal Localization Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrincipalLocalizationNaturality

noncomputable section

/-! Localization commutes with the natural base change of an algebra map. -/

open TensorProduct

universe u

variable {C R A B : Type u} [CommRing C] [CommRing R] [CommRing A] [CommRing B]
variable [Algebra C R] [Algebra C A] [Algebra C B]

def principalBaseChangeMap (φ : A →ₐ[C] B) (a : A) :
    Localization.Away ((1 : R) ⊗ₜ[C] a) →ₐ[R] Localization.Away ((1 : R) ⊗ₜ[C] φ a) := by
  have : IsLocalization.Away
      (Algebra.TensorProduct.map (AlgHom.id R R) φ ((1 : R) ⊗ₜ[C] a))
      (Localization.Away ((1 : R) ⊗ₜ[C] φ a)) := by
    simpa only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply] using
      (inferInstanceAs (IsLocalization.Away ((1 : R) ⊗ₜ[C] φ a)
        (Localization.Away ((1 : R) ⊗ₜ[C] φ a))))
  exact IsLocalization.Away.mapₐ _ _ (Algebra.TensorProduct.map (AlgHom.id R R) φ)
    ((1 : R) ⊗ₜ[C] a)

theorem principalBaseChangeMap_algebraMap (φ : A →ₐ[C] B) (a : A) (x : R ⊗[C] A) :
    principalBaseChangeMap (R := R) φ a (algebraMap _ _ x) =
      algebraMap _ _ (Algebra.TensorProduct.map (AlgHom.id R R) φ x) := by
  simp only [principalBaseChangeMap, IsLocalization.Away.mapₐ_apply,
    IsLocalization.Away.map, IsLocalization.map_eq]
  rfl

theorem principalModelBaseChangeIso_natural (φ : A →ₐ[C] B) (a : A) :
    (Flat.LocalizationModels.principalModelBaseChangeIso (C := C) R (φ a)).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id R R)
        (IsLocalization.Away.mapₐ (Localization.Away a) (Localization.Away (φ a)) φ a)) =
    (principalBaseChangeMap (R := R) φ a).comp
      (Flat.LocalizationModels.principalModelBaseChangeIso (C := C) R a).toAlgHom := by
  apply Algebra.TensorProduct.ext
  · ext
  · apply IsLocalization.algHom_ext (Submonoid.powers a)
    apply AlgHom.ext
    intro b
    change Flat.LocalizationModels.principalModelBaseChangeIso (C := C) R (φ a)
        ((1 : R) ⊗ₜ[C] IsLocalization.Away.mapₐ _ _ φ a
          (algebraMap A (Localization.Away a) b)) =
      principalBaseChangeMap (R := R) φ a
        (Flat.LocalizationModels.principalModelBaseChangeIso (C := C) R a
          ((1 : R) ⊗ₜ[C] algebraMap A (Localization.Away a) b))
    simp only [IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map, IsLocalization.map_eq,
      Flat.LocalizationModels.principalModelBaseChangeIso, IsLocalization.Away.tensorProductEquivTMulRight_tmul,
      principalBaseChangeMap_algebraMap, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrincipalLocalizationNaturality
