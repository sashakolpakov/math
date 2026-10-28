import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrincipalLocalizationNaturality

/-! # Natural Principal Map Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalPrincipalMapDescent

noncomputable section

/-! The actual localized maps become isomorphisms over common finite coefficients. -/

open TensorProduct

universe u v

variable {C R A B : Type u} [CommRing C] [CommRing R] [CommRing A] [CommRing B]
variable [Algebra C R] [Algebra C A] [Algebra C B]

theorem principalBaseChangeMap_bijective_iff (φ : A →ₐ[C] B) (a : A) :
    Function.Bijective (PrincipalLocalizationNaturality.principalBaseChangeMap (R := R) φ a) ↔
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R R)
        (IsLocalization.Away.mapₐ (Localization.Away a) (Localization.Away (φ a)) φ a)) := by
  let eA := HilbertConstruction.Flat.LocalizationModels.principalModelBaseChangeIso (C := C) R a
  let eB := HilbertConstruction.Flat.LocalizationModels.principalModelBaseChangeIso (C := C) R (φ a)
  have h := congrArg
    (fun f : R ⊗[C] Localization.Away a →ₐ[R] Localization.Away ((1 : R) ⊗ₜ[C] φ a) =>
      Function.Bijective f) (PrincipalLocalizationNaturality.principalModelBaseChangeIso_natural (R := R) φ a)
  change Function.Bijective (eB ∘ Algebra.TensorProduct.map (AlgHom.id R R)
      (IsLocalization.Away.mapₐ (Localization.Away a) (Localization.Away (φ a)) φ a)) =
    Function.Bijective (PrincipalLocalizationNaturality.principalBaseChangeMap (R := R) φ a ∘ eA) at h
  rw [Function.Bijective.of_comp_iff' eB.bijective,
    Function.Bijective.of_comp_iff _ eA.bijective] at h
  exact h.symm.to_iff

theorem exists_common_natural_principalMap_bijective
    [Algebra.FiniteType C A] [Algebra.FiniteType C B]
    [Module.Flat C A] [Module.Flat C B]
    (φ : A →ₐ[C] B) {ι : Type v} [Finite ι] (f : ι → A)
    (hφ : ∀ i, Function.Bijective (PrincipalLocalizationNaturality.principalBaseChangeMap (R := R) φ (f i)))
    (E : Subalgebra C R) (hE : E.FG) :
    ∃ D : Subalgebra C R, E ≤ D ∧ D.FG ∧
      ∀ i, Function.Bijective (PrincipalLocalizationNaturality.principalBaseChangeMap (R := D) φ (f i)) := by
  have (i : ι) : Module.Flat C (Localization.Away (f i)) := HilbertConstruction.Flat.LocalizationModels.localizationAway_flat_overBase (f i)
  have (i : ι) : Module.Flat C (Localization.Away (φ (f i))) :=
    HilbertConstruction.Flat.LocalizationModels.localizationAway_flat_overBase (φ (f i))
  have (i : ι) : Algebra.FiniteType C (Localization.Away (f i)) :=
    HilbertConstruction.Flat.LocalizationModels.localizationAway_finiteType_overBase (f i)
  have (i : ι) : Algebra.FiniteType C (Localization.Away (φ (f i))) :=
    HilbertConstruction.Flat.LocalizationModels.localizationAway_finiteType_overBase (φ (f i))
  obtain ⟨D, hED, hD, hd⟩ := NaturalTensorMapDescent.exists_common_natural_tensorMap_bijective
    (fun i => Localization.Away (f i)) (fun i => Localization.Away (φ (f i)))
    (fun i => IsLocalization.Away.mapₐ _ _ φ (f i))
    (fun i => (principalBaseChangeMap_bijective_iff φ (f i)).mp (hφ i)) E hE
  exact ⟨D, hED, hD, fun i => (principalBaseChangeMap_bijective_iff φ (f i)).mpr (hd i)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalPrincipalMapDescent
