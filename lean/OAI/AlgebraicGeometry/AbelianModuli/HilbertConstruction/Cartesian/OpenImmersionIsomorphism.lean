import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocalizationMapCartesian
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.OpenImmersionCriterion
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Open Immersion Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.OpenImmersionIsomorphism

noncomputable section

/-! A pullback of an open immersion over an open inside its image is an isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem isIso_of_cartesian_openImmersion_range
    {V U X Y : Scheme.{u}} (p : V ⟶ U) (a : V ⟶ X) (b : U ⟶ Y) (f : X ⟶ Y)
    (H : IsPullback p a b f) [IsOpenImmersion f]
    (h : Set.range b ⊆ Set.range f) : IsIso p := by
  have : IsOpenImmersion p := MorphismProperty.of_isPullback H.flip inferInstance
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top p
  apply TopologicalSpace.Opens.ext
  apply Set.ext
  intro y
  constructor
  · intro _
    trivial
  · intro _
    obtain ⟨x, hx⟩ := h ⟨y, rfl⟩
    obtain ⟨v, hv, _⟩ := Scheme.exists_preimage_of_isPullback H y x hx.symm
    exact ⟨v, hv⟩

theorem localizationMap_bijective_of_basicOpen_subset_range
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))] (a : A)
    (ha : (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) ⊆
      Set.range (PrimeSpectrum.comap φ)) :
    Function.Bijective (IsLocalization.Away.map
      (Localization.Away a) (Localization.Away (φ a)) φ a) := by
  have h : Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a)))) ⊆
      Set.range (Spec.map (CommRingCat.ofHom φ)) := by
    intro y hy
    apply ha
    exact (congrArg (fun S : Set (PrimeSpectrum A) => (y : PrimeSpectrum A) ∈ S)
      (PrimeSpectrum.localization_away_comap_range (Localization.Away a) a)).mp hy
  have := isIso_of_cartesian_openImmersion_range _ _ _ _ (LocalizationMapCartesian.localizationMap_isPullback φ a) h
  exact isIso_SpecMap_iff.mp this

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.OpenImmersionIsomorphism
