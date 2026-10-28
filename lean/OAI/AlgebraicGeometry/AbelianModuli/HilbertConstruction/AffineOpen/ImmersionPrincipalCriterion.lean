import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.OpenImmersionCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocalizationMapCartesian

/-! # Immersion Principal Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.ImmersionPrincipalCriterion

noncomputable section

/-! An affine map is an open immersion when principal preimages cover and each localized map is an isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem isOpenImmersion_SpecMap_of_principal_isomorphisms
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) {ι : Type v} (f : ι → A)
    (hcover : Ideal.span (Set.range (fun i => φ (f i))) = ⊤)
    (hiso : ∀ i, Function.Bijective (IsLocalization.Away.map
      (Localization.Away (f i)) (Localization.Away (φ (f i))) φ (f i))) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) := by
  let V (i : ι) := Spec (.of (Localization.Away (φ (f i))))
  let U (i : ι) := Spec (.of (Localization.Away (f i)))
  let a (i : ι) : V i ⟶ Spec (.of B) :=
    Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (φ (f i)))))
  let b (i : ι) : U i ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (f i))))
  let p (i : ι) : V i ⟶ U i := Spec.map (CommRingCat.ofHom (IsLocalization.Away.map
    (Localization.Away (f i)) (Localization.Away (φ (f i))) φ (f i)))
  have (i : ι) : IsOpenImmersion (a i) := IsOpenImmersion.of_isLocalization (φ (f i))
  have (i : ι) : IsOpenImmersion (b i) := IsOpenImmersion.of_isLocalization (f i)
  have (i : ι) : IsIso (p i) := by
    have : IsIso (CommRingCat.ofHom (IsLocalization.Away.map
        (Localization.Away (f i)) (Localization.Away (φ (f i))) φ (f i))) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr (hiso i)
    exact inferInstanceAs (IsIso (Spec.map (CommRingCat.ofHom (IsLocalization.Away.map
      (Localization.Away (f i)) (Localization.Away (φ (f i))) φ (f i)))))
  apply Cartesian.OpenImmersionCriterion.isOpenImmersion_of_cartesian_isomorphism_pieces (Spec.map (CommRingCat.ofHom φ)) V U a b p
    (fun i => (LocalizationMapCartesian.localizationMap_isPullback φ (f i)).flip)
  intro x
  have hx : x ∈ ⨆ i, PrimeSpectrum.basicOpen (φ (f i)) := by
    rw [PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr hcover]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  refine ⟨i, ?_⟩
  change x ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away (φ (f i)))))
  exact (congrArg (fun S : Set (PrimeSpectrum B) => (x : PrimeSpectrum B) ∈ S)
    (PrimeSpectrum.localization_away_comap_range
      (Localization.Away (φ (f i))) (φ (f i)))).mpr hi

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.ImmersionPrincipalCriterion
