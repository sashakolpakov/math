import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Isomorphism

/-! # Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Refinement

noncomputable section

/-!
# IntegralComparison: principal refinement inside a cartesian crystalline open

The localized square is also a pullback of ambient schemes. If the
principal open of the target lies in the image of a cartesian crystalline
open immersion, its localized crystalline morphism is an isomorphism.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Localization
open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LocalizationMaps OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CartesianMaps

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
variable {U V : BigCrystallineSite.Object p B J δ f} (α : U ⟶ V) (r : V.ring)

lemma ambient_pullback :
    IsPullback (BigCrystallineSite.Object.ambient.map (Crystalline.LocalizationMaps.localizedHom α r)) (BigCrystallineSite.Object.ambient.map (Crystalline.Localization.hom U (α.ringMap r)))
      (BigCrystallineSite.Object.ambient.map (Crystalline.Localization.hom V r)) (BigCrystallineSite.Object.ambient.map α) := by
  have : IsLocalization ((Submonoid.powers r).map α.ringMap.toRingHom) (Crystalline.Localization.Ring U (α.ringMap r)) := by
    rw [Submonoid.map_powers]
    infer_instance
  exact (CommRingCat.isPushout_of_isLocalization α.ringMap.toRingHom (Crystalline.LocalizationMaps.ringMap α r)
    (Crystalline.LocalizationMaps.ringMap_comp α r) (Submonoid.powers r)).op.map Scheme.Spec

lemma open_pullback_isIso {P T S Z : Scheme.{u}} {a : P ⟶ T} {b : P ⟶ S}
    {c : T ⟶ Z} {d : S ⟶ Z} [IsOpenImmersion d] (h : IsPullback a b c d)
    (hr : Set.range c ⊆ Set.range d) : IsIso a := by
  have : IsOpenImmersion a := MorphismProperty.of_isPullback h.flip inferInstance
  have ha : Function.Surjective a := by
    intro t
    obtain ⟨s, hs⟩ := hr ⟨t, rfl⟩
    obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback h t s hs.symm
    exact ⟨z, hz⟩
  have : Epi a.base := (TopCat.epi_iff_surjective a.base).mpr ha
  exact IsOpenImmersion.isIso a

lemma localized_isIso [IsOpenImmersion (BigCrystallineSite.Object.ambient.map α)] (hα : BigCrystallineSite.Object.Cartesian α)
    (hr : (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum V.ring)) ⊆ Set.range (BigCrystallineSite.Object.ambient.map α)) :
    IsIso (Crystalline.LocalizationMaps.localizedHom α r) := by
  have hsub : Set.range (BigCrystallineSite.Object.ambient.map (Crystalline.Localization.hom V r)) ⊆ Set.range (BigCrystallineSite.Object.ambient.map α) := by
    intro x hx
    have hx' : x ∈ (BigCrystallineSite.Object.ambient.map (Crystalline.Localization.hom V r)).opensRange := hx
    rw [Crystalline.Localization.hom_range] at hx'
    exact hr hx'
  have : IsIso (BigCrystallineSite.Object.ambient.map (Crystalline.LocalizationMaps.localizedHom α r)) :=
    open_pullback_isIso (ambient_pullback α r) hsub
  exact Crystalline.Isomorphism.isIso_of_cartesian (Crystalline.LocalizationMaps.localizedHom α r)
    (Crystalline.CartesianMaps.localizedHom_cartesian α hα r)

def factor [IsOpenImmersion (BigCrystallineSite.Object.ambient.map α)] (hα : BigCrystallineSite.Object.Cartesian α)
    (hr : (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum V.ring)) ⊆ Set.range (BigCrystallineSite.Object.ambient.map α)) :
    Crystalline.Localization.object V r ⟶ U := by
  have : IsIso (Crystalline.LocalizationMaps.localizedHom α r) := localized_isIso α r hα hr
  exact inv (Crystalline.LocalizationMaps.localizedHom α r) ≫ Crystalline.Localization.hom U (α.ringMap r)

lemma factor_comp [IsOpenImmersion (BigCrystallineSite.Object.ambient.map α)] (hα : BigCrystallineSite.Object.Cartesian α)
    (hr : (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum V.ring)) ⊆ Set.range (BigCrystallineSite.Object.ambient.map α)) :
    factor α r hα hr ≫ α = Crystalline.Localization.hom V r := by
  have : IsIso (Crystalline.LocalizationMaps.localizedHom α r) := localized_isIso α r hα hr
  change (inv (Crystalline.LocalizationMaps.localizedHom α r) ≫ Crystalline.Localization.hom U (α.ringMap r)) ≫ α = Crystalline.Localization.hom V r
  rw [Category.assoc, ← Crystalline.LocalizationMaps.localizedHom_square, IsIso.inv_hom_id_assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Refinement
