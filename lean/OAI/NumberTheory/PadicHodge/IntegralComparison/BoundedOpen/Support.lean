import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionPresheaf

/-! # Support -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Support

noncomputable section

/-!
# IntegralComparison: the geometric support condition for actual bounded crystalline objects
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionPresheaf

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (T : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n)

theorem property_iff_range_subset (V : Y.Opens) :
    SectionPresheaf.property fY n V T ↔ Set.range T.obj.mapToX ⊆ (V : Set Y) := by
  constructor
  · rintro ⟨t, ht⟩ z ⟨w, rfl⟩
    have hz : T.obj.mapToX w ∈ Set.range V.ι := ⟨t w, congrArg (fun m => m w) ht⟩
    rwa [Scheme.Opens.range_ι] at hz
  · intro h
    have h' : Set.range T.obj.mapToX ⊆ Set.range V.ι := by
      rwa [Scheme.Opens.range_ι]
    exact ⟨IsOpenImmersion.lift V.ι T.obj.mapToX h', IsOpenImmersion.lift_fac V.ι T.obj.mapToX h'⟩

theorem property_top : SectionPresheaf.property fY n ⊤ T :=
  (property_iff_range_subset fY n T ⊤).mpr (Set.subset_univ _)

theorem property_inf (U V : Y.Opens) : SectionPresheaf.property fY n (U ⊓ V) T ↔
    SectionPresheaf.property fY n U T ∧ SectionPresheaf.property fY n V T := by
  rw [property_iff_range_subset, property_iff_range_subset, property_iff_range_subset]
  exact Set.subset_inter_iff

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Support
