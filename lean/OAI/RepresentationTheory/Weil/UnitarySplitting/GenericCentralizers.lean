import OAI.RepresentationTheory.Weil.UnitarySplitting.GenericCharacterCorrection
import OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyCentralizers

/-! # Generic Centralizers -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.GenericCentralizers.Construction

noncomputable section

/-! Generic extension preserves commutation with a fixed centralizer. -/

theorem genericExtension_commutes
    {G A : Type} [Group G] [Group A] (D : Set G) (f : G → A)
    (hD : ∀ s : Finset G, ∃ t : G, ∀ g ∈ s, g * t ∈ D)
    (hm : ∀ a ∈ D, ∀ b ∈ D, a * b ∈ D → f (a * b) = f a * f b)
    (b : A) (hb : ∀ g ∈ D, Commute (f g) b) (g : G) :
    Commute (GenericCharacterCorrection.Construction.genericExtension D f hD g) b := by
  obtain ⟨t, ht, hgt⟩ := GenericCharacterCorrection.Construction.generic_denominator D hD g
  rw [GenericCharacterCorrection.Construction.genericExtension_apply D f hD hm g t ht hgt]
  exact (hb (g * t) hgt).mul_left (hb t ht).inv_left

theorem characterCorrectedLift_commutes
    {G Z A : Type} [CommGroup Z] [Group A]
    (ι : Z →* A) (hcentral : ∀ z : Z, ∀ x : A, Commute (ι z) x)
    (ℓ : Z) (κ : G → Z) (a : G → A) (g : G) (b : A) (hab : Commute (a g) b) :
    Commute (GenericCharacterCorrection.Construction.characterCorrectedLift ι ℓ κ a g) b :=
  (hcentral _ b).mul_left hab

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.GenericCentralizers.Construction
