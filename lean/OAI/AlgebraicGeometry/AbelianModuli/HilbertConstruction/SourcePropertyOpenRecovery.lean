import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.SourcePropertyBaseOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FactoredBaseRecovery

/-! # Source Property Open Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SourcePropertyOpenRecovery

noncomputable section

/-! An arbitrary test map landing in an open base where a base-change-stable property holds inherits that property on the actual Cartesian family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]

theorem property_pullback_of_restriction {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens)
    (hP : P (f ∣_ U)) : P (pullback.snd f U.ι) := by
  let h := (isPullback_morphismRestrict f U).flip
  have hpb : IsPullback h.isoPullback.inv (pullback.snd f U.ι) (f ∣_ U) (𝟙 U.toScheme) :=
    IsPullback.of_horiz_isIso ⟨h.isoPullback_inv_snd.trans (Category.comp_id _).symm⟩
  exact MorphismProperty.of_isPullback (P := P) hpb hP

theorem property_recovery_of_range_subset_open
    {X Y S T : Scheme.{u}} (q : Y ⟶ X) (p : Y ⟶ T) (f : X ⟶ S) (c : T ⟶ S)
    (h : IsPullback q p f c) (U : S.Opens) (hP : P (f ∣_ U)) (hc : Set.range c ⊆ U) : P p := by
  let a : T ⟶ U.toScheme := IsOpenImmersion.lift U.ι c (by simpa only [Scheme.Opens.range_ι] using hc)
  have ha : a ≫ U.ι = c := IsOpenImmersion.lift_fac _ _ _
  have H : IsPullback q p f (a ≫ U.ι) := by
    rw [ha]
    exact h
  exact MorphismProperty.of_isPullback (P := P) (FactoredBaseRecovery.factoredBaseRecovery_isPullback q p f a U.ι H)
    (property_pullback_of_restriction P f U hP)

theorem property_pullback_of_range_subset_properBaseOpen [IsZariskiLocalAtSource P]
    {X S T : Scheme.{u}} (f : X ⟶ S) [IsProper f] (c : T ⟶ S)
    (hc : Set.range c ⊆ Proper.SourcePropertyBaseOpen.properSourcePropertyBaseOpen P f) : P (pullback.snd f c) :=
  property_recovery_of_range_subset_open P _ _ f c (IsPullback.of_hasPullback f c)
    (Proper.SourcePropertyBaseOpen.properSourcePropertyBaseOpen P f) (Proper.SourcePropertyBaseOpen.properSourcePropertyBaseOpen_restrict P f) hc

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SourcePropertyOpenRecovery
