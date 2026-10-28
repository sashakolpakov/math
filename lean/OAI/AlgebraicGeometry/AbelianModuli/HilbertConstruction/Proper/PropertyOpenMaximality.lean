import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SourcePropertyOpenRecovery

/-! # Property Open Maximality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.PropertyOpenMaximality

noncomputable section

/-! The proper-base property open is the largest open base on which the restricted family has the property, when open target inclusions preserve it. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P]
variable [P.IsStableUnderBaseChange] [P.RespectsRight (@IsOpenImmersion : MorphismProperty Scheme.{u})]
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]

theorem properSourcePropertyBaseOpen_restrict_iff (U : S.Opens) :
    P (f ∣_ U) ↔ U ≤ SourcePropertyBaseOpen.properSourcePropertyBaseOpen P f := by
  constructor
  · intro hP
    have hp : P ((f ∣_ U) ≫ U.ι) :=
      MorphismProperty.RespectsRight.postcomp (Q := @IsOpenImmersion) U.ι inferInstance _ hP
    rw [morphismRestrict_ι] at hp
    have hsrc := (SourcePropertyOpenLocus.sourcePropertyOpenLocus_iff P f (f ⁻¹ᵁ U)).mp hp
    intro s hs hbad
    obtain ⟨x, hx, hxs⟩ := hbad
    apply hx
    apply hsrc
    change f x ∈ U
    rwa [hxs]
  · intro hU
    apply SourcePropertyOpenRecovery.property_recovery_of_range_subset_open P _ _ f U.ι
      (isPullback_morphismRestrict f U).flip (SourcePropertyBaseOpen.properSourcePropertyBaseOpen P f)
      (SourcePropertyBaseOpen.properSourcePropertyBaseOpen_restrict P f)
    rintro s ⟨s', rfl⟩
    exact hU s'.property

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.PropertyOpenMaximality
