import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.SmoothDimensionClassification
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.PropertyComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.FamilySmoothOpen

/-! # Family Dimension Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Smooth relative projective Hilbert families have an actual open base classifying precisely their fixed-dimension pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem Hilbert.FamilyDimensionOpen.smoothDimension_recovery_iff_range
    {X Y S T : Scheme.{u}} (q : Y ⟶ X) (p : Y ⟶ T) (f : X ⟶ S) (c : T ⟶ S)
    (h : IsPullback q p f c) [IsProper f] [Smooth f] (g : ℕ) :
    SmoothOfRelativeDimension g p ↔ Set.range c ⊆ Proper.SmoothDimensionOpen.properSmoothDimensionBaseOpen f g := by
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension g : MorphismProperty Scheme.{u}) :=
    smoothOfRelativeDimension_isStableUnderBaseChange g
  exact (Cartesian.PropertyComparison.property_cartesian_iff_pullback (@SmoothOfRelativeDimension g) q p f c h).trans
    (Proper.SmoothDimensionClassification.smoothDimension_pullback_iff_range_subset f g c)

variable {S : Scheme.{u}} {n : ℕ} {P : Polynomial ℚ} (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily S n P)
variable [Smooth F.family.scheme.hom] (g : ℕ)

def RelativeProjective.Families.RelativeProjectiveHilbertFamily.dimensionBaseOpen : S.Opens := by
  have : IsProper F.family.scheme.hom := F.family.proper
  exact Proper.SmoothDimensionOpen.properSmoothDimensionBaseOpen F.family.scheme.hom g

theorem RelativeProjective.Families.RelativeProjectiveHilbertFamily.pullback_dimension_iff_range {T : Scheme.{u}} (c : T ⟶ S) :
    SmoothOfRelativeDimension g (F.pullback c).family.scheme.hom ↔ Set.range c ⊆ F.dimensionBaseOpen g := by
  have : IsProper F.family.scheme.hom := F.family.proper
  exact Hilbert.FamilyDimensionOpen.smoothDimension_recovery_iff_range _ _ F.family.scheme.hom c
    (ClosedFamily.Transport.closedFamilyTransport_isPullback (RelativeProjective.BaseMaps.relativeProjectiveBaseMap c n) c
      (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback c n) F.family.ideal) g

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
