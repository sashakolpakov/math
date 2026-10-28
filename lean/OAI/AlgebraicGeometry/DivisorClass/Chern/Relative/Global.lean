import OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.CechIs
import OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.Cocycle

/-! # Global -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.Global

noncomputable section

/-!
# ChernClass: the actual global relative Chern class of the rational section

The relative Cech comparison transports the constructed Chern cocycle back
to the ordinary relative singular cohomology of the original analytic space.
Forgetting support gives exactly the original `firstChernClassQ`.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.CechIs.RationalCech

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicLineBundle

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X)
variable [IsIntegral X.carrier]

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
local notation "A" => (OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen : Set T)

/-- A relative class in the original analytic space, built from the actual Chern cocycle. -/
def _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.rationalSectionChernRelativeClass : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T A 2 :=
  (CechIs.RationalCech.relativeCechCohomologyIso T A L.logCover L.logCover_covers 1).inv
    (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (CechSequence.RationalCech.relativeCechTotal T A L.logCover) 2 L.relativeChernTotalCocycle)

/-- The actual augmentation sends the global class to the constructed relative cocycle. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.rationalSectionChernRelativeClass_cech :
    (CechIs.RationalCech.relativeCechCohomologyIso T A L.logCover L.logCover_covers 1).hom
      L.rationalSectionChernRelativeClass =
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (CechSequence.RationalCech.relativeCechTotal T A L.logCover) 2 L.relativeChernTotalCocycle :=
  (CechIs.RationalCech.relativeCechCohomologyIso T A L.logCover L.logCover_covers 1).inv_hom_id_apply _

/-- Forgetting support gives precisely the actual first Chern class of the bundle. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.rationalSectionChernRelativeClass_absolute :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) T A 2 L.rationalSectionChernRelativeClass =
      First.firstChernClassQ X L := by
  have h := ConcreteCategory.congr_hom
    (CechIs.RationalCech.relativeCechCohomologyIso_inclusion T A L.logCover L.logCover_covers 1)
    L.rationalSectionChernRelativeClass
  change HomologicalComplex.homologyMap (CechSequence.RationalCech.relativeCechTotalInclusion T A L.logCover) 2
      ((CechIs.RationalCech.relativeCechCohomologyIso T A L.logCover L.logCover_covers 1).hom
        L.rationalSectionChernRelativeClass) =
    (Rational.CechComparison.RationalCech.singularCechCohomologyIso T L.logCover L.logCover_covers 2).hom
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) T A 2 L.rationalSectionChernRelativeClass) at h
  rw [L.rationalSectionChernRelativeClass_cech] at h
  have hi := congrArg (Rational.CechComparison.RationalCech.singularCechCohomologyIso T L.logCover L.logCover_covers 2).inv h.symm
  rw [Iso.hom_inv_id_apply] at hi
  exact hi.trans L.relativeChernTotalCocycle_firstChern

end AlgebraicLineBundle

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.Global
