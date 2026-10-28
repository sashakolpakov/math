import OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.Global
import OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.CechIs
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologySections

/-! # Chern Restriction -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.ChernRestriction

noncomputable section

/-!
# ChernClass: actual local restrictions of the global relative Chern class

On each logarithmic chart, the genuine global relative Chern class restricts
to the supported winding of the same actual rational-section equation.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologySections.Cycles OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.CechIs.RationalCech

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicLineBundle

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X)
variable [IsIntegral X.carrier]

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
local notation "A" => (OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen : Set T)

/-- Taking the local component sends the full relative Chern cocycle to
the actual relative winding cocycle, including its closedness proof. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.relativeChernTotalCocycle_local (a : Fin 1 → L.LogCoverIndex) :
    AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (CechIs.RationalCech.relativeCechLocalProjection T A L.logCover a) 2 L.relativeChernTotalCocycle =
      SubspaceCechD.relativeWindingCocycle (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a))
        (L.analyticReferenceLocus (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a))
        (L.logIntersectionEquation a 0) (L.logIntersectionEquation_ne_zero a 0) :=
  Subtype.ext (L.relativeChernTotalCocycle_zeroColumn a)

/-- The constructed global class has exactly the actual section-equation winding on each chart. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.rationalSectionChernRelativeClass_local (a : Fin 1 → L.LogCoverIndex) :
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T A
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a) 2 L.rationalSectionChernRelativeClass =
    Supported.Winding.supportedWindingClass (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a))
      (L.analyticReferenceLocus (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a))
      (L.logIntersectionEquation a 0) (L.logIntersectionEquation_ne_zero a 0) := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f => HomologicalComplex.homologyMap f 2)
      (CechIs.RationalCech.relativeCechAugmentation_local T A L.logCover a)) L.rationalSectionChernRelativeClass
  rw [HomologicalComplex.homologyMap_comp] at h
  change HomologicalComplex.homologyMap (CechIs.RationalCech.relativeCechLocalProjection T A L.logCover a) 2
      ((CechIs.RationalCech.relativeCechCohomologyIso T A L.logCover L.logCover_covers 1).hom
        L.rationalSectionChernRelativeClass) =
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T A
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a) 2 L.rationalSectionChernRelativeClass at h
  rw [L.rationalSectionChernRelativeClass_cech, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality,
    L.relativeChernTotalCocycle_local, SubspaceCechD.relativeWindingCocycle_class] at h
  exact h.symm

end AlgebraicLineBundle

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.ChernRestriction
