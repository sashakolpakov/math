import OAI.AlgebraicGeometry.Cycle.ComponentSmoothSupportPurity

/-! # Component Smooth Iso Hom -/

namespace OAI.AlgebraicGeometry

noncomputable section

open _root_.AlgebraicGeometry

/-!
# Purity along the smooth locus of an integral cycle component

-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Topology _root_.TopologicalSpace Opposite

open OAI.AlgebraicTopology.Singular

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (x : X.left)
  {p : ℕ} (hx : Order.coheight x = p)

/-- Its forward map displays the open-section identification, canonical
sheafification comparison on the open, and exact open-restriction homology comparison. -/
@[simp] theorem ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportLowestSectionCohomologyIso_hom :
    (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportLowestSectionCohomologyIso X x hx).hom =
      HomologicalComplex.homologyMap
        (AlgebraicTopology.Sheaf.OpenRestrictedLowestCohomology.TopCat.openRestrictionTopSectionComplexIso (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
          (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x)
          (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x))).inv
        (2 * (p : ℤ)) ≫
      AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyToSheafSection
        (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x))
        (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothRestrictedInjectiveComplex X x) (2 * (p : ℤ)) ⊤ ≫
      (AlgebraicTopology.Sheaf.OpenRestrictedLowestCohomology.TopCat.openRestrictionHomologyTopSectionsIso (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
        (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x)
        (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentAnalyticClosedSupport X x))
        (2 * (p : ℤ))).hom := rfl

end

end OAI.AlgebraicGeometry
