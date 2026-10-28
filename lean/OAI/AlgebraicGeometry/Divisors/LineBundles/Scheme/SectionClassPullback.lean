import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GlobalSectionClassRestriction

/-! # Section Class Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SectionClassPullback.BundleCycles

noncomputable section

/-! The class of an actual global section pulls back along every scheme morphism by the evaluation square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (i : X ⟶ Y) (s : Γ(Y.left, ⊤))

theorem schemeSectionZeroImage_pullback :
    Set.range (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage X (i.left.appTop s)) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' Set.range (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s) := by
  rw [CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_range, CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_range]
  ext x
  exact (congrArg (fun t : ℂ => t = 0)
    (DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation_map i x s)).symm.to_iff

theorem schemeSectionClass_mapsTo : Set.MapsTo (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map i)
    (Set.range (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage X (i.left.appTop s)))ᶜ
    (Set.range (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s))ᶜ := by
  intro x hx hy
  exact hx ((Set.ext_iff.mp (schemeSectionZeroImage_pullback i s) x).mpr hy)

theorem schemeSectionEquation_square :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map i ≫ CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation Y s = CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation X (i.left.appTop s) := by
  ext x a
  exact DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation_map i x s

theorem schemeSectionSupportedClass_pullback :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map i)
      (schemeSectionClass_mapsTo i s) 2 (Finite.GlobalSectionClassRestriction.BundleCycles.schemeSectionSupportedClass Y s) =
    Finite.GlobalSectionClassRestriction.BundleCycles.schemeSectionSupportedClass X (i.left.appTop s) := by
  have h := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map i) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation Y s)
    (schemeSectionClass_mapsTo i s) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation_mapsTo Y s) 2
  have he := CycleClass.Thom.ThomOpenRestriction.Constructions.pairMap_congr
    (schemeSectionEquation_square i s)
    ((CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation_mapsTo Y s).comp (schemeSectionClass_mapsTo i s))
    (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation_mapsTo X (i.left.appTop s)) 2
  exact ConcreteCategory.congr_hom (h.trans he)
    (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SectionClassPullback.BundleCycles
