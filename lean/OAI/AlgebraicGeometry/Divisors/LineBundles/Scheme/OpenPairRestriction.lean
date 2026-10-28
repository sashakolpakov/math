import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.Ambient
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ClosedClassPullbackGenerator

/-! # Open Pair Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.OpenPairRestriction.BundleCycles

noncomputable section

/-! Scheme open pullback is the analytic supported restriction followed by the actual open-point homeomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : X.left.Opens) (F : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (n : ℕ)

def schemeOpenPairCohomologyIso :=
  AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity.relativePairHomeomorphCohomologyIso (ModuleCat.of ℚ ℚ)
    (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver X U)))
    (Y := TopCat.of (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen X U)) (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemePointHomeomorph X U)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X U) ⁻¹' F)ᶜ
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) Fᶜ (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen X U))
    (fun _ => Iff.rfl) n

theorem schemeOpenPairPullback_factor :
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      Fᶜ (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen X U) n ≫ (schemeOpenPairCohomologyIso X U F n).hom =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X U)) (fun _ hx => hx) n := by
  let e := TopCat.isoOfHomeo (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver X U)))
    (Y := TopCat.of (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen X U)) (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemePointHomeomorph X U)
  let j := CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen X U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
  have he : e.hom ≫ j = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X U) := by ext x; rfl
  have hc := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) e.hom j
    (show Set.MapsTo e.hom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X U) ⁻¹' F)ᶜ
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) Fᶜ (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen X U)) from fun _ hx => hx)
    (show Set.MapsTo j (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) Fᶜ (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen X U)) Fᶜ from fun _ hx => hx) n
  exact hc.trans (CycleClass.Thom.ThomOpenRestriction.Constructions.pairMap_congr he (fun _ hx => hx) (fun _ hx => hx) n)

theorem schemeOpenPairPullback_injective_of_analytic
    (h : Function.Injective (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ)
      (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) Fᶜ (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen X U) n)) :
    Function.Injective (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X U))
      (show Set.MapsTo (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X U))
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X U) ⁻¹' F)ᶜ Fᶜ from fun _ hx => hx) n) := by
  intro a b hab
  apply h
  apply (ModuleCat.mono_iff_injective (schemeOpenPairCohomologyIso X U F n).hom).mp inferInstance
  exact (ConcreteCategory.congr_hom (schemeOpenPairPullback_factor X U F n) a).trans
    (hab.trans (ConcreteCategory.congr_hom (schemeOpenPairPullback_factor X U F n) b).symm)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.OpenPairRestriction.BundleCycles
