import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.OpenPairRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ClosedClassOpenPullback

/-! # Open Pair Support -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.OpenPairSupport.BundleCycles

noncomputable section

/-! The open pair comparison accepts any proved description of the actual inverse-image support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (i : X ⟶ Y)
  (F : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (G : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
  (hG : G = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' F)

include hG in
theorem schemeOpenPairSupport_mapsTo : Set.MapsTo (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map i) Gᶜ Fᶜ := by
  intro x hx hy
  exact hx ((Set.ext_iff.mp hG x).mpr hy)

theorem schemeOpenPairPullback_injective_of_analytic_support
    (Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : Y.left.Opens) (F : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
    (G : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver Y U)))
    (hG : G = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion Y U) ⁻¹' F) (n : ℕ)
    (h : Function.Injective (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ)
      (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) Fᶜ (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen Y U) n)) :
    Function.Injective (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion Y U))
      (schemeOpenPairSupport_mapsTo (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion Y U) F G hG) n) := by
  subst G
  exact OpenPairRestriction.BundleCycles.schemeOpenPairPullback_injective_of_analytic Y U F n h

variable [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  [IsIntegral Y.left] [Smooth Y.hom]
  [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] [IsOpenImmersion i.left]
  (d p : ℕ) (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom)

theorem schemeClosedRestrictedClass_openPullback_of_support (c : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint Y.hom d →₀ ℚ)
    (hc : ∀ z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint Y.hom d, c z ≠ 0 →
      Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y (irreducibleSetEquivPoints.symm z.val)) ⊆ F) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map i)
      (schemeOpenPairSupport_mapsTo i F G hG) (2 * p)
      (OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap Y F d p hd (OpenSupportedCycle.BundleCycles.schemeClosedRestrictCycle Y F d c)) =
    OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap X G d p (GradedOpenClass.BundleCycles.openOverGraded_codimension i d p hd)
      (OpenSupportedCycle.BundleCycles.schemeClosedRestrictCycle X G d (Open.GradedOverRestriction.BundleCycles.openOverGradedRestriction i d c)) := by
  subst G
  exact ClosedClassOpenPullback.BundleCycles.schemeClosedRestrictedClass_openPullback i F d p hd c hc

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.OpenPairSupport.BundleCycles
