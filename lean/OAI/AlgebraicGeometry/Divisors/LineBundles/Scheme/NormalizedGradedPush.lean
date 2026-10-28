import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.Ambient
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.NormalizedPrincipalCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GradedClassZero
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GradedPrincipalClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.GradedOverRestriction

/-! # Normalized Graded Push -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.NormalizedGradedPush.BundleCycles

noncomputable section

/-! On the actual ambient complement, the full principal cycle is
exactly the finite pushforward from the smooth normalization, and its
canonical graded cycle class vanishes. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

theorem pointRestriction_immersionPushforward {S T : Scheme} (i : S ⟶ T) [IsOpenImmersion i]
    (a : S →₀ ℚ) :
    Finsupp.comapDomain i (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward i a) i.isOpenEmbedding.injective.injOn = a := by
  rw [IsomorphismDivisorPushforward.BundleCycles.pointPushforward_eq_mapDomain_of_immersion]
  exact Finsupp.leftInverse_lcomapDomain_mapDomain (R := ℚ) i i.isOpenEmbedding.injective a

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    (W : IrreducibleCloseds X.left) (d : ℕ)
    (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.hom = d + 1)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0)

def schemeNormalizedGradedPrincipal : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).hom d →₀ ℚ :=
  Graded.RationalPointDivisor.BundleCycles.gradedRationalPointDivisor (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left
    (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).hom d (NormalizedFunction.BundleCycles.schemeNormalizedFunction X W g)

include hW in
omit [AlgebraicGeometry.IsIntegral X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeNormalizedGradedPrincipal_forget :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).hom d (schemeNormalizedGradedPrincipal X W d g) =
      RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left (NormalizedFunction.BundleCycles.schemeNormalizedFunction X W g) :=
  Graded.RationalPointDivisor.BundleCycles.gradedRationalPointDivisor_push (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left
    (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).hom d ((SchemeNormalization.Topology.BundleCycles.schemeSmoothNormalization_dimension X W).trans hW) _

include hW hg in
omit [AlgebraicGeometry.IsIntegral X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemePrincipal_open_eq_normalizedPush :
    Open.GradedOverRestriction.BundleCycles.openOverGradedRestriction (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (SchemeNormalization.AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)) d
      (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor X.hom d W g) =
    Finite.GradedOverPushforward.BundleCycles.finiteOverGradedPushforward (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationToAmbient X W) d (schemeNormalizedGradedPrincipal X W d g) := by
  let i := CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (SchemeNormalization.AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)
  let f := SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationToAmbient X W
  let a := RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left (NormalizedFunction.BundleCycles.schemeNormalizedFunction X W g)
  apply Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective (SchemeNormalization.Ambient.BundleCycles.schemeNormalizationAmbientOver X W).hom d
  rw [Open.GradedOverRestriction.BundleCycles.openOverGradedRestriction_forget, Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push X.hom d W hW,
    Finite.GradedOverPushforward.BundleCycles.finiteOverGradedPushforward_forget, schemeNormalizedGradedPrincipal_forget X W d hW g]
  have h := NormalizedPrincipalCycle.BundleCycles.schemeNormalizedPrincipal_pointPushforward X W g hg
  change IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward (f.left ≫ i.left) a = Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g at h
  rw [IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_comp, LinearMap.comp_apply] at h
  exact (congrArg (fun b => Finsupp.comapDomain i.left b i.left.isOpenEmbedding.injective.injOn) h.symm).trans
    (pointRestriction_immersionPushforward i.left (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f.left a))

include hW hg in
theorem schemeNormalizedGradedPush_class_zero [IsSeparated X.hom]
    (p : ℕ) (hp : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom) :
    GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass (SchemeNormalization.Ambient.BundleCycles.schemeNormalizationAmbientOver X W) d p
      (hp.trans (SchemeNormalization.Ambient.BundleCycles.schemeNormalizationAmbient_dimension X W).symm)
      (Finite.GradedOverPushforward.BundleCycles.finiteOverGradedPushforward (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationToAmbient X W) d (schemeNormalizedGradedPrincipal X W d g)) = 0 := by
  have hS : d + 1 = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).hom :=
    hW.symm.trans (SchemeNormalization.Topology.BundleCycles.schemeSmoothNormalization_dimension X W).symm
  apply Finite.GradedClassZero.BundleCycles.finiteOverGradedCycleClass_zero (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationToAmbient X W) d 1 p hS
    (hp.trans (SchemeNormalization.Ambient.BundleCycles.schemeNormalizationAmbient_dimension X W).symm)
  exact GradedPrincipalClass.BundleCycles.schemeGradedCycleClass_principal_zero (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W) d hS
    (NormalizedFunction.BundleCycles.schemeNormalizedUnitRepresentative X W g hg) (NormalizedFunction.BundleCycles.schemeNormalizedFunction_ne_zero X W g hg)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.NormalizedGradedPush.BundleCycles
