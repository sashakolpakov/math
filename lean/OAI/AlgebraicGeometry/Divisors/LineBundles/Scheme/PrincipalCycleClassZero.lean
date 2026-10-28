import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.NormalizedGradedPush
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GradedOpenClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.Ambient

/-! # Principal Cycle Class Zero -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.PrincipalCycleClassZero.BundleCycles

noncomputable section

/-! Every full principal divisor on an arbitrary integral closed support
has zero canonical ambient cycle class, including singular supports in
nonprojective smooth separated complex schemes. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom] [IsSeparated X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]

theorem schemeGradedCycleClass_support_principal_zero
    (d p : ℕ) (hp : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (W : IrreducibleCloseds X.left) (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.hom = d + 1)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass X d p hp (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor X.hom d W g) = 0 := by
  let i := CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (SchemeNormalization.AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)
  let r := Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) i
  let : IsIso r := SchemeNormalization.Ambient.BundleCycles.schemeNormalizationAmbientBetti_isIso X W d p hW hp
  have hclass := LinearMap.congr_fun (GradedOpenClass.BundleCycles.schemeGradedCycleClass_openRestriction i d p hp)
    (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor X.hom d W g)
  have hcycle := NormalizedGradedPush.BundleCycles.schemePrincipal_open_eq_normalizedPush X W d hW g hg
  have hz := NormalizedGradedPush.BundleCycles.schemeNormalizedGradedPush_class_zero X W d hW g hg p hp
  have hr : r (GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass X d p hp (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor X.hom d W g)) = 0 := by
    exact hclass.symm.trans
      ((congrArg (GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass (SchemeNormalization.Ambient.BundleCycles.schemeNormalizationAmbientOver X W) d p
        (hp.trans (SchemeNormalization.Ambient.BundleCycles.schemeNormalizationAmbient_dimension X W).symm)) hcycle).trans hz)
  have he := congrArg (inv r) hr
  exact (Iso.hom_inv_id_apply (asIso r) _).symm.trans (he.trans (map_zero _))

theorem schemeGradedCycleClass_kills_relations
    (d p : ℕ) (hp : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom) :
    DimensionChow.BundleCycles.dimensionRationalEquivalenceQ X.hom d ≤ LinearMap.ker (GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass X d p hp) := by
  apply Submodule.span_le.mpr
  rintro a ⟨W, hW, g, hg, rfl⟩
  exact schemeGradedCycleClass_support_principal_zero X d p hp W hW g hg

def schemeDimensionChowCycleClass
    (d p : ℕ) (hp : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom) :
    DimensionChow.BundleCycles.DimensionChowQ X.hom d →ₗ[ℚ] Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X (p + p) :=
  (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ X.hom d).liftQ (GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass X d p hp)
    (schemeGradedCycleClass_kills_relations X d p hp)

theorem schemeDimensionChowCycleClass_cycle
    (d p : ℕ) (hp : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (a : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ) :
    schemeDimensionChowCycleClass X d p hp (DimensionChow.BundleCycles.dimensionCycleToChowQ X.hom d a) =
      GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass X d p hp a := rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.PrincipalCycleClassZero.BundleCycles
