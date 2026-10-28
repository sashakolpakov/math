import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GlobalSectionFormula
import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.SectionGerm
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.OpenSupportedCycle

/-! # Section Formula -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.SectionFormula.BundleCycles

noncomputable section

/-! Applying the constructed global finite section formula to the actual smooth normalization identifies its supported section cup with the original principal cycle restricted to the normalization ambient open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (W : IrreducibleCloseds X.left) (s : Γ(X.left, ⊤))

local instance normalizationSectionFormulaSupportTop : Nonempty (⊤ : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).Opens) :=
  ⟨⟨genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W), Opens.mem_top _⟩⟩

def schemeNormalizationSectionSupport : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Ambient.BundleCycles.schemeNormalizationAmbientOver X W)) :=
  Finite.RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport (AmbientMap.BundleCycles.schemeSmoothNormalizationToAmbient X W)
    ((CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)).left.appTop s)

variable (p : ℕ) (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
  (n : ℕ) (hn : n + (p + 1) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
  (hs : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).germToFunctionField ⊤ ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop s) ≠ 0)

include hs in
theorem schemeNormalization_sectionCup_eq_originalPrincipalClass :
    Finite.GlobalSectionClassRestriction.BundleCycles.finiteGlobalSectionCup (AmbientMap.BundleCycles.schemeSmoothNormalizationToAmbient X W)
      ((CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)).left.appTop s)
      p (FiniteParent.BundleCycles.schemeSmoothNormalization_nativeCodimension X W p hp) =
    Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap (Ambient.BundleCycles.schemeNormalizationAmbientOver X W) (schemeNormalizationSectionSupport X W s)
      n (p + 1) (hn.trans (Ambient.BundleCycles.schemeNormalizationAmbient_dimension X W).symm)
      (Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRestrictCycle (Ambient.BundleCycles.schemeNormalizationAmbientOver X W) (schemeNormalizationSectionSupport X W s) n
        (Open.GradedOverRestriction.BundleCycles.openOverGradedRestriction (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)) n
          (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor X.hom n W
            ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).germToFunctionField ⊤ ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop s))))) := by
  let k := AmbientMap.BundleCycles.schemeSmoothNormalizationToAmbient X W
  let t := (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)).left.appTop s
  let hcod := FiniteParent.BundleCycles.schemeSmoothNormalization_nativeCodimension X W p hp
  let hdim := hn.trans (Ambient.BundleCycles.schemeNormalizationAmbient_dimension X W).symm
  have hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.hom = n + 1 := by omega
  have hcycle := (Finite.RegularSupportedCycle.BundleCycles.finiteRegularSupportedCycle_forget k t p hcod n hdim).trans
    (SectionGerm.BundleCycles.schemePrincipal_open_eq_normalizedRestrictedSectionPush X W s n hW hs).symm
  have h := Finite.GlobalSectionFormula.BundleCycles.finiteGlobalSectionCup_eq_principalSupportedClass k t p hcod n hdim
    (SectionGerm.BundleCycles.schemeNormalizedSection_ne_zero X W s hs)
  exact h.trans (Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap_eq_of_forget_eq (Ambient.BundleCycles.schemeNormalizationAmbientOver X W)
    (schemeNormalizationSectionSupport X W s) n (p + 1) hdim
    (Finite.RegularSupportedCycle.BundleCycles.finiteRegularSupportedCycle k t p hcod n hdim) _ hcycle)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.SectionFormula.BundleCycles
