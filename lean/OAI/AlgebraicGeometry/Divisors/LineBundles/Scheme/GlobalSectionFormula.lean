import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.SectionDetection
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SectionPrincipalRestriction

/-! # Global Section Formula -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GlobalSectionFormula.BundleCycles

noncomputable section

/-! The supported cup of the canonical class of any integral support with a nonzero regular section is the canonical class of its full principal divisor. The normalization and all exceptional-set comparisons are constructed in the proof. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (W : IrreducibleCloseds X.left) (s : Γ(X.left, ⊤))

local instance globalSectionFormulaSupportTop : Nonempty (⊤ : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).Opens) :=
  ⟨⟨genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W), Opens.mem_top _⟩⟩

theorem schemeSupportSectionCup_eq_principalSupportedClass
    (p : ℕ) (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (n : ℕ) (hn : n + (p + 1) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (hs : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).germToFunctionField ⊤ ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop s) ≠ 0) :
    SupportSectionCup.BundleCycles.schemeSupportSectionCup X W s p hp = SectionPrincipalRestriction.BundleCycles.schemeSectionPrincipalSupportedClass X W s n p hn := by
  apply SchemeNormalization.SectionDetection.BundleCycles.schemeNormalizationSectionPullback_injective X W s hs p hp
  exact (SupportSectionCup.BundleCycles.schemeSupportSectionCup_normalization X W s p hp).trans
    ((SchemeNormalization.SectionFormula.BundleCycles.schemeNormalization_sectionCup_eq_originalPrincipalClass X W s p hp n hn hs).trans
      (SectionPrincipalRestriction.BundleCycles.schemeSectionPrincipalSupportedClass_normalization X W s n p hn).symm)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GlobalSectionFormula.BundleCycles
