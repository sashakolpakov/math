import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedSupportSections

/-! # Support Analytic Detection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportAnalyticDetection.BundleCycles

noncomputable section

/-! In the first possible degree of an actual closed algebraic support, analytic neighborhoods covering that support detect the global relative cohomology class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedSupportSections.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (F : Closeds X.left) (c : ℕ)
  (hc : ∀ Z : IrreducibleCloseds X.left, (Z : Set X.left) ⊆ F →
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + c ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
local notation "O" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions.analyticOpen X F.compl

include hc in
theorem closedSupportedClass_eq_of_analytic_neighborhoods
    (U : {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X // ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ F} → Opens T)
    (hU : ∀ z, z.val ∈ U z)
    (a b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (O : Set T) (2 * c))
    (hab : ∀ z, CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) (U z) (2 * c) a =
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) (U z) (2 * c) b) : a = b := by
  let S := ((CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) T O).homology (2 * c)).obj
  have hi : IsIso (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) T O (2 * c)) :=
    CycleClass.Geometric.ComplexThom.Cycles.relativeCohomologyGlobalSectionMap_isIso T O (2 * c)
      (fun y n hn => CycleClass.Thom.Scheme.ClosedSupportSections.Constructions.closedSupportedStalk_isZero X F c hc y n hn)
  apply (ModuleCat.mono_iff_injective
    (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) T O (2 * c))).mp inferInstance
  apply CycleClass.Geometric.SupportedGerms.Cycles.supportedCohomologySection_ext_on_support (ModuleCat.of ℚ ℚ) T O ⊤ (2 * c)
  intro y _ hy
  let z : {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X // ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ F} := ⟨y, not_not.mp hy⟩
  have image (t : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (O : Set T) (2 * c)) :
      S.map (homOfLE (le_top : U z ≤ ⊤)).op
        (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) T O (2 * c) t) =
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O (U z) (2 * c)
        (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) (U z) (2 * c) t) :=
    ConcreteCategory.congr_hom
      (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap_restrict (ModuleCat.of ℚ ℚ) T O (U z) (2 * c)) t
  have he : S.map (homOfLE (le_top : U z ≤ ⊤)).op
      (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) T O (2 * c) a) =
      S.map (homOfLE (le_top : U z ≤ ⊤)).op
        (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) T O (2 * c) b) := by
    rw [image a, image b]
    exact congrArg (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O (U z) (2 * c)) (hab z)
  have hg := congrArg (TopCat.Presheaf.germ S (U z) y (hU z)) he
  rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at hg
  exact hg

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportAnalyticDetection.BundleCycles
