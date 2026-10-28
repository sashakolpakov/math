import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SupportDetection

/-! # Support Local Detection -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SupportLocalDetection.Constructions

noncomputable section

/-! In the first possible supported degree, equality on an ambient
open follows from equality near every point of its closed support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedSupportSections.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem restriction_eq_iff_pairMap {T : TopCat} (O : Set T) (P : Opens T) (S : Set P)
    (he : S = AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := T) O P)
    (hm : Set.MapsTo (Geometric.LocalHomology.Cycles.subspaceInclusion T (P : Set T)) S O) (d : ℕ)
    (a b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T O d) :
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T O P d a =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T O P d b ↔
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Geometric.LocalHomology.Cycles.subspaceInclusion T (P : Set T)) hm d a =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Geometric.LocalHomology.Cycles.subspaceInclusion T (P : Set T)) hm d b := by
  cases he
  rfl

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (F : Closeds X.left) (c : ℕ)
  (hc : ∀ Z : IrreducibleCloseds X.left, (Z : Set X.left) ⊆ F →
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + c ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
  (G : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
local notation "O" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions.analyticOpen X F.compl

include hc in
theorem relativeClass_eq_on_open_of_local
    (a b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (O : Set T) (2 * c))
    (hloc : ∀ x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X, x ∈ G → x ∉ O →
      ∃ P : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X), x ∈ P ∧
        Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) P (2 * c) a =
          Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) P (2 * c) b) :
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) G (2 * c) a =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) G (2 * c) b := by
  let S := ((Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) T O).homology (2 * c)).obj
  have hs : IsIso (Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O G (2 * c)) :=
    ClosedSupportSections.Constructions.closedSupportSectionMap_isIso X F c hc G
  apply (ModuleCat.mono_iff_injective
    (Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O G (2 * c))).mp inferInstance
  have image (a' : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (O : Set T) (2 * c)) (P : Opens T) :
      S.map (homOfLE (le_top : P ≤ ⊤)).op
        (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap (ModuleCat.of ℚ ℚ) T O (2 * c) a') =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O P (2 * c)
        (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) P (2 * c) a') :=
    ConcreteCategory.congr_hom (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap_restrict (ModuleCat.of ℚ ℚ) T O P (2 * c)) a'
  rw [← image a G, ← image b G]
  apply Geometric.SupportedGerms.Cycles.supportedCohomologySection_ext_on_support (ModuleCat.of ℚ ℚ) T O G (2 * c)
  intro x hxG hxO
  obtain ⟨P, hxP, he⟩ := hloc x hxG hxO
  have h := congrArg (Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O P (2 * c)) he
  rw [← image a P, ← image b P] at h
  have hg := congrArg (TopCat.Presheaf.germ S P x hxP) h
  rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at hg
  rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
  exact hg

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SupportLocalDetection.Constructions
