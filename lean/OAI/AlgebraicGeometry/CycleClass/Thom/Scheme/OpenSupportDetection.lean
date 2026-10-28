import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedSupportSections

/-! # Open Support Detection -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.OpenSupportDetection.Constructions

noncomputable section

/-! In the first possible supported degree, equality on arbitrary
analytic neighborhoods of the support detects equality on any fixed
ambient analytic open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedSupportSections.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (F : Closeds X.left) (c : ℕ)
  (hc : ∀ Z : IrreducibleCloseds X.left, (Z : Set X.left) ⊆ F →
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + c ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
local notation "O" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions.analyticOpen X F.compl
local notation "I" => Subtype (fun x : U => OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (Subtype.val x) ∈ F)

include hc in
theorem relativeClass_eq_of_support_neighborhoods
    (P : I → Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (hP : ∀ x, P x ≤ U)
    (hxP : ∀ x, x.val.val ∈ P x)
    (a b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set T) U) (2 * c))
    (hab : ∀ x, (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) T (O : Set T) (2 * c)).map
        (homOfLE (hP x)).op a =
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) T (O : Set T) (2 * c)).map
        (homOfLE (hP x)).op b) : a = b := by
  let H := ((Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) T O).homology (2 * c)).obj
  let : IsIso (Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O U (2 * c)) :=
    ClosedSupportSections.Constructions.closedSupportSectionMap_isIso X F c hc U
  apply (ModuleCat.mono_iff_injective
    (Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O U (2 * c))).mp inferInstance
  apply Geometric.SupportedGerms.Cycles.supportedCohomologySection_ext_on_support (ModuleCat.of ℚ ℚ) T O U (2 * c)
  intro x hxU hxO
  let z : I := ⟨⟨x, hxU⟩, not_not.mp hxO⟩
  have image (v : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set T) U) (2 * c)) :=
    ConcreteCategory.congr_hom (Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap_naturality
      (ModuleCat.of ℚ ℚ) T O (homOfLE (hP z)) (2 * c)) v
  have he : H.map (homOfLE (hP z)).op (Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O U (2 * c) a) =
      H.map (homOfLE (hP z)).op (Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O U (2 * c) b) :=
    (image a).symm.trans ((congrArg (Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O (P z) (2 * c)) (hab z)).trans (image b))
  have hg := congrArg (TopCat.Presheaf.germ H (P z) x (hxP z)) he
  rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at hg
  exact hg

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.OpenSupportDetection.Constructions
