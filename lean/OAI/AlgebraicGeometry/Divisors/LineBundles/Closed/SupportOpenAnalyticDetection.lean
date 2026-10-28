import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportAnalyticDetection

/-! # Support Open Analytic Detection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportOpenAnalyticDetection.BundleCycles

noncomputable section

section

/-! In the first support degree, classes on any analytic open are detected by smaller analytic neighborhoods covering its actual algebraic support. -/

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
theorem closedSupportedClass_on_open_eq_of_neighborhoods
    (V : Opens T) (U : {x : V // ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ F} → Opens T)
    (hUV : ∀ z, U z ≤ V) (hU : ∀ z, z.val.val ∈ U z)
    (a b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of V)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set T) V) (2 * c))
    (hab : ∀ z, (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) T (O : Set T) (2 * c)).map
        (homOfLE (hUV z)).op a =
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) T (O : Set T) (2 * c)).map
        (homOfLE (hUV z)).op b) : a = b := by
  let S := ((CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) T O).homology (2 * c)).obj
  have hi := CycleClass.Thom.Scheme.ClosedSupportSections.Constructions.closedSupportSectionMap_isIso X F c hc V
  apply (ModuleCat.mono_iff_injective
    (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O V (2 * c))).mp inferInstance
  apply CycleClass.Geometric.SupportedGerms.Cycles.supportedCohomologySection_ext_on_support (ModuleCat.of ℚ ℚ) T O V (2 * c)
  intro y hyV hy
  let z : {x : V // ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ F} := ⟨⟨y, hyV⟩, not_not.mp hy⟩
  have image (t : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of V)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set T) V) (2 * c)) :
      S.map (homOfLE (hUV z)).op
        (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O V (2 * c) t) =
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O (U z) (2 * c)
        ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) T (O : Set T) (2 * c)).map
          (homOfLE (hUV z)).op t) :=
    (ConcreteCategory.congr_hom (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap_naturality (ModuleCat.of ℚ ℚ)
      T O (homOfLE (hUV z)) (2 * c)) t).symm
  have he : S.map (homOfLE (hUV z)).op
      (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O V (2 * c) a) =
      S.map (homOfLE (hUV z)).op
        (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O V (2 * c) b) := by
    rw [image a, image b]
    exact congrArg (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O (U z) (2 * c)) (hab z)
  have hg := congrArg (TopCat.Presheaf.germ S (U z) y (hU z)) he
  rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at hg
  exact hg

end

/-! The analytic support detection theorem applies to any literally identified presentation of the complement of the same closed algebraic support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (F : Closeds X.left) (c : ℕ)
  (hc : ∀ Z : IrreducibleCloseds X.left, (Z : Set X.left) ⊆ F →
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + c ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

variable (A : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (hA : A = (CycleClass.Thom.Scheme.SectionEvaluation.Constructions.analyticOpen X F.compl : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))

include hc hA in
theorem closedSupportedSetClass_on_open_eq_of_neighborhoods
    (V : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (U : {x : V // ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ F} → Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (hUV : ∀ z, U z ≤ V) (hU : ∀ z, z.val.val ∈ U z)
    (a b : (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) A (2 * c)).obj (Opposite.op V))
    (hab : ∀ z, (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) A (2 * c)).map
        (homOfLE (hUV z)).op a =
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) A (2 * c)).map
        (homOfLE (hUV z)).op b) : a = b := by
  subst A
  exact closedSupportedClass_on_open_eq_of_neighborhoods X F c hc V U hUV hU a b hab

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportOpenAnalyticDetection.BundleCycles
