import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedSupportPurity
import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.FlasqueComparison

/-! # Closed Support Sections -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedSupportSections

noncomputable section

/-! In the first possible supported cohomological degree, classes on any
analytic open are exactly sections of the actual supported cohomology sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (F : Closeds X.left) (c : ℕ)
  (hc : ∀ Z : IrreducibleCloseds X.left, (Z : Set X.left) ⊆ F →
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + c ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
local notation "O" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions.analyticOpen X F.compl

include hc in
theorem closedSupportedStalk_isZero (x : T) (n : ℕ) (hn : n < 2 * c) :
    IsZero ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex
      (Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) T O) x).homology n) := by
  let Q := AlgebraicTopology.Cohomology.Singular.RelativeStalk.relativeNeighborhoodCohomology (ModuleCat.of ℚ ℚ) T (O : Set T) x n
  have hQ : IsZero Q := Q.isZero (fun U => by
    have h := ClosedSupportPurity.Constructions.closedSupport_open_cohomology_isZero X F c hc U.unop.1 n hn
    have he : {y : U.unop.1 | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y.val ∈ F}ᶜ =
        AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set T) U.unop.1 := by
      ext y
      rfl
    rw [he] at h
    exact h)
  exact ((colimit.isColimit Q).isZero_pt hQ).of_iso
    (AlgebraicTopology.Cohomology.Singular.SupportedStalk.supportedStalkRelativeCohomologyIso ℚ T O x n)

include hc in
theorem closedSupportSectionMap_isIso (U : Opens T) :
    IsIso (Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O U (2 * c)) := by
  rw [Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap_def]
  have := AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.quasiIso_relativeToSupportedSheafSections_of_metrizable ℚ T O U
  have := DivisorClass.Chern.Open.FlasqueComparison.rationalFlasqueOpenSectionMap_isIso U
    (Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) T O)
    (Geometric.GlobalSupportPurity.Cycles.supportedSingularSheaf_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ) T O) (2 * c)
    (fun n hn => Geometric.GlobalSupportPurity.Cycles.rationalSheafComplex_exactAt_of_stalk_isZero _ n
      (fun x => closedSupportedStalk_isZero X F c hc x n hn))
  infer_instance

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedSupportSections
