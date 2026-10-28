import OAI.AlgebraicGeometry.ComplexMultiplication.FilteredSmoothAdditiveAcyclic
import OAI.AlgebraicGeometry.ComplexMultiplication.NatExtendedAcyclic
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.AcyclicGlobalClasses

/-! # Filtered Smooth Int -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.FilteredSmoothInt

noncomputable section

/-! # The genuine filtered smooth complex, in the original integer grading -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "E" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "M" => OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X
local notation "Y" => TopCat.of M

local instance CMOriginalFilteredSmoothComplexInt.localInstance1 : HasExt.{1} (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) := HasExt.standard _

/-- The actual filtered forms, extended by zero in the original negative degrees. -/
def originalFilteredSmoothComplexInt (r : ℤ) :
    CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ :=
  (FilteredSmoothAdditiveAcyclic.originalFilteredSmoothComplexNat X r).extend ComplexShape.embeddingUpNat

/-- The actual inclusion into the original smooth de Rham complex. -/
def originalFilteredSmoothInclusionInt (r : ℤ) :
    originalFilteredSmoothComplexInt X r ⟶ ReferenceSmooth.Integration.originalSmoothDeRhamComplexInt X :=
  HomologicalComplex.extendMap (FilteredSmoothAdditiveAcyclic.originalFilteredSmoothInclusionNat X r)
    ComplexShape.embeddingUpNat

instance originalFilteredSmoothComplexInt_isStrictlyGE (r : ℤ) :
    (originalFilteredSmoothComplexInt X r).IsStrictlyGE 0 := by
  change CochainComplex.IsStrictlyGE ((FilteredSmoothAdditiveAcyclic.originalFilteredSmoothComplexNat X r).extend
    ComplexShape.embeddingUpNat) 0
  infer_instance

/-- The genuine filtered inclusion is monic after forgetting scalars. -/
instance originalFilteredSmoothInclusionNat_f_mono (r : ℤ) (q : ℕ) :
    Mono ((FilteredSmoothAdditiveAcyclic.originalFilteredSmoothInclusionNat X r).f q) := by
  change Mono ((ReferenceSmooth.FormSheaf.originalSmoothFormSheafForget X).map
    (Comparison.Betti.Filtered.SmoothComplex.Hodge.filteredFormSheafInclusion E M q r))
  have : IsSplitMono (Comparison.Betti.Filtered.SmoothComplex.Hodge.filteredFormSheafInclusion E M q r) :=
    IsSplitMono.mk' ⟨Comparison.Betti.Filtered.SmoothRetraction.Hodge.filteredFormSheafRetraction E M q r,
      Comparison.Betti.Filtered.SmoothRetraction.Hodge.filteredFormSheafInclusion_retraction E M q r⟩
  infer_instance

/-- Monicity also holds in every original integer degree. -/
instance originalFilteredSmoothInclusionInt_f_mono (r : ℤ) (q : ℤ) :
    Mono ((originalFilteredSmoothInclusionInt X r).f q) :=
  NatExtendedAcyclic.natExtended_map_f_mono (FilteredSmoothAdditiveAcyclic.originalFilteredSmoothInclusionNat X r) q

variable [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

/-- All terms remain Ext-acyclic in the exact original integer grading. -/
theorem originalFilteredSmoothComplexInt_ext_vanish (r : ℤ) (q : ℤ) (k : ℕ) :
    Subsingleton (Ext.{1} ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor Y).obj (AddCommGrpCat.of ℤ))
      ((originalFilteredSmoothComplexInt X r).X q) (k + 1)) :=
  NatExtendedAcyclic.natExtended_term_ext_vanish _ (FilteredSmoothAdditiveAcyclic.originalFilteredSmoothComplexNat X r)
    (fun n k => FilteredSmoothAdditiveAcyclic.originalFilteredSmoothForm_ext_vanish X n r k) q k

/-- Every original hypercohomology class has a genuine filtered global-form representative. -/
theorem originalFilteredSmoothGlobalClass_surjective (r n : ℤ) :
    Function.Surjective
      (GlobalNaturality.globalSectionsToHypercohomology X (originalFilteredSmoothComplexInt X r) n) :=
  AcyclicGlobalClasses.globalSectionsToHypercohomology_surjective_of_term_ext_vanish X
    (originalFilteredSmoothComplexInt X r) 0
      (originalFilteredSmoothComplexInt_ext_vanish X r) n

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.FilteredSmoothInt
