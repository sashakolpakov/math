import OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.ScalarForget
import OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.Hypercohomology
import OAI.AlgebraicGeometry.Comparison.Betti.Filtered.FormExtVanishing
import OAI.AlgebraicGeometry.Comparison.Betti.Filtered.SmoothComplex
import OAI.AlgebraicGeometry.Comparison.Betti.Complex.SheafCohomology
import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveConstantExt

/-! # Filtered Smooth Additive Acyclic -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.FilteredSmoothAdditiveAcyclic

noncomputable section

/-! # The actual filtered smooth sheaves are acyclic after forgetting scalars

This retains the original integer-constant source of Paul-Lez's hypercohomology.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

private theorem complexSheafCohomology_transport (Y : TopCat.{0})
    (N : Sheaf (Opens.grothendieckTopology Y) (ModuleCat.{0} ℂ)) (q : ℕ)
    (h : Subsingleton (Ext.{1}
      ((constantSheaf (Opens.grothendieckTopology Y) (ModuleCat.{0} ℂ)).obj
        (ModuleCat.of ℂ ℂ)) N q)) :
    Subsingleton (Sheaf.H.{0} ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj N) q) := by
  exact (Comparison.Betti.Complex.SheafCohomology.complexSheafCohomologyForgetEquiv Y N q).toEquiv.subsingleton_congr.mp h

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "E" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "M" => OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X
local notation "Y" => TopCat.of M

local instance CMFilteredSmoothAdditiveAcyclic.localInstance1 : HasExt.{1} (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) := HasExt.standard _
local instance CMFilteredSmoothAdditiveAcyclic.localInstance2 : HasExt.{1} (Comparison.Betti.ConstantSheafSections.ComplexSheaves Y) := HasExt.standard _

/-- Literal additive forgetting of the genuine filtered smooth de Rham complex. -/
def originalFilteredSmoothComplexNat (r : ℤ) :
    CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℕ :=
  ((ReferenceSmooth.FormSheaf.originalSmoothFormSheafForget X).mapHomologicalComplex (.up ℕ)).obj
    (Comparison.Betti.Filtered.SmoothComplex.Hodge.filteredSmoothSheafComplex E M r)

/-- Its actual inclusion retains the original smooth differential. -/
def originalFilteredSmoothInclusionNat (r : ℤ) :
    originalFilteredSmoothComplexNat X r ⟶
      ((ReferenceSmooth.FormSheaf.originalSmoothFormSheafForget X).mapHomologicalComplex (.up ℕ)).obj
        (Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex E M) :=
  ((ReferenceSmooth.FormSheaf.originalSmoothFormSheafForget X).mapHomologicalComplex (.up ℕ)).map
    (Comparison.Betti.Filtered.SmoothComplex.Hodge.filteredSmoothSheafInclusion E M r)

variable [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

/-- All higher cohomology of the actual additive filtered form sheaf vanishes. -/
theorem originalFilteredSmoothForm_cohomology_vanish (n : ℕ) (r : ℤ) (q : ℕ) :
    Subsingleton (Sheaf.H.{0} ((originalFilteredSmoothComplexNat X r).X n) (q + 1)) := by
  exact complexSheafCohomology_transport Y
    (Comparison.Betti.Filtered.SmoothComplex.Hodge.filteredFormSheaf E M n r) (q + 1)
    (Comparison.Betti.Filtered.FormExtVanishing.Hodge.filteredFormSheaf_ext_vanish E M n r q)

/-- Thus its higher Ext from the original unlifted integer constants also vanishes. -/
theorem originalFilteredSmoothForm_ext_vanish (n : ℕ) (r : ℤ) (q : ℕ) :
    Subsingleton (Ext.{1} ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor Y).obj (AddCommGrpCat.of ℤ))
      ((originalFilteredSmoothComplexNat X r).X n) (q + 1)) :=
  Comparison.Betti.AdditiveConstantExt.Cech.constantIntegerExt_subsingleton Y _ (q + 1)
    (originalFilteredSmoothForm_cohomology_vanish X n r q)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.FilteredSmoothAdditiveAcyclic
