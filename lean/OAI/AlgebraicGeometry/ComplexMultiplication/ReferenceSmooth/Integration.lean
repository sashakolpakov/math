import OAI.AlgebraicGeometry.ComplexMultiplication.SmoothIntegrationGlobalValues
import OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.ScalarForget
import OAI.AlgebraicGeometry.Hodge.Filtration
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! # Integration -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.Integration

noncomputable section

/-! # Actual simplex integration on the original analytic space

The maps literally forget complex scalars and extend the genuine sheaf
integration by zero. No comparison map or normalization is assumed.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "Model" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "F" => OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.FormSheaf.originalSmoothFormSheafForget X
local notation "mapComplex" =>
  Functor.mapHomologicalComplex (FormSheaf.originalSmoothFormSheafForget X) (ComplexShape.up ℕ)

/-- The actual smooth de Rham sheaf complex with original additive coefficients. -/
def originalSmoothDeRhamComplexInt : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ :=
  ((mapComplex).obj (Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex Model (ComplexPoint.Basic.ComplexSchemePoint X))).extend
    ComplexShape.embeddingUpNat

/-- The actual smooth-singular sheaf complex with original additive coefficients. -/
def originalSmoothSingularComplexInt : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ :=
  ((mapComplex).obj (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafComplex Model (ComplexPoint.Basic.ComplexSchemePoint X)
    (ModuleCat.of ℂ ℂ))).extend ComplexShape.embeddingUpNat

/-- The genuine open-domain simplex integrals on the original analytic space. -/
def originalSmoothIntegrationSheafComplexInt :
    originalSmoothDeRhamComplexInt X ⟶ originalSmoothSingularComplexInt X :=
  HomologicalComplex.extendMap
    ((mapComplex).map (SmoothIntegrationGlobalValues.actualSmoothIntegrationSheaf Model (ComplexPoint.Basic.ComplexSchemePoint X)))
    ComplexShape.embeddingUpNat

set_option backward.isDefEq.respectTransparency false in
/-- Actual simplex integration remains a quasi-isomorphism with original additive coefficients. -/
instance originalSmoothIntegrationSheafComplexInt_quasiIso :
    QuasiIso (originalSmoothIntegrationSheafComplexInt X) := by
  have := SmoothIntegrationGlobalValues.actualSmoothIntegrationSheaf_quasiIso Model (ComplexPoint.Basic.ComplexSchemePoint X)
  dsimp only [originalSmoothIntegrationSheafComplexInt]
  infer_instance

/-- Actual smooth forms and actual smooth-singular sheaves give the same hypercohomology. -/
def originalSmoothIntegrationHypercohomologyAddEquiv (n : ℤ) :
    ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (originalSmoothDeRhamComplexInt X) n ≃+
      ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (originalSmoothSingularComplexInt X) n where
  toEquiv := Localization.SmallShiftedHom.postcompEquiv
    (originalSmoothIntegrationSheafComplexInt X)
    (originalSmoothIntegrationSheafComplexInt_quasiIso X)
  map_add' := (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (originalSmoothIntegrationSheafComplexInt X) n).map_add

/-- Its actual underlying map is original hypercohomology postcomposition. -/
theorem originalSmoothIntegrationHypercohomologyAddEquiv_apply (n : ℤ)
    (α : ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (originalSmoothDeRhamComplexInt X) n) :
    originalSmoothIntegrationHypercohomologyAddEquiv X n α =
      ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (originalSmoothIntegrationSheafComplexInt X) n α := rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.Integration
