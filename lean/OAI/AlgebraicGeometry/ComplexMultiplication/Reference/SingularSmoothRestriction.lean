import OAI.AlgebraicGeometry.ComplexMultiplication.SingularSheafConstants
import OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.Integration
import OAI.AlgebraicGeometry.Cohomology.SingularComparison

/-! # Singular Smooth Restriction -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularSmoothRestriction

noncomputable section

/-! # Original singular sheaves restrict to genuine smooth singular sheaves

The map forgets complex module scalars, uses the actual chain-evaluation
isomorphism, and restricts to actual smooth simplices. No comparison premise
is supplied.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "Model" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "Y" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
local notation "mapComplex" =>
  Functor.mapHomologicalComplex (ReferenceSmooth.FormSheaf.originalSmoothFormSheafForget X) (ComplexShape.up ℕ)

/-- The genuine complex-coefficient singular sheaf complex, with original additive coefficients. -/
def originalOrdinarySingularComplexInt : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ :=
  ((mapComplex).obj (AlgebraicTopology.Cohomology.Singular.SheafResolution.singularSheafComplex Y)).extend
    ComplexShape.embeddingUpNat

/-- Actual chain evaluation identifies the two integer-indexed ordinary singular complexes. -/
def originalOrdinarySingularComplexIntBridgeIso :
    originalOrdinarySingularComplexInt X ≅ ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X ℂ :=
  (ComplexShape.embeddingUpNat.extendFunctor _).mapIso
    (SingularSheafBridge.originalComplexSingularSheafBridgeIso Y)

/-- Genuine restriction to smooth singular simplices, after literal scalar forgetting. -/
def originalOrdinaryToSmoothSheafRestrictionInt :
    originalOrdinarySingularComplexInt X ⟶ ReferenceSmooth.Integration.originalSmoothSingularComplexInt X :=
  HomologicalComplex.extendMap
    ((mapComplex).map (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafRestriction Model
      (ComplexPoint.Basic.ComplexSchemePoint X) (ModuleCat.of ℂ ℂ))) ComplexShape.embeddingUpNat

set_option backward.isDefEq.respectTransparency false in
/-- Actual restriction remains a quasi-isomorphism with the original additive coefficients. -/
instance originalOrdinaryToSmoothSheafRestrictionInt_quasiIso :
    QuasiIso (originalOrdinaryToSmoothSheafRestrictionInt X) := by
  have := AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.quasiIso_manifoldSmoothSheafRestriction Model
    (ComplexPoint.Basic.ComplexSchemePoint X) (ModuleCat.of ℂ ℂ)
  dsimp only [originalOrdinaryToSmoothSheafRestrictionInt]
  infer_instance

/-- Restriction from the unchanged original singular-cochain sheaf complex. -/
def originalSingularToSmoothSheafRestrictionInt :
    ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X ℂ ⟶ ReferenceSmooth.Integration.originalSmoothSingularComplexInt X :=
  (originalOrdinarySingularComplexIntBridgeIso X).inv ≫
    originalOrdinaryToSmoothSheafRestrictionInt X

/-- The actual original singular-to-smooth restriction induces cohomology isomorphisms. -/
instance originalSingularToSmoothSheafRestrictionInt_quasiIso :
    QuasiIso (originalSingularToSmoothSheafRestrictionInt X) := by
  dsimp only [originalSingularToSmoothSheafRestrictionInt]
  infer_instance

/-- Original ordinary and actual smooth singular sheaves give the same hypercohomology. -/
def originalSingularSmoothHypercohomologyAddEquiv (n : ℤ) :
    ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X ℂ) n ≃+
      ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (ReferenceSmooth.Integration.originalSmoothSingularComplexInt X) n where
  toEquiv := Localization.SmallShiftedHom.postcompEquiv
    (originalSingularToSmoothSheafRestrictionInt X)
    (originalSingularToSmoothSheafRestrictionInt_quasiIso X)
  map_add' := (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (originalSingularToSmoothSheafRestrictionInt X) n).map_add

/-- The equivalence uses exactly the original hypercohomology postcomposition map. -/
theorem originalSingularSmoothHypercohomologyAddEquiv_apply (n : ℤ)
    (α : ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X ℂ) n) :
    originalSingularSmoothHypercohomologyAddEquiv X n α =
      ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (originalSingularToSmoothSheafRestrictionInt X) n α := rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularSmoothRestriction
