import OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.FormSheaf
import OAI.Analysis.DifferentialForms.Manifold.DeRhamResolution
import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-! # Constants -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.Constants

noncomputable section

/-! # The original holomorphic-to-smooth map retains actual scalar constants -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "Model" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "I" => 𝓘(ℂ, Model)

/-- The original scalar zero-form retains its actual scalar value on every tangent tuple. -/
theorem originalHolomorphicToSmoothOpenForm_constant
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (c : ℂ) (x : U)
    (v : Fin 0 → TangentSpace 𝓘(ℝ, Model) x.val) :
    OpenForms.originalHolomorphicToSmoothOpenForm X U 0
      (ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormOfConstant X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) c) x v = c := by
  have hy : extChartAt I x.val x.val ∈
      ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) x.val := by
    refine ⟨mem_extChartAt_target x.val, ?_⟩
    change (extChartAt I x.val).symm (extChartAt I x.val x.val) ∈ U
    rw [(extChartAt I x.val).left_inv (mem_extChartAt_source x.val)]
    exact x.property
  have hc := ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_ofConstant X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) x.val c hy
  have hv := congrArg (fun a : Model [⋀^Fin 0]→L[ℂ] ℂ =>
    a (fun i => Analysis.DifferentialForms.Manifold.TangentCoordinates.preferredTangentEquiv (E := Model) x.val (v i))) hc
  change OpenForms.originalHolomorphicSmoothOpenForm X U 0
    (ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormOfConstant X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) c) x v = _
  rw [OpenForms.originalHolomorphicSmoothOpenForm_apply]
  exact hv

/-- The actual scalar inclusion into smooth zero-forms, via actual locally constant functions. -/
def originalConstantsToSmoothZero :
    𝓒ᵖ(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ) ⟶ (FormSheaf.originalSmoothFormAddSheaf X 0).presheaf :=
  Functor.whiskerRight
    (AlgebraicTopology.DeRham.Comparison.ConstantLocallyConstant.constantToLocallyConstant (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) ≫
      Analysis.DifferentialForms.Manifold.LocallyConstantKernel.manifoldLocallyConstantToZeroPresheaf Model (ComplexPoint.Basic.ComplexSchemePoint X))
    (forget₂ (ModuleCat ℂ) AddCommGrpCat)

/-- The original holomorphic-to-smooth presheaf map retains the actual constant augmentation. -/
theorem originalHolomorphicToSmoothPresheaf_constant :
    ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) ≫
      FormSheaf.originalHolomorphicToSmoothPresheaf X 0 = originalConstantsToSmoothZero X := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro c
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  apply ContinuousAlternatingMap.ext
  intro v
  change OpenForms.originalHolomorphicToSmoothOpenForm X U.unop 0
      (ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormOfConstant X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) U c) x v =
    Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantToManifoldZeroForm Model U.unop
      (LocallyConstant.const U.unop c) x v
  rw [Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantToManifoldZeroForm_apply]
  exact originalHolomorphicToSmoothOpenForm_constant X U.unop c x v

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.Constants
