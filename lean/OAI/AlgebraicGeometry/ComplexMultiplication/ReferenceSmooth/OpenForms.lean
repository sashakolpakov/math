import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RealFormDifferential
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CotangentRestriction
import OAI.Analysis.DifferentialForms.Manifold.OpenDerivative

/-! # Open Forms -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.OpenForms

noncomputable section

/-! # Original holomorphic forms as genuine smooth forms on their open domain

The original quotient maps complex-linearly to actual smooth tangent forms.
Restriction and exterior differentiation agree with the original operations.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "Model" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "I" => 𝓘(ℂ, Model)

/-- At each point of the original open the field is the original quotient evaluation. -/
theorem originalHolomorphicOriginalComplexField_apply
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (p : ℕ)
    (θ : ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) p) (x : U) :
    Reference.RealFormSmooth.originalHolomorphicOriginalComplexField X U p θ x =
      Reference.CotangentEvaluation.originalHolomorphicCotangentEvaluation X U p θ x := by
  exact dite_eq_left x.property

/-- The original holomorphic-form class gives an actual smooth form on its domain. -/
def originalHolomorphicSmoothOpenForm
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (p : ℕ)
    (θ : ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) p) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm Model U p :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ofRaw U (Reference.RealFormSmooth.originalHolomorphicRealRawForm X U p θ)
    (Reference.RealFormSmooth.originalHolomorphicRealRawForm_smooth X U p θ)

/-- The smooth form has the actual original cotangent values in preferred real coordinates. -/
theorem originalHolomorphicSmoothOpenForm_apply
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (p : ℕ)
    (θ : ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) p) (x : U)
    (v : Fin p → TangentSpace 𝓘(ℝ, Model) x.val) :
    originalHolomorphicSmoothOpenForm X U p θ x v =
      Reference.CotangentEvaluation.originalHolomorphicCotangentEvaluation X U p θ x
        (fun i => Analysis.DifferentialForms.Manifold.TangentCoordinates.preferredTangentEquiv (E := Model) x.val (v i)) := by
  change Reference.RealFormSmooth.originalHolomorphicOriginalComplexField X U p θ x
      (fun i => Analysis.DifferentialForms.Manifold.TangentCoordinates.preferredTangentEquiv (E := Model) x.val (v i)) = _
  rw [originalHolomorphicOriginalComplexField_apply]
  rfl

/-- Actual smooth tangent forms retain the complex-linear structure of the original quotient. -/
def originalHolomorphicToSmoothOpenForm
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (p : ℕ) :
    ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) p →ₗ[ℂ]
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm Model U p where
  toFun := originalHolomorphicSmoothOpenForm X U p
  map_add' θ η := by
    apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
    intro x
    apply ContinuousAlternatingMap.ext
    intro v
    change originalHolomorphicSmoothOpenForm X U p (θ + η) x v =
      originalHolomorphicSmoothOpenForm X U p θ x v +
        originalHolomorphicSmoothOpenForm X U p η x v
    rw [originalHolomorphicSmoothOpenForm_apply, originalHolomorphicSmoothOpenForm_apply,
      originalHolomorphicSmoothOpenForm_apply]
    exact congrArg (fun c : TangentSpace I x.val [⋀^Fin p]→L[ℂ] ℂ =>
      c (fun i => Analysis.DifferentialForms.Manifold.TangentCoordinates.preferredTangentEquiv (E := Model) x.val (v i)))
        (congrFun ((Reference.CotangentEvaluation.originalHolomorphicCotangentEvaluation X U p).map_add θ η) x)
  map_smul' c θ := by
    apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
    intro x
    apply ContinuousAlternatingMap.ext
    intro v
    change originalHolomorphicSmoothOpenForm X U p (c • θ) x v =
      c • originalHolomorphicSmoothOpenForm X U p θ x v
    rw [originalHolomorphicSmoothOpenForm_apply, originalHolomorphicSmoothOpenForm_apply]
    exact congrArg (fun a : TangentSpace I x.val [⋀^Fin p]→L[ℂ] ℂ =>
      a (fun i => Analysis.DifferentialForms.Manifold.TangentCoordinates.preferredTangentEquiv (E := Model) x.val (v i)))
        (congrFun ((Reference.CotangentEvaluation.originalHolomorphicCotangentEvaluation X U p).map_smul c θ) x)

/-- The genuine smooth-form map commutes with the original open restriction. -/
theorem originalHolomorphicToSmoothOpenForm_restrict
    {U V : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))} (h : V ≤ U) (p : ℕ)
    (θ : ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) p) :
    originalHolomorphicToSmoothOpenForm X V p
      (ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormRestriction X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (homOfLE h).op p θ) =
        Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h
          (originalHolomorphicToSmoothOpenForm X U p θ) := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  apply ContinuousAlternatingMap.ext
  intro v
  change originalHolomorphicSmoothOpenForm X V p _ x v =
    originalHolomorphicSmoothOpenForm X U p θ ⟨x.val, h x.property⟩ v
  rw [originalHolomorphicSmoothOpenForm_apply, originalHolomorphicSmoothOpenForm_apply]
  exact congrArg (fun a : TangentSpace I x.val [⋀^Fin p]→L[ℂ] ℂ =>
    a (fun i => Analysis.DifferentialForms.Manifold.TangentCoordinates.preferredTangentEquiv (E := Model) x.val (v i)))
      (Reference.CotangentRestriction.originalHolomorphicCotangentEvaluation_restrict X h p θ x)

/-- The genuine smooth-form map commutes with the original exterior differential. -/
theorem originalHolomorphicToSmoothOpenForm_differential
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (p : ℕ)
    (θ : ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) p) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (originalHolomorphicToSmoothOpenForm X U p θ) =
      originalHolomorphicToSmoothOpenForm X U (p + 1)
        (ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) p θ) := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  exact (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d_ofRaw_apply
    (Reference.RealFormSmooth.originalHolomorphicRealRawForm X U p θ)
    (Reference.RealFormSmooth.originalHolomorphicRealRawForm_smooth X U p θ) x).trans
    (Reference.RealFormDifferential.originalHolomorphicRealRawForm_differential X U p θ x)

/-- No original holomorphic-form class is lost under actual real tangent evaluation. -/
theorem originalHolomorphicToSmoothOpenForm_injective
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (p : ℕ) :
    Function.Injective (originalHolomorphicToSmoothOpenForm X U p) := by
  intro θ η h
  apply Reference.CotangentEvaluation.originalHolomorphicCotangentEvaluation_injective X U p
  funext x
  apply ContinuousAlternatingMap.ext
  intro v
  let T := Analysis.DifferentialForms.Manifold.TangentCoordinates.preferredTangentEquiv (E := Model) x.val
  have hv := congrArg (fun f : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm Model U p =>
    f x (fun i => T.symm (v i))) h
  change originalHolomorphicSmoothOpenForm X U p θ x (fun i => T.symm (v i)) =
    originalHolomorphicSmoothOpenForm X U p η x (fun i => T.symm (v i)) at hv
  rw [originalHolomorphicSmoothOpenForm_apply, originalHolomorphicSmoothOpenForm_apply] at hv
  have htuple : (fun i => T (T.symm (v i))) = v := funext fun i => T.apply_symm_apply (v i)
  change Reference.CotangentEvaluation.originalHolomorphicCotangentEvaluation X U p θ x
      (fun i => T (T.symm (v i))) =
    Reference.CotangentEvaluation.originalHolomorphicCotangentEvaluation X U p η x (fun i => T (T.symm (v i))) at hv
  rw [htuple] at hv
  exact hv

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.OpenForms
