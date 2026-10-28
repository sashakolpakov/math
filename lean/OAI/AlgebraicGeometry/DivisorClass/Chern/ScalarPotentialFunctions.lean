import OAI.AlgebraicGeometry.DivisorClass.Chern.GlobalScalarConjugation
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Change
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothPeriodMap

/-! # Scalar Potential Functions -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ScalarPotentialFunctions

noncomputable section

/-! Actual zero-forms as smooth scalar functions, with the original local curvature operator. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothPeriodMap.CM.Construction

section Real

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem zeroFormScalar_eval_any (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) (x : M)
    (v : Fin 0 → TangentSpace 𝓘(ℝ, E) x) : ComplexMultiplication.HodgeComparison.HolomorphicPrimitive.CM.Construction.zeroFormScalar f x = f x v :=
  congrArg (f x) (Subsingleton.elim _ _)

def scalarPotentialOpenFunction (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) (U : Opens M) :
    SmoothScalarForm.SmoothComplexOpenFunction (E := E) U :=
  ⟨fun x => ComplexMultiplication.HodgeComparison.HolomorphicPrimitive.CM.Construction.zeroFormScalar f x.val, (ComplexMultiplication.HodgeComparison.SmoothPeriodMap.CM.Construction.zeroFormScalar_contMDiff f).comp (contMDiff_subtype_val (I := 𝓘(ℝ, E)))⟩

theorem scalarPotentialOpenFunction_zeroForm (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) (U : Opens M) :
    SmoothScalarForm.smoothScalarOpenZeroForm (scalarPotentialOpenFunction f U) = Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U f := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  ext v
  rw [SmoothScalarForm.smoothScalarOpenZeroForm_apply]
  exact zeroFormScalar_eval_any f x.val v

def realPotentialScalar (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) (x : M) : ℝ := (ComplexMultiplication.HodgeComparison.HolomorphicPrimitive.CM.Construction.zeroFormScalar f x).re

theorem realPotentialScalar_smooth (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (realPotentialScalar f) :=
  Complex.reCLM.contDiff.contMDiff.comp (ComplexMultiplication.HodgeComparison.SmoothPeriodMap.CM.Construction.zeroFormScalar_contMDiff f)

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem realPotentialScalar_cast (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0)
    (hf : ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm f = f) (x : M) : (realPotentialScalar f x : ℂ) = ComplexMultiplication.HodgeComparison.HolomorphicPrimitive.CM.Construction.zeroFormScalar f x := by
  have hc : star (ComplexMultiplication.HodgeComparison.HolomorphicPrimitive.CM.Construction.zeroFormScalar f x) = ComplexMultiplication.HodgeComparison.HolomorphicPrimitive.CM.Construction.zeroFormScalar f x :=
    congrArg (fun a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0 => ComplexMultiplication.HodgeComparison.HolomorphicPrimitive.CM.Construction.zeroFormScalar a x) hf
  apply Complex.ext
  · rfl
  · have hi := congrArg Complex.im hc
    change -(ComplexMultiplication.HodgeComparison.HolomorphicPrimitive.CM.Construction.zeroFormScalar f x).im = (ComplexMultiplication.HodgeComparison.HolomorphicPrimitive.CM.Construction.zeroFormScalar f x).im at hi
    change 0 = (ComplexMultiplication.HodgeComparison.HolomorphicPrimitive.CM.Construction.zeroFormScalar f x).im
    linarith

end Real

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem oneFormHolomorphicPart_onOpen (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1) (U : Opens M) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U (ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.oneFormHolomorphicPart a) =
      Manifold.OneFormProjection.openManifoldOnePart (-Complex.I) (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U a) := by
  change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U ((1 / 2 : ℂ) •
    (a - Complex.I • Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit⁻¹ a)) =
    (1 / 2 : ℂ) • (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U a + (-Complex.I) •
      Open.ManifoldAction.openManifoldComplexAction AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit⁻¹ (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U a))
  rw [map_smul, map_sub, map_smul, Open.ManifoldAction.openManifoldComplexAction_onOpen]
  module

theorem scalarPotentialOpenFunction_curvature (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) (U : Opens M) :
    ScalarOpenConnection.smoothScalarOpenCurvature (scalarPotentialOpenFunction f U) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U (Projective.ScalarPotential.globalScalarCurvature f) := by
  rw [ScalarOpenConnection.smoothScalarOpenCurvature, scalarPotentialOpenFunction_zeroForm, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen_d,
    ← oneFormHolomorphicPart_onOpen, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen_d]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ScalarPotentialFunctions
