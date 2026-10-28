import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ChartIso
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.IntrinsicCoefficientAction
import OAI.AlgebraicGeometry.Comparison.Betti.SemilinearBasisTransport

/-! # Chart Module Bases -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ChartModuleBases

noncomputable section

/-! Native holomorphic coordinate changes transport actual differential-module bases. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

def chartFunctionEquiv (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (V : Opens E) (hV : V ≤ Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e) :
    C^∞⟮𝓘(ℂ, E), V; 𝓘(ℂ), ℂ⟯ ≃ₐ[ℂ]
      C^∞⟮𝓘(ℂ, E), Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen e V; 𝓘(ℂ), ℂ⟯ where
  toFun f := f.comp ⟨ChartMaps.chartForward e V, ChartMaps.chartForward_holomorphic e he V⟩
  invFun f := f.comp ⟨ChartIso.chartInverseToPreimage e V hV, ChartIso.chartInverseToPreimage_holomorphic e he V hV⟩
  left_inv f := by
    apply ContMDiffMap.ext
    intro x
    exact congrArg f (congrFun (ChartIso.chartForward_inverseToPreimage e V hV) x)
  right_inv f := by
    apply ContMDiffMap.ext
    intro x
    exact congrArg f (congrFun (ChartIso.chartInverseToPreimage_forward e V hV) x)
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

def chartFormEquiv (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (V : Opens E) (hV : V ≤ Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e) (n : ℕ) :
    DeRhamComplex.forms E V n ≃ₗ[ℂ] DeRhamComplex.forms E (Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen e V) n :=
  ((HomologicalComplex.eval (ModuleCat ℂ) (ComplexShape.up ℕ) n).mapIso
    (ChartIso.chartComplexIso e he V hV)).symm.toLinearEquiv

variable [FiniteDimensional ℂ E]

def chartPreimageFormBasis (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (V : Opens E) (hV : V ≤ Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e) (n : ℕ)
    (b : Module.Basis I (FunctionPure.holomorphicFunctions V) (DeRhamComplex.forms E V n)) :
    Module.Basis I C^∞⟮𝓘(ℂ, E), Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen e V; 𝓘(ℂ), ℂ⟯
      (DeRhamComplex.forms E (Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen e V) n) :=
  SemilinearBasisTransport.LinearAlgebra.basisTransport b
    ((IntrinsicFunctionSheaf.holomorphicFunctionContMDiffEquiv V).trans (chartFunctionEquiv e he V hV)).toRingEquiv
    (chartFormEquiv e he V hV n).toAddEquiv (fun f a =>
      (congrArg (HolomorphicPullback.pullback (ChartMaps.chartForward e V) (ChartMaps.chartForward_holomorphic e he V) n)
        (IntrinsicCoefficientAction.nativeFunction_smul_eq V n f a).symm).trans
          (ManifoldHolomorphicModules.pullback_function_smul (ChartMaps.chartForward e V) (ChartMaps.chartForward_holomorphic e he V) n
            (IntrinsicFunctionSheaf.holomorphicFunctionContMDiffEquiv V f) a))

theorem chartPreimageFormBasis_apply (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (V : Opens E) (hV : V ≤ Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e) (n : ℕ)
    (b : Module.Basis I (FunctionPure.holomorphicFunctions V) (DeRhamComplex.forms E V n)) (i : I) :
    chartPreimageFormBasis e he V hV n b i =
      HolomorphicPullback.pullback (ChartMaps.chartForward e V) (ChartMaps.chartForward_holomorphic e he V) n (b i) :=
  SemilinearBasisTransport.LinearAlgebra.basisTransport_apply b _ _ _ i

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ChartModuleBases
