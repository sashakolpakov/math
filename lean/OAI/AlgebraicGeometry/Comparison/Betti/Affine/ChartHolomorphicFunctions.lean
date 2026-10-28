import OAI.AlgebraicGeometry.Comparison.Betti.Affine.RegularDifferentialsSpan
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FunctionDifferential

/-! # Chart Holomorphic Functions -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.ChartHolomorphicFunctions

noncomputable section

/-! Native affine-chart regular functions and their actual holomorphic differentials. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology

open OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FunctionDifferential

variable {A : Type} [CommRing A] [Algebra ℂ A] {n : ℕ}

def affineChartHolomorphicFunction
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A n) (a : A) :
    C^∞⟮𝓘(ℂ, Fin n → ℂ), Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e; 𝓘(ℂ), ℂ⟯ :=
  ⟨fun z => e.symm z a, by
    intro z
    apply (contMDiffAt_subtype_iff (U := Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e) (x := z)
      (f := fun y : Fin n → ℂ => e.symm y a)).mpr
    exact (((he.1 a).contDiffAt (e.open_target.mem_nhds z.property)).of_le
      (show (∞ : ℕ∞ω) ≤ ω from le_top)).contMDiffAt⟩

theorem affineChartHolomorphicFunction_extension
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A n) (a : A) (z : Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e) :
    Holomorphic.CoefficientMem.openCoefficientExtension (Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e) (affineChartHolomorphicFunction e he a) =ᶠ[𝓝 (z : Fin n → ℂ)]
      (fun y => e.symm y a) := by
  filter_upwards [e.open_target.mem_nhds z.property] with y hy
  exact Holomorphic.CoefficientMem.openCoefficientExtension_apply (Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e) _ ⟨y, hy⟩

theorem affineChartHolomorphicDifferential_dual
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A n) (a : A) (z : Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e) :
    Pure.OneCovectorDual.Holomorphic.pureOneCovectorDualEquiv (Fin n → ℂ)
        ((Holomorphic.CoefficientIndependence.openFormHolomorphicSectionFunctionEquiv (Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e) 1
          (Holomorphic.DeRhamComplex.differential (Fin n → ℂ) (Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e) 0
            (Holomorphic.ZeroFunctions.holomorphicFunctionZeroForm (affineChartHolomorphicFunction e he a)))).val z) =
      (fderiv ℂ (fun y => e.symm y a) (z : Fin n → ℂ)).toLinearMap := by
  rw [Holomorphic.FunctionDifferential.holomorphicFunctionDifferential_dual,
    (affineChartHolomorphicFunction_extension e he a z).fderiv_eq]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.ChartHolomorphicFunctions
