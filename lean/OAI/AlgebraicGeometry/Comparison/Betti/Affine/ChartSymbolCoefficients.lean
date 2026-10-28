import OAI.AlgebraicGeometry.Comparison.Betti.Affine.ChartFormEvaluation
import OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorExteriorBasis

/-! # Chart Symbol Coefficients -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.ChartSymbolCoefficients

noncomputable section

/-! The original algebraic symbols have the exact determinant coefficients in native affine charts. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorExteriorBasis.Holomorphic

attribute [local instance] Smooth.SymbolPointwise.tangentNormedGroup Smooth.SymbolPointwise.tangentNormedSpace

variable {A : Type} [CommRing A] [Algebra ℂ A] {d : ℕ}

theorem affineChartHolomorphicFormMap_symbol_coefficients
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin d → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A d) (n : ℕ) (a : Fin (n + 1) → A)
    (x : Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e) (v : Fin n → (Fin d → ℂ)) :
    (Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv (Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e) n).symm
        (Holomorphic.DeRhamComplex.inclusion (Fin d → ℂ) (Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e) n
          (ChartFormEvaluation.affineChartHolomorphicFormMap e he n (Algebraic.Forms.formSymbol A a))) x v =
      e.symm x (a 0) *
        (Matrix.of (fun i j => fderiv ℂ (fun y => e.symm y (a j.succ)) (x : Fin d → ℂ) (v i))).det := by
  change Smooth.CochainMap.smoothFormMap (ChartFormEvaluation.affineChartContinuousEvaluation e he)
    (ChartFormEvaluation.affineChartEvaluation_realSmooth e he) n (Algebraic.Forms.formSymbol A a) x
      (fun i => (Analysis.DifferentialForms.Manifold.OpenEquivalence.openTangentEquiv x).symm (v i)) = _
  rw [Smooth.CochainMap.smoothFormMap_symbol, Smooth.SymbolPointwise.smoothSymbol_covectors]
  erw [IteratedCovectorDeterminant.Smooth.iteratedCovectorWedge_eq_det]
  apply congrArg (fun B : Matrix (Fin n) (Fin n) ℂ => e.symm x (a 0) * B.det)
  ext i j
  exact ChartFormEvaluation.affineChartFunctionCovector_apply e he (a j.succ) x (v i)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.ChartSymbolCoefficients
