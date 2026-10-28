import OAI.AlgebraicGeometry.Comparison.Betti.Affine.ChartSymbolCoefficients

/-! # Symbol Frame Values -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.SymbolFrameValues

noncomputable section

/-! Symbols built from a regular cotangent basis evaluate to the canonical pure exterior basis. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {A ι : Type} [CommRing A] [Algebra ℂ A] [LinearOrder ι] {d : ℕ}

def regularExteriorSymbol (a : ι → A) (n : ℕ) (s : Set.powersetCard ι n) : Algebraic.Forms.Form A n :=
  Algebraic.Forms.formSymbol A (Fin.cons 1 (fun j => a (Set.powersetCard.ofFinEmbEquiv.symm s j)))

theorem affineChart_symbol_coefficients_eq_basis
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin d → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A d) (x : Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e)
    (b : Module.Basis ι ℂ (Module.Dual ℂ (Fin d → ℂ))) (a : ι → A)
    (hb : ∀ i, b i = (fderiv ℂ (fun y => e.symm y (a i)) (x : Fin d → ℂ)).toLinearMap)
    (n : ℕ) (s : Set.powersetCard ι n) :
    (Holomorphic.CoefficientIndependence.openFormHolomorphicSectionFunctionEquiv (Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e) n
        (ChartFormEvaluation.affineChartHolomorphicFormMap e he n (regularExteriorSymbol a n s))).val x =
      Pure.CovectorExteriorBasis.Holomorphic.pureCovectorExteriorBasis b n s := by
  apply Subtype.ext
  ext v
  change (Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv (Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e) n).symm
    (Holomorphic.DeRhamComplex.inclusion (Fin d → ℂ) (Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e) n
      (ChartFormEvaluation.affineChartHolomorphicFormMap e he n
        (Algebraic.Forms.formSymbol A (Fin.cons 1
          (fun j => a (Set.powersetCard.ofFinEmbEquiv.symm s j)))))) x v = _
  rw [ChartSymbolCoefficients.affineChartHolomorphicFormMap_symbol_coefficients, Pure.CovectorExteriorBasis.Holomorphic.pureCovectorExteriorBasis_apply_det]
  simp only [Fin.cons_zero, Fin.cons_succ, map_one, one_mul]
  congr 1
  ext i j
  exact congrArg (fun f : Module.Dual ℂ (Fin d → ℂ) => f (v i))
    (hb (Set.powersetCard.ofFinEmbEquiv.symm s j)).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.SymbolFrameValues
