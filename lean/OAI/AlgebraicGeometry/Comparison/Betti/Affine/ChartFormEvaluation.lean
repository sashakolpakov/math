import OAI.AlgebraicGeometry.Comparison.Betti.Affine.ChartHolomorphicFunctions
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.Factorization

/-! # Chart Form Evaluation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.ChartFormEvaluation

noncomputable section

/-! The original symbol realization applied to regular evaluation in a native affine chart. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {A : Type} [CommRing A] [Algebra ℂ A] {d : ℕ}

def affineChartContinuousEvaluation
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin d → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A d) : A →ₐ[ℂ] C(Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e, ℂ) where
  toFun a := ⟨fun z => e.symm z a, (ChartHolomorphicFunctions.affineChartHolomorphicFunction e he a).property.continuous⟩
  map_zero' := by ext z; exact map_zero (e.symm z)
  map_one' := by ext z; exact map_one (e.symm z)
  map_add' a b := by ext z; exact map_add (e.symm z) a b
  map_mul' a b := by ext z; exact map_mul (e.symm z) a b
  commutes' c := by ext z; exact (e.symm z).commutes c

theorem affineChartEvaluation_complexSmooth
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin d → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A d) (a : A) :
    ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ∞ (affineChartContinuousEvaluation e he a) :=
  (ChartHolomorphicFunctions.affineChartHolomorphicFunction e he a).property

theorem affineChartEvaluation_realSmooth
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin d → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A d) (a : A) :
    ContMDiff 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, ℂ) ∞ (affineChartContinuousEvaluation e he a) :=
  Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex (affineChartEvaluation_complexSmooth e he a)

def affineChartHolomorphicFormMap
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin d → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A d) (n : ℕ) :
    Algebraic.Forms.Form A n →ₗ[ℂ] Holomorphic.DeRhamComplex.forms (Fin d → ℂ) (Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e) n :=
  Holomorphic.Factorization.Smooth.holomorphicFormMap (affineChartContinuousEvaluation e he)
    (affineChartEvaluation_realSmooth e he) (affineChartEvaluation_complexSmooth e he) n

theorem affineChartFunctionCovector_apply
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin d → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A d) (a : A) (x : Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e) (v : Fin d → ℂ) :
    Smooth.SymbolPointwise.functionCovector (affineChartContinuousEvaluation e he)
        (affineChartEvaluation_realSmooth e he) a x
        (fun _ => (Analysis.DifferentialForms.Manifold.OpenEquivalence.openTangentEquiv x).symm v) =
      fderiv ℂ (fun y => e.symm y a) (x : Fin d → ℂ) v := by
  have h := Holomorphic.FunctionDifferential.holomorphicFunctionDifferential_coefficients (ChartHolomorphicFunctions.affineChartHolomorphicFunction e he a) x
    (fun _ => v)
  rw [Holomorphic.DeRhamComplex.inclusion_differential, (ChartHolomorphicFunctions.affineChartHolomorphicFunction_extension e he a x).fderiv_eq] at h
  exact h

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.ChartFormEvaluation
