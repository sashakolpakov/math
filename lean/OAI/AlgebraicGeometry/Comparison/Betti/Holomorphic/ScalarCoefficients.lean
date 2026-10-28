import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ChartCoefficients
import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF

/-! # Scalar Coefficients -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ScalarCoefficients

noncomputable section

/-! Every actual scalar coordinate coefficient is a smooth holomorphic function. -/

open scoped _root_.Manifold ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def complexCovectorEvaluation {n : ℕ} (v : Fin n → E) :
    (E [⋀^Fin n]→L[ℝ] ℂ) →L[ℂ] ℂ where
  toLinearMap :=
    { toFun := fun covector => covector v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  cont := (ContinuousAlternatingMap.apply ℝ E ℂ v).continuous

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M] {n : ℕ}

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

theorem form_scalarCoefficient_holomorphic (a : DeRhamComplex.forms E M n)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) (v : Fin n → E) :
    ContDiffOn ℂ ∞ (fun y => (DeRhamComplex.inclusion E M n a).val.inChart e y v) e.target := by
  apply Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF.Constructions.HolomorphicDerivative.contDiffOn_infty_of_differentiableOn e.open_target
  intro y hy
  exact ((complexCovectorEvaluation v).differentiableAt.comp y
    (ChartCoefficients.form_coefficients_complex a e he hy)).differentiableWithinAt

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ScalarCoefficients
