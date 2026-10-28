import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.ConfigurationChartEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ChartEvaluationComposition

/-! # Evaluation Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.EvaluationNaturality

noncomputable section

/-! The ring point of a balanced chart commutes with changing the
coefficient algebra of a vector configuration. -/
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable {B : Type w} [CommRing B] [Algebra R B] {r m : ℕ}

theorem balancedConfigurationPolynomialEvaluation_comp
    (v : Fin m → Fin r → A) (ψ : A →ₐ[R] B) :
    ψ.comp (Balanced.ConfigurationChartEvaluation.balancedConfigurationPolynomialEvaluation (R := R) v) =
      Balanced.ConfigurationChartEvaluation.balancedConfigurationPolynomialEvaluation (R := R) (fun z k => ψ (v z k)) := by
  apply AlgHom.ext
  intro p
  exact MvPolynomial.comp_aeval_apply (fun jk : Fin m × Fin r => v jk.1 jk.2) ψ p.val

theorem balancedConfigurationChartEvaluation_comp
    (i : Fin m) (v : Fin m → Fin r → A)
    (a : (Fin r → Fin m) → ℕ) (ha : a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (hv : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) a))
    (ψ : A →ₐ[R] B)
    (hw : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ (fun z k => ψ (v z k))) a)) :
    ψ.toRingHom.comp (Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i v a ha hv) =
      Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i (fun z k => ψ (v z k)) a ha hw := by
  unfold Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation
  rw [Homogeneous.ChartEvaluationComposition.homogeneousAwayEvaluation_comp]
  have h : ψ.toRingHom.comp (Balanced.ConfigurationChartEvaluation.balancedConfigurationPolynomialEvaluation (R := R) v).toRingHom =
      (Balanced.ConfigurationChartEvaluation.balancedConfigurationPolynomialEvaluation (R := R) (fun z k => ψ (v z k))).toRingHom :=
    congrArg AlgHom.toRingHom (balancedConfigurationPolynomialEvaluation_comp v ψ)
  congr 1

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.EvaluationNaturality
