import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.FiberOrbits
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.HomogeneousTransformations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ChartEvaluationEquality

/-! # Orbit Invariance -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.OrbitInvariance

noncomputable section

/-! Ring points of the balanced frame chart are constant on the orbits
of invertible coordinate transformations and independent unit scalings. -/
open scoped BigOperators Classical
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A] {r m : ℕ}

theorem balancedConfigurationChartEvaluation_invariant (hr : 0 < r)
    (i : Fin m) (v w : Fin m → Fin r → A)
    (a : (Fin r → Fin m) → ℕ) (ha : a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (hv : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) a))
    (hw : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ w) a))
    (T : (Fin r → A) ≃ₗ[A] (Fin r → A)) (s : Fin m → Aˣ)
    (h : ∀ z, w z = (s z : A) • T (v z)) :
    Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i v a ha hv =
      Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i w a ha hw := by
  apply Homogeneous.ChartEvaluationEquality.homogeneousAwayEvaluation_eq_of_cross (Balanced.DeterminantGrading.balancedDeterminantGrading R r m i)
    (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement R a ha)
    (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement_mem_grading R a ha i)
    (Balanced.ConfigurationChartEvaluation.balancedConfigurationPolynomialEvaluation (R := R) v).toRingHom
    (Balanced.ConfigurationChartEvaluation.balancedConfigurationPolynomialEvaluation (R := R) w).toRingHom
    ((Balanced.ConfigurationChartEvaluation.balancedConfigurationPolynomialEvaluation_denominator (R := R) v a ha).symm ▸ hv)
    ((Balanced.ConfigurationChartEvaluation.balancedConfigurationPolynomialEvaluation_denominator (R := R) w a ha).symm ▸ hw)
  intro k p hp
  have hka : k • a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight :=
    (Balanced.ExponentFiniteGeneration.balancedExponentMonoid _).nsmul_mem ha k
  have hp' : p.val ∈ Balanced.MonomialSpan.balancedMonomialDegreeSpan (R := R) (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R)
      DeterminantBlockDegrees.labeledDeterminantWeight i (Balanced.ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight (k • a) i) := by
    rw [Balanced.ExponentCompletion.monomialMultiDegree_nsmul]
    exact hp
  have hq : Balanced.MonomialAlgebra.exponentMonomial (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R) (k • a) ∈
      Balanced.MonomialSpan.balancedMonomialDegreeSpan (R := R) (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R) DeterminantBlockDegrees.labeledDeterminantWeight i
        (Balanced.ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight (k • a) i) :=
    Submodule.subset_span ⟨k • a, ⟨hka, rfl⟩, rfl⟩
  have hc := Balanced.HomogeneousTransformations.balancedHomogeneousPolynomial_cross_invariant hr v T.toLinearMap (fun z => (s z : A))
    (k • a) hka i p.val (Balanced.MonomialAlgebra.exponentMonomial (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R) (k • a)) hp' hq
  have he : (fun jk : Fin m × Fin r => (s jk.1 : A) * T.toLinearMap (v jk.1) jk.2) =
      (fun jk : Fin m × Fin r => w jk.1 jk.2) := by
    funext jk
    exact (congrFun (h jk.1) jk.2).symm
  rw [he, NonvanishingMonomialCompletion.exponentMonomial_nsmul, map_pow, map_pow] at hc
  exact (mul_comm _ _).trans hc.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.OrbitInvariance
