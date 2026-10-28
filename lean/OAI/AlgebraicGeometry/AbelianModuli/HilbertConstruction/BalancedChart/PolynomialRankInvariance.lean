import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.FrameRankInvariance
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.OrbitPointEquivalence

/-! # Polynomial Rank Invariance -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.PolynomialRankInvariance

noncomputable section

/-! The polynomial flat-rank condition is well defined on the
balanced chart's actual configuration orbits. Equal chart evaluation
maps give the same rank condition over arbitrary coefficient rings. -/
open scoped Classical
universe u
variable {A : Type u} [CommRing A] {n m : ℕ}

def ConfigurationPolynomialFlatRank (w : Fin m → Fin (n + 1) → A) (D k : ℕ) : Prop :=
  Module.Flat A ((Fin m → A) ⧸ (Matrix.toLin' (Configuration.MonomialMatrix.configurationMonomialMatrix w D)).range) ∧
    ∀ p : PrimeSpectrum A, Module.rankAtStalk (R := A)
      ((Fin m → A) ⧸ (Matrix.toLin' (Configuration.MonomialMatrix.configurationMonomialMatrix w D)).range) p + k = m

theorem configurationPolynomialFlatRank_of_frameOrbit
    (v w : Fin m → Fin (n + 1) → A)
    (T : (Fin (n + 1) → A) ≃ₗ[A] (Fin (n + 1) → A)) (s : Fin m → Aˣ)
    (h : ∀ z, w z = (s z : A) • T (v z)) (D k : ℕ) :
    ConfigurationPolynomialFlatRank w D k ↔ ConfigurationPolynomialFlatRank v D k := by
  have hw : w = fun z j => (s z : A) * T (v z) j :=
    funext (fun z => funext (fun j => congrFun (h z) j))
  rw [hw]
  exact Configuration.FrameRankInvariance.configurationMonomialMatrix_flatRank_frameChange_iff v D T s k m

variable {R : Type u} [CommRing R] [Algebra R A]

theorem balancedChart_equal_evaluation_polynomialFlatRank
    (i : Fin m) (σ : Fin (n + 1) → Fin m) (e : Fin m) (c : Fin m → Fin (n + 1))
    (a : (Fin (n + 1) → Fin m) → ℕ) (C : Fin m → (Fin (n + 1) → Fin m) → ℕ)
    (ha : a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (hC : ∀ z, C z + Frame.CoordinateExponents.frameCoordinateExponent σ e z (c z) = a)
    (hframe : Frame.ChartDenominators.frameDiscriminantExponent σ e ≤ a)
    (v w : Fin m → Fin (n + 1) → A)
    (hv : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) a))
    (hw : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ w) a))
    (heval : Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i v a ha hv =
      Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i w a ha hw) (D k : ℕ) :
    ConfigurationPolynomialFlatRank w D k ↔ ConfigurationPolynomialFlatRank v D k := by
  obtain ⟨T, s, hs⟩ := FiberOrbits.balancedChart_equal_evaluation_implies_same_orbit
    i σ e c a C ha hC hframe v w hv hw heval
  exact configurationPolynomialFlatRank_of_frameOrbit v w T s hs D k

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.PolynomialRankInvariance
