import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.ConfigurationChartEvaluation

/-! # Orbit Normalization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.OrbitNormalization

noncomputable section

/-! The value of the universal normalized configuration is related to
every configuration in the chart by an invertible linear transformation
and one unit scalar for each marked point. -/
open scoped Classical
universe u v
variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A] {r m : ℕ}

theorem balancedChartEvaluation_is_frame_normalization
    (i : Fin m) (σ : Fin r → Fin m) (e : Fin m) (c : Fin m → Fin r)
    (a : (Fin r → Fin m) → ℕ) (C : Fin m → (Fin r → Fin m) → ℕ)
    (ha : a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (hC : ∀ z, C z + Frame.CoordinateExponents.frameCoordinateExponent σ e z (c z) = a)
    (hframe : Frame.ChartDenominators.frameDiscriminantExponent σ e ≤ a)
    (w : Fin m → Fin r → A) (hw : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ w) a)) :
    ∃ T : (Fin r → A) ≃ₗ[A] (Fin r → A), ∃ s : Fin m → Aˣ, ∀ z k,
      Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i w a ha hw
          (Balanced.FrameChartNormalization.balancedFrameChartVectors R i σ e c a C ha hC z k) =
        (s z : A) * T (w z) k := by
  have hΔ : IsUnit (ProjectiveFrame.Discriminant.projectiveFrameDiscriminant (Pi.basisFun A (Fin r))
      (fun j => w (σ j)) (w e)) := by
    rw [← Frame.ChartDenominators.frameDiscriminantExponent_monomial]
    exact Unit.MonomialFractions.exponentMonomial_isUnit_of_le _ hframe hw
  let T := DeterminantFrameLinearMap.determinantFrameLinearEquiv (Pi.basisFun A (Fin r)) (fun j => w (σ j)) (w e) hΔ
  have hu (z : Fin m) : IsUnit (T (w z) (c z)) := by
    change IsUnit (DeterminantFrameLinearMap.determinantFrameLinearMap (Pi.basisFun A (Fin r))
      (fun j => w (σ j)) (w e) (w z) (c z))
    rw [← Frame.CoordinateMonomials.frameCoordinateExponent_linearMap]
    apply Unit.MonomialFractions.exponentMonomial_isUnit_of_le _ _ hw
    intro τ
    calc
      Frame.CoordinateExponents.frameCoordinateExponent σ e z (c z) τ ≤ C z τ + Frame.CoordinateExponents.frameCoordinateExponent σ e z (c z) τ :=
        Nat.le_add_left _ _
      _ = a τ := congrFun (hC z) τ
  refine ⟨T, fun z => (hu z).unit⁻¹, ?_⟩
  intro z k
  apply (hu z).mul_right_cancel
  calc
    _ = T (w z) k := Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation_frame_cross i σ e c a C ha hC w hw z k
    _ = (↑(hu z).unit⁻¹ * T (w z) (c z)) * T (w z) k := by rw [(hu z).val_inv_mul, one_mul]
    _ = (↑(hu z).unit⁻¹ * T (w z) k) * T (w z) (c z) := by ring

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.OrbitNormalization
