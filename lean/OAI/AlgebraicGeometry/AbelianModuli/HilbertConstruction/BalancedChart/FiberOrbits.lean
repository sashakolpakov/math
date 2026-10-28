import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.OrbitNormalization

/-! # Fiber Orbits -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.FiberOrbits

noncomputable section

/-! Two configurations defining the same ring point of a balanced frame
chart differ by a common invertible linear map and unit point scalings. -/
open scoped Classical
universe u v
variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A] {r m : ℕ}

theorem balancedChart_equal_evaluation_implies_same_orbit
    (i : Fin m) (σ : Fin r → Fin m) (e : Fin m) (c : Fin m → Fin r)
    (a : (Fin r → Fin m) → ℕ) (C : Fin m → (Fin r → Fin m) → ℕ)
    (ha : a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (hC : ∀ z, C z + Frame.CoordinateExponents.frameCoordinateExponent σ e z (c z) = a)
    (hframe : Frame.ChartDenominators.frameDiscriminantExponent σ e ≤ a)
    (v w : Fin m → Fin r → A)
    (hv : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) a))
    (hw : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ w) a))
    (heq : Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i v a ha hv =
      Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i w a ha hw) :
    ∃ T : (Fin r → A) ≃ₗ[A] (Fin r → A), ∃ s : Fin m → Aˣ,
      ∀ z, w z = (s z : A) • T (v z) := by
  obtain ⟨T₁, s₁, h₁⟩ := OrbitNormalization.balancedChartEvaluation_is_frame_normalization
    (R := R) i σ e c a C ha hC hframe v hv
  obtain ⟨T₂, s₂, h₂⟩ := OrbitNormalization.balancedChartEvaluation_is_frame_normalization
    (R := R) i σ e c a C ha hC hframe w hw
  have hn (z : Fin m) : (s₁ z : A) • T₁ (v z) = (s₂ z : A) • T₂ (w z) := by
    funext k
    exact (h₁ z k).symm.trans ((congrArg
      (fun χ : Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i a ha →+* A =>
        χ (Balanced.FrameChartNormalization.balancedFrameChartVectors R i σ e c a C ha hC z k)) heq).trans (h₂ z k))
  refine ⟨T₁.trans T₂.symm, fun z => (s₂ z)⁻¹ * s₁ z, ?_⟩
  intro z
  apply T₂.injective
  rw [map_smul]
  change T₂ (w z) = (↑((s₂ z)⁻¹ * s₁ z) : A) • T₂ (T₂.symm (T₁ (v z)))
  rw [T₂.apply_symm_apply, Units.val_mul, mul_smul, hn, ← mul_smul,
    Units.inv_mul, one_smul]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.FiberOrbits
