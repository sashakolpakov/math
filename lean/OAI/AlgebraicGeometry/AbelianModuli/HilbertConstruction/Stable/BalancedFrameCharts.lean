import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SparseBalancedFrameCharts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.SupportMonomialCompletion

/-! # Balanced Frame Charts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedFrameCharts

noncomputable section

/-! Every sparse configuration has a balanced frame chart whose
denominator contains every nonzero minor of that configuration. -/
open scoped Classical
universe u
variable {K : Type u} [Field K] {r m : ℕ}

theorem sparseConfiguration_stable_balanced_frame_chart
    (v : Fin m → Fin r → K) (hv : ∀ i, v i ≠ 0) (hr : 2 ≤ r) (hm : 2 ≤ m)
    (hs : ∀ W : Submodule K (Fin r → K), W ≠ ⊤ →
      r * (Finset.univ.filter (fun i => v i ∈ W)).card < m) :
    ∃ (σ : Fin r → Fin m) (e : Fin m) (c : Fin m → Fin r)
      (a : (Fin r → Fin m) → ℕ) (C : Fin m → (Fin r → Fin m) → ℕ),
      a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight ∧
      Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) a ≠ 0 ∧
      Frame.ChartDenominators.frameChartExponent σ e c ≤ a ∧
      (∀ z, C z + Frame.CoordinateExponents.frameCoordinateExponent σ e z (c z) = a) ∧
      ∀ τ, LabeledDeterminantPolynomials.labeledDeterminant τ v ≠ 0 → 0 < a τ := by
  obtain ⟨σ, e, hframe⟩ := SparseBalancedFrameCharts.sparseConfiguration_exists_frame_discriminant v (by omega) hs
  obtain ⟨c, hc⟩ := Frame.ChartDenominators.frame_exists_nonvanishing_chart v hv σ e hframe
  obtain ⟨a, b, ha, hab, han, hapos⟩ := Positive.SupportMonomialCompletion.sparseConfiguration_complete_with_positive_support
    v hv hr hm hs (Frame.ChartDenominators.frameChartExponent σ e c) hc
  have hle : Frame.ChartDenominators.frameChartExponent σ e c ≤ a := by
    rw [← hab]
    intro τ
    exact Nat.le_add_left _ _
  have hC (z : Fin m) : ∃ C, C + Frame.CoordinateExponents.frameCoordinateExponent σ e z (c z) = a :=
    SupportedExponentCompletion.exponent_complement_of_le ((Frame.ChartDenominators.frameCoordinateExponent_le_chart σ e z c).trans hle)
  choose C hC using hC
  exact ⟨σ, e, c, a, C, ha, han, hle, hC, hapos⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedFrameCharts
