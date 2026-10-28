import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpDominated
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct

/-! # Coefficient Convergence -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoefficientConvergence.CM.Construction

noncomputable section

/-! Strong L2 convergence of actual bounded coefficient fields from their
pointwise convergence, for use in differentiating the weak equation. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology

variable {α F ι : Type*} [MeasurableSpace α]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {μ : Measure α}

theorem boundedFieldLp_tendsto {l : Filter ι} [l.IsCountablyGenerated]
    (A : ι → α → F →L[ℝ] F) (B : α → F →L[ℝ] F)
    (hA : ∀ i, AEStronglyMeasurable (A i) μ) (hB : AEStronglyMeasurable B μ)
    {C : ℝ} (hC : ∀ i, ∀ᵐ x ∂μ, ‖A i x‖ ≤ C) (hC₀ : ∀ᵐ x ∂μ, ‖B x‖ ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => A i x) l (𝓝 (B x))) (u : Lp F 2 μ) :
    Tendsto (fun i => LpCoefficients.CM.Construction.boundedFieldLp (A i) (hA i) (hC i) u) l
      (𝓝 (LpCoefficients.CM.Construction.boundedFieldLp B hB hC₀ u)) := by
  apply LpDominated.CM.Construction.l2_tendsto_dominated_representatives
    (fun i => LpCoefficients.CM.Construction.boundedFieldLp (A i) (hA i) (hC i) u) (LpCoefficients.CM.Construction.boundedFieldLp B hB hC₀ u)
    (fun i x => A i x (u x)) (fun x => B x (u x))
    (fun i => LpCoefficients.CM.Construction.boundedFieldLp_coe (A i) (hA i) (hC i) u) (LpCoefficients.CM.Construction.boundedFieldLp_coe B hB hC₀ u)
    (fun x => C * ‖u x‖) ((Lp.memLp u).norm.const_smul C)
  · apply Filter.Eventually.of_forall
    intro i
    filter_upwards [hC i] with x hx
    exact ((A i x).le_opNorm _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  · filter_upwards [hC₀] with x hx
    exact ((B x).le_opNorm _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  · filter_upwards [hlim] with x hx
    exact ((ContinuousLinearMap.apply ℝ F (u x)).continuous.tendsto (B x)).comp hx

theorem boundedFieldLp_tendsto_varying {l : Filter ι} [l.IsCountablyGenerated]
    (A : ι → α → F →L[ℝ] F) (B : α → F →L[ℝ] F)
    (hA : ∀ i, AEStronglyMeasurable (A i) μ) (hB : AEStronglyMeasurable B μ)
    {C : ℝ} (hC : ∀ i, ∀ᵐ x ∂μ, ‖A i x‖ ≤ C) (hC₀ : ∀ᵐ x ∂μ, ‖B x‖ ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => A i x) l (𝓝 (B x)))
    (u : ι → Lp F 2 μ) (u₀ : Lp F 2 μ) (hu : Tendsto u l (𝓝 u₀)) :
    Tendsto (fun i => LpCoefficients.CM.Construction.boundedFieldLp (A i) (hA i) (hC i) (u i)) l
      (𝓝 (LpCoefficients.CM.Construction.boundedFieldLp B hB hC₀ u₀)) := by
  let M := fun i => LpCoefficients.CM.Construction.boundedFieldLp (p := 2) (A i) (hA i) (hC i)
  have hnorm : Tendsto (fun i => ‖M i (u i - u₀)‖) l (𝓝 (0 : ℝ)) := by
    have hupper : Tendsto (fun i => C * ‖u i - u₀‖) l (𝓝 (0 : ℝ)) := by
      have hc : Tendsto (fun _ : ι => C) l (𝓝 C) := tendsto_const_nhds
      have hc₀ : Tendsto (fun _ : ι => u₀) l (𝓝 u₀) := tendsto_const_nhds
      simpa only [sub_self, norm_zero, mul_zero] using
        (hc.mul (hu.sub hc₀).norm)
    exact squeeze_zero (fun i => norm_nonneg _) (fun i =>
      LpCoefficients.CM.Construction.boundedFieldLinear_norm_le (A i) (hA i) (hC i) (u i - u₀)) hupper
  have hzero : Tendsto (fun i => M i (u i - u₀)) l (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [sub_zero] using hnorm
  have hfixed := boundedFieldLp_tendsto A B hA hB hC hC₀ hlim u₀
  change Tendsto (fun i => M i u₀) l (𝓝 (LpCoefficients.CM.Construction.boundedFieldLp B hB hC₀ u₀)) at hfixed
  have h := hzero.add hfixed
  have heq (i : ι) : M i (u i - u₀) + M i u₀ = M i (u i) := by
    rw [map_sub, sub_add_cancel]
  simpa only [heq, zero_add] using h

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoefficientConvergence.CM.Construction
