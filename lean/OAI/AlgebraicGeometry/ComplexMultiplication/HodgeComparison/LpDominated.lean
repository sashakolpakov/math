import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpCoefficients
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Lp Dominated -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpDominated.CM.Construction

noncomputable section

/-! Dominated convergence in actual vector-valued L2 using specified
representatives, with no common-null-set assumption on an uncountable parameter. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology

variable {α F ι : Type*} [MeasurableSpace α] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {μ : Measure α}

theorem l2_norm_sq_integral (u : Lp F 2 μ) : ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq u, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem l2_tendsto_dominated_representatives {l : Filter ι} [l.IsCountablyGenerated]
    (u : ι → Lp F 2 μ) (u₀ : Lp F 2 μ) (f : ι → α → F) (f₀ : α → F)
    (hf : ∀ i, u i =ᵐ[μ] f i) (hf₀ : u₀ =ᵐ[μ] f₀)
    (b : α → ℝ) (hb : MemLp b 2 μ)
    (hbound : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖f i x‖ ≤ b x)
    (hbound₀ : ∀ᵐ x ∂μ, ‖f₀ x‖ ≤ b x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => f i x) l (𝓝 (f₀ x))) :
    Tendsto u l (𝓝 u₀) := by
  have hfm (i : ι) : AEStronglyMeasurable (f i) μ := (Lp.aestronglyMeasurable (u i)).congr (hf i)
  have hf₀m : AEStronglyMeasurable f₀ μ := (Lp.aestronglyMeasurable u₀).congr hf₀
  have hmeas : ∀ᶠ i in l, AEStronglyMeasurable (fun x => ‖f i x - f₀ x‖ ^ 2) μ :=
    Filter.Eventually.of_forall (fun i => ((hfm i).sub hf₀m).norm.aemeasurable.pow_const 2 |>.aestronglyMeasurable)
  have hdom : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖‖f i x - f₀ x‖ ^ 2‖ ≤ 4 * b x ^ 2 := by
    filter_upwards [hbound] with i hi
    filter_upwards [hi, hbound₀] with x hx hx₀
    have hb0 : 0 ≤ b x := (norm_nonneg _).trans hx₀
    have hn : ‖f i x - f₀ x‖ ≤ 2 * b x := (norm_sub_le _ _).trans (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (f i x - f₀ x)]
  have hlim0 : ∀ᵐ x ∂μ, Tendsto (fun i => ‖f i x - f₀ x‖ ^ 2) l (𝓝 (0 : ℝ)) := by
    filter_upwards [hlim] with x hx
    have hx₀ : Tendsto (fun _ : ι => f₀ x) l (𝓝 (f₀ x)) := tendsto_const_nhds
    simpa only [sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
      (hx.sub hx₀).norm.pow 2
  have hint := tendsto_integral_filter_of_dominated_convergence (fun x => 4 * b x ^ 2)
    hmeas hdom (hb.integrable_sq.const_mul 4) hlim0
  have heq (i : ι) : ‖u i - u₀‖ ^ 2 = ∫ x, ‖f i x - f₀ x‖ ^ 2 ∂μ := by
    rw [l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (u i) u₀, hf i, hf₀] with x hsub hx hx₀
    simp only [hsub, Pi.sub_apply, hx, hx₀]
  have hnormsq : Tendsto (fun i => ‖u i - u₀‖ ^ 2) l (𝓝 (0 : ℝ)) := by
    simpa only [heq, integral_zero] using hint
  have hnorm : Tendsto (fun i => ‖u i - u₀‖) l (𝓝 (0 : ℝ)) := by
    have h : Tendsto (fun i => Real.sqrt (‖u i - u₀‖ ^ 2)) l (𝓝 (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp hnormsq
    have heq : (fun i => Real.sqrt (‖u i - u₀‖ ^ 2)) = (fun i => ‖u i - u₀‖) :=
      funext (fun i => Real.sqrt_sq (norm_nonneg (u i - u₀)))
    rwa [heq, Real.sqrt_zero] at h
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpDominated.CM.Construction
