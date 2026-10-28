import OAI.Analysis.Fourier.WavePackets.ShellDerivatives
import OAI.Analysis.Fourier.WavePackets.PartialFourierSmooth

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory Set Metric
open scoped ContDiff

theorem norm_iteratedFDeriv_affine_restriction
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : Y → ℂ} (hf : ContDiff ℝ ∞ f) (L : X →L[ℝ] Y) (a : Y) (j : ℕ) (x : X) :
    ‖iteratedFDeriv ℝ j (fun y => f (a + L y)) x‖ ≤
      ‖iteratedFDeriv ℝ j f (a + L x)‖ * ‖L‖ ^ j := by
  have ht : ContDiff ℝ ∞ (fun y : Y => f (a + y)) := hf.comp (contDiff_const.add contDiff_id)
  change ‖iteratedFDeriv ℝ j ((fun y : Y => f (a + y)) ∘ L) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_right ht x (by simp), iteratedFDeriv_comp_add_left]
  simpa using (iteratedFDeriv ℝ j f (a + L x)).norm_compContinuousLinearMap_le (fun _ => L)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- A common compact spatial support away from zero permits one smooth
replacement of the shell phase on the entire amplitude support. -/
theorem exists_compact_shell_phase {A : ℝ × E → ℂ}
    (hc : HasCompactSupport A) (hz : ∀ r : ℝ, (r, (0 : E)) ∉ tsupport A) :
    ∃ ψ : WithLp 2 (ℝ × E) → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      ∀ z, A (WithLp.ofLp z) ≠ 0 → ψ z = -(z.fst - ‖z.snd‖) := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E
  have hS : IsCompact (Prod.snd '' tsupport A) := hc.image continuous_snd
  have hzero : (0 : E) ∉ Prod.snd '' tsupport A := by
    rintro ⟨⟨r, x⟩, hx, he⟩
    change x = 0 at he
    subst x
    exact hz r hx
  obtain ⟨ρ, hρ, _, heρ⟩ := exists_smooth_compact_norm_replacement hS hzero
  have hc' : HasCompactSupport (fun z : WithLp 2 (ℝ × E) => A (WithLp.ofLp z)) :=
    hc.comp_homeomorph e.toHomeomorph
  obtain ⟨R, hR, hRb⟩ := hc'.isBounded.exists_pos_norm_le
  let β : ContDiffBump (0 : WithLp 2 (ℝ × E)) :=
    { rIn := R + 1, rOut := R + 2, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  refine ⟨fun z => -(β z * (z.fst - ρ z.snd)), ?_, ?_, ?_⟩
  · exact (β.contDiff.mul ((contDiff_fst.comp e.contDiff).sub
      (hρ.comp (contDiff_snd.comp e.contDiff)))).neg
  · exact β.hasCompactSupport.mul_right.neg
  · intro z hzA
    have hb : β z = 1 := by
      apply β.one_of_mem_closedBall
      rw [mem_closedBall, dist_zero_right]
      exact (hRb z (subset_tsupport _ hzA)).trans (by dsimp [β]; linarith)
    have hρz := heρ ⟨WithLp.ofLp z, subset_tsupport A hzA, rfl⟩
    change ρ z.snd = ‖z.snd‖ at hρz
    simp only [hb, one_mul, hρz]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Polynomial shell-width control remains uniform for a genuinely
radius-dependent compact smooth amplitude. -/
theorem uniform_amplitude_shell_derivative_bound {A : ℝ × E → ℂ}
    (ha : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (hz : ∀ r : ℝ, (r, (0 : E)) ∉ tsupport A)
    (φ : SchwartzMap ℝ ℂ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x,
      ‖iteratedFDeriv ℝ N (fun ξ => A (r, ξ) * φ ((r - ‖ξ‖) / δ)) x‖ ≤
        C * (δ⁻¹) ^ N := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E
  let a : WithLp 2 (ℝ × E) → ℂ := fun z => A (WithLp.ofLp z)
  have ha' : ContDiff ℝ ∞ a := ha.comp e.contDiff
  have hc' : HasCompactSupport a := hc.comp_homeomorph e.toHomeomorph
  obtain ⟨ψ, hψ, hsψ, heψ⟩ := exists_compact_shell_phase hc hz
  obtain ⟨C, hC, hb⟩ := uniform_scaled_shell_derivative_bound hψ hsψ ha' hc' φ N
  let L : E →L[ℝ] WithLp 2 (ℝ × E) :=
    e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ ℝ E)
  refine ⟨C * ‖L‖ ^ N, by positivity, ?_⟩
  intro r δ hδ hδone x
  let F : WithLp 2 (ℝ × E) → ℂ := fun z => φ ((0 - ψ z) / δ) * a z
  have hF : ContDiff ℝ ∞ F := ((φ.smooth ⊤).comp ((contDiff_const.sub hψ).div_const δ)).mul ha'
  have he (ξ : E) : F (e.symm (r, 0) + L ξ) = A (r, ξ) * φ ((r - ‖ξ‖) / δ) := by
    have hp : e.symm (r, 0) + L ξ = e.symm (r, ξ) := by
      dsimp [L]
      rw [← map_add]
      simp
    rw [hp]
    by_cases hzA : A (r, ξ) = 0
    · simp [F, a, e, hzA]
    · have hh := heψ (e.symm (r, ξ)) hzA
      simpa [F, a, e, hh, mul_comm] using congrArg (fun t => φ ((0 - t) / δ) * A (r, ξ)) hh
  have hb' := hb 0 δ hδ hδone (e.symm (r, 0) + L x)
  have hrest := norm_iteratedFDeriv_affine_restriction hF L (e.symm (r, 0)) N x
  rw [show (fun y => F (e.symm (r, 0) + L y)) =
      (fun ξ => A (r, ξ) * φ ((r - ‖ξ‖) / δ)) by funext ξ; exact he ξ] at hrest
  exact hrest.trans (by nlinarith [mul_le_mul_of_nonneg_right hb' (pow_nonneg (norm_nonneg L) N)])

end OAI.Analysis.Fourier.WavePackets
