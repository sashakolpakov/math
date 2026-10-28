import OAI.Analysis.Fourier.WavePackets.ShellDerivatives
import OAI.Analysis.Fourier.Wave.Basic

open OAI.Analysis.Fourier.Wave

namespace OAI.Analysis.Fourier.WavePackets

open Set Metric Filter
open scoped ContDiff Topology

/-- A compact smooth extension of the exact radial Bochner--Riesz
derivative amplitude. Its support stays away from zero frequency and
nonpositive radius, uniformly independently of the shell width. -/
theorem exists_stein_amplitude (n : ℕ) (α : ℝ) :
    ∃ A : ℝ × Space n → ℂ,
      ContDiff ℝ ∞ A ∧ HasCompactSupport A ∧
      (∀ r : ℝ, (r, (0 : Space n)) ∉ tsupport A) ∧
      (∀ r ξ, 1 ≤ r → r ≤ 2 → 1 / 2 ≤ ‖ξ‖ → ‖ξ‖ ≤ 2 →
        A (r, ξ) = (2 * α * ‖ξ‖ ^ 2 * r ^ (-2 * α) *
          (r + ‖ξ‖) ^ (α - 1) : ℝ)) ∧
      (∀ r ξ, A (r, ξ) ≠ 0 → 0 < r ∧ 1 / 4 < ‖ξ‖ ∧ ‖ξ‖ < 3) := by
  let β : ContDiffBump (3 / 2 : ℝ) :=
    { rIn := 1 / 2, rOut := 1, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  let γ : ContDiffBump (0 : Space n) :=
    { rIn := 1 / 4, rOut := 1 / 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  let ζ : ContDiffBump (0 : Space n) :=
    { rIn := 2, rOut := 3, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  let b : ℝ × Space n → ℝ := fun p => β p.1 * ζ p.2 * (1 - γ p.2)
  let A : ℝ × Space n → ℂ := fun p =>
    (b p * (2 * α * ‖p.2‖ ^ 2 * p.1 ^ (-2 * α) * (p.1 + ‖p.2‖) ^ (α - 1)) : ℝ)
  have hb : ContDiff ℝ ∞ b :=
    ((β.contDiff.comp contDiff_fst).mul (ζ.contDiff.comp contDiff_snd)).mul
      (contDiff_const.sub (γ.contDiff.comp contDiff_snd))
  have hA0 {p : ℝ × Space n} (hz : b p = 0) : A p = 0 := by simp [A, hz]
  have hbs {r : ℝ} {ξ : Space n} (hn : b (r, ξ) ≠ 0) :
      0 < r ∧ 1 / 4 < ‖ξ‖ ∧ ‖ξ‖ < 3 := by
    have hβ : β r ≠ 0 := by intro hz; exact hn (by simp [b, hz])
    have hζ : ζ ξ ≠ 0 := by intro hz; exact hn (by simp [b, hz])
    have hγ : γ ξ ≠ 1 := by intro hz; exact hn (by simp [b, hz])
    have hr : |r - 3 / 2| < 1 := by
      have ht : r ∈ Function.support β := hβ
      simpa only [β.support_eq, mem_ball, Real.dist_eq, β] using ht
    have hξ3 : ‖ξ‖ < 3 := by
      have ht : ξ ∈ Function.support ζ := hζ
      simpa only [ζ.support_eq, mem_ball, dist_zero_right, ζ] using ht
    refine ⟨by have := (abs_lt.mp hr).1; linarith, ?_, hξ3⟩
    by_contra! he
    exact hγ (γ.one_of_mem_closedBall (by simpa only [mem_closedBall, dist_zero_right, γ] using he))
  have hsupport : tsupport A ⊆ closedBall (3 / 2 : ℝ) 1 ×ˢ
      {ξ : Space n | 1 / 4 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 3} := by
    apply closure_minimal _ (isClosed_closedBall.prod
      ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)))
    rintro ⟨r, ξ⟩ hn
    have hbn : b (r, ξ) ≠ 0 := fun hz => hn (hA0 hz)
    have hβ : β r ≠ 0 := by intro hz; exact hbn (by simp [b, hz])
    have hr : r ∈ closedBall (3 / 2 : ℝ) 1 := by
      have ht := subset_tsupport (β : ℝ → ℝ) hβ
      simpa only [β.tsupport_eq, β] using ht
    exact ⟨hr, (hbs hbn).2.1.le, (hbs hbn).2.2.le⟩
  refine ⟨A, ?_, ?_, ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    rintro ⟨r, ξ⟩
    by_cases hr : 0 < r
    · by_cases hξ : ξ = 0
      · subst ξ
        apply (show ContDiffAt ℝ ∞ (fun _ : ℝ × Space n => (0 : ℂ)) (r, 0) from
          contDiffAt_const).congr_of_eventuallyEq
        filter_upwards [γ.eventuallyEq_one.comp_tendsto continuousAt_snd] with p hp
        change γ p.2 = 1 at hp
        exact hA0 (p := p) (by simp [b, hp])
      · have hnorm : ContDiffAt ℝ ∞ (fun p : ℝ × Space n => ‖p.2‖) (r, ξ) :=
          (contDiffAt_norm ℝ hξ).comp _ contDiffAt_snd
        have hpow : ContDiffAt ℝ ∞ (fun p : ℝ × Space n => p.1 ^ (-2 * α)) (r, ξ) :=
          contDiffAt_fst.rpow_const_of_ne hr.ne'
        have hsum : ContDiffAt ℝ ∞ (fun p : ℝ × Space n => (p.1 + ‖p.2‖) ^ (α - 1)) (r, ξ) :=
          (contDiffAt_fst.add hnorm).rpow_const_of_ne (by dsimp; positivity)
        exact Complex.ofRealCLM.contDiff.comp_contDiffAt _
          (hb.contDiffAt.mul (((contDiffAt_const.mul (hnorm.pow 2)).mul hpow).mul hsum))
    · have hnot : r ∉ tsupport (β : ℝ → ℝ) := by
        rw [β.tsupport_eq]
        intro h
        have ht : |r - 3 / 2| ≤ 1 := by simpa only [mem_closedBall, Real.dist_eq, β] using h
        have := (abs_le.mp ht).1
        linarith
      apply (show ContDiffAt ℝ ∞ (fun _ : ℝ × Space n => (0 : ℂ)) (r, ξ) from
        contDiffAt_const).congr_of_eventuallyEq
      filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hnot).comp_tendsto continuousAt_fst] with p hp
      change β p.1 = 0 at hp
      exact hA0 (p := p) (by simp [b, hp])
  · apply HasCompactSupport.of_support_subset_isCompact
      ((isCompact_closedBall (3 / 2 : ℝ) 1).prod (isCompact_closedBall (0 : Space n) 3))
    intro p hp
    have ht := hsupport (subset_tsupport A hp)
    exact ⟨ht.1, by simpa only [mem_closedBall, dist_zero_right] using ht.2.2⟩
  · intro r hr
    have ht := (hsupport hr).2.1
    norm_num at ht
  · intro r ξ hr1 hr2 hξ1 hξ2
    have hβ : β r = 1 := β.one_of_mem_closedBall (by
      simp only [mem_closedBall, Real.dist_eq, β]
      exact abs_le.mpr ⟨by linarith, by linarith⟩)
    have hζ : ζ ξ = 1 := ζ.one_of_mem_closedBall (by simpa only [mem_closedBall, dist_zero_right, ζ] using hξ2)
    have hγ : γ ξ = 0 := γ.zero_of_le_dist (by simpa only [dist_zero_right, γ] using hξ1)
    simp only [A, b, hβ, hζ, hγ, sub_zero, mul_one, one_mul]
  · intro r ξ hn
    exact hbs (fun hz => hn (hA0 hz))

end OAI.Analysis.Fourier.WavePackets
