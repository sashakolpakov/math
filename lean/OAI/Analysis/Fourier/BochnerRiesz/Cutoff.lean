import OAI.Analysis.Fourier.BochnerRiesz.Projection
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

/-- A smooth compact annular cutoff, with explicitly separated inner
and outer plateaux. -/
theorem exists_annular_cutoff {n : ℕ} {a b c d : ℝ}
    (ha : 0 < a) (hab : a < b) (hbc : b ≤ c) (hcd : c < d) :
    ∃ χ : Space n → ℂ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (0 : Space n) ∉ tsupport χ ∧
      (∀ ξ, b ≤ ‖ξ‖ → ‖ξ‖ ≤ c → χ ξ = 1) ∧
      (∀ ξ, χ ξ ≠ 0 → a < ‖ξ‖ ∧ ‖ξ‖ < d) := by
  let inner : ContDiffBump (0 : Space n) := ⟨a, b, ha, hab⟩
  let outer : ContDiffBump (0 : Space n) := ⟨c, d, lt_of_lt_of_le (ha.trans hab) hbc, hcd⟩
  let χ : Space n → ℂ := fun ξ ↦ ((1 - inner ξ) * outer ξ : ℝ)
  have hsm : ContDiff ℝ ∞ χ := by
    exact Complex.ofRealCLM.contDiff.comp ((contDiff_const.sub inner.contDiff).mul outer.contDiff)
  have hband (ξ : Space n) (hξ : χ ξ ≠ 0) : a < ‖ξ‖ ∧ ‖ξ‖ < d := by
    constructor
    · by_contra! hsmall
      have hi : inner ξ = 1 := inner.one_of_mem_closedBall (by
        simpa only [mem_closedBall, dist_zero_right] using hsmall)
      exact hξ (by simp [χ, hi])
    · have ho : outer ξ ≠ 0 := by
        intro hz
        exact hξ (by simp [χ, hz])
      have hm : ξ ∈ Function.support outer := ho
      rw [outer.support_eq] at hm
      simpa only [mem_ball, dist_zero_right] using hm
  have hs : tsupport χ ⊆ closedBall (0 : Space n) d := by
    apply closure_minimal _ isClosed_closedBall
    intro ξ hξ
    exact mem_closedBall.mpr (by simpa only [dist_zero_right] using (hband ξ hξ).2.le)
  have hlow : tsupport χ ⊆ {ξ : Space n | a ≤ ‖ξ‖} := by
    apply closure_minimal _ (isClosed_le continuous_const continuous_norm)
    intro ξ hξ
    exact (hband ξ hξ).1.le
  have hc : HasCompactSupport χ :=
    (isCompact_closedBall (0 : Space n) d).of_isClosed_subset isClosed_closure hs
  refine ⟨χ, hsm, hc, ?_, ?_, hband⟩
  · intro hz
    have h := hlow hz
    simp only [Set.mem_ofPred_eq, norm_zero, not_le.mpr ha] at h
  · intro ξ hb' hc'
    have hi : inner ξ = 0 := inner.zero_of_le_dist (by
      simpa only [dist_zero_right] using hb')
    have ho : outer ξ = 1 := outer.one_of_mem_closedBall (by
      simpa only [mem_closedBall, dist_zero_right] using hc')
    simp [χ, hi, ho]

end OAI.Analysis.Fourier.BochnerRiesz
