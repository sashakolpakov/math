import OAI.Analysis.Fourier.BochnerRiesz.Cutoff

open OAI.Analysis.Fourier.Wave

/-! Nested fixed annular cutoffs for the cycles-frequency shell interval. -/

namespace OAI.Analysis.Fourier.SquareFunction

open scoped ContDiff

theorem exists_stein_annular_cutoffs (n : ℕ) :
    ∃ χ ψ : Space n → ℂ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ (0 : Space n) ∉ tsupport χ ∧
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ (0 : Space n) ∉ tsupport ψ ∧
      (∀ ξ, 1 / 2 ≤ ‖ξ‖ → ‖ξ‖ ≤ 3 → χ ((2 * Real.pi) • ξ) = 1) ∧
      (∀ ξ, χ ξ ≠ 0 → ψ ξ = 1) ∧
      (∀ ξ, ψ ξ ≠ 0 → (2 : ℝ) ^ (-(6 : ℤ)) ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ (2 : ℝ) ^ (6 : ℤ)) := by
  have hπ := Real.pi_pos
  obtain ⟨χ, hχ, hcχ, hzχ, hχone, hχsupp⟩ :=
    OAI.Analysis.Fourier.BochnerRiesz.exists_annular_cutoff (n := n)
      (a := Real.pi / 2) (b := Real.pi) (c := 6 * Real.pi) (d := 8 * Real.pi)
      (by positivity) (by linarith) (by linarith) (by linarith)
  obtain ⟨ψ, hψ, hcψ, hzψ, hψone, hψsupp⟩ :=
    OAI.Analysis.Fourier.BochnerRiesz.exists_annular_cutoff (n := n)
      (a := Real.pi / 4) (b := Real.pi / 2) (c := 8 * Real.pi) (d := 16 * Real.pi)
      (by positivity) (by linarith) (by linarith) (by linarith)
  refine ⟨χ, ψ, hχ, hcχ, hzχ, hψ, hcψ, hzψ, ?_, ?_, ?_⟩
  · intro ξ hlo hhi
    apply hχone
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      nlinarith
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      nlinarith
  · intro ξ hξ
    exact hψone ξ (hχsupp ξ hξ).1.le (hχsupp ξ hξ).2.le
  · intro ξ hξ
    obtain ⟨hlo, hhi⟩ := hψsupp ξ hξ
    norm_num
    constructor
    · linarith [Real.pi_gt_three]
    · linarith [Real.pi_lt_four]

theorem exists_stein_boundary_cutoffs (n : ℕ) :
    ∃ χ ψ : Space n → ℂ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ (0 : Space n) ∉ tsupport ψ ∧
      (∀ ξ, 1 / 4 ≤ ‖ξ‖ → ‖ξ‖ ≤ 3 → χ ((2 * Real.pi) • ξ) = 1) ∧
      (∀ ξ, χ ξ ≠ 0 → ψ ξ = 1) ∧
      (∀ ξ, ψ ξ ≠ 0 → (2 : ℝ) ^ (-(6 : ℤ)) ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ (2 : ℝ) ^ (6 : ℤ)) := by
  have hπ := Real.pi_pos
  obtain ⟨χ, hχ, hcχ, _, hχone, hχsupp⟩ :=
    OAI.Analysis.Fourier.BochnerRiesz.exists_annular_cutoff (n := n)
      (a := Real.pi / 4) (b := Real.pi / 2) (c := 6 * Real.pi) (d := 8 * Real.pi)
      (by positivity) (by linarith) (by linarith) (by linarith)
  obtain ⟨ψ, hψ, hcψ, hzψ, hψone, hψsupp⟩ :=
    OAI.Analysis.Fourier.BochnerRiesz.exists_annular_cutoff (n := n)
      (a := Real.pi / 8) (b := Real.pi / 4) (c := 8 * Real.pi) (d := 16 * Real.pi)
      (by positivity) (by linarith) (by linarith) (by linarith)
  refine ⟨χ, ψ, hχ, hcχ, hψ, hcψ, hzψ, ?_, ?_, ?_⟩
  · intro ξ hlo hhi
    apply hχone
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      nlinarith
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      nlinarith
  · intro ξ hξ
    exact hψone ξ (hχsupp ξ hξ).1.le (hχsupp ξ hξ).2.le
  · intro ξ hξ
    obtain ⟨hlo, hhi⟩ := hψsupp ξ hξ
    norm_num
    constructor
    · linarith [Real.pi_gt_three]
    · linarith [Real.pi_lt_four]

end OAI.Analysis.Fourier.SquareFunction
