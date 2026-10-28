import OAI.Geometry.Nikodym.ProjectiveTube
import Mathlib.Analysis.SpecificLimits.Basic

open Set Metric
open scoped Topology

noncomputable section
namespace OAI.Geometry.Nikodym

def dyadicRadius (j : ℕ) : ℝ := (1/2 : ℝ)^j

theorem dyadicRadius_pos (j : ℕ) : 0 < dyadicRadius j := pow_pos (by norm_num) _

theorem dyadicRadius_le_one (j : ℕ) : dyadicRadius j ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

theorem exists_dyadic_band {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ j : ℕ, dyadicRadius j ≤ s ∧ s ≤ 2 * dyadicRadius j := by
  have he : ∃ j : ℕ, dyadicRadius j ≤ s := by
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hs (by norm_num : (1/2 : ℝ) < 1)
    exact ⟨j, hj.le⟩
  let j := Nat.find he
  refine ⟨j, Nat.find_spec he, ?_⟩
  cases hj : j with
  | zero => simp only [dyadicRadius, pow_zero]; linarith
  | succ k =>
    have hk : ¬dyadicRadius k ≤ s := Nat.find_min he (by omega)
    have hk' : s < dyadicRadius k := lt_of_not_ge hk
    have hpow : 2 * dyadicRadius (k+1) = dyadicRadius k := by
      simp only [dyadicRadius, pow_succ]
      ring
    rw [hpow]
    exact hk'.le

/-- A finite dyadic annular decomposition, with all retained radii at
least δ.  The discarded center has radius 2δ. -/
theorem exists_finite_dyadic_decomposition {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, dyadicRadius N < δ ∧ ∀ s : ℝ, |s| ≤ 1 →
      |s| ≤ 2*δ ∨ ∃ j < N, δ ≤ dyadicRadius j ∧
        (s ∈ Icc (dyadicRadius j) (2*dyadicRadius j) ∨
          -s ∈ Icc (dyadicRadius j) (2*dyadicRadius j)) := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1/2 : ℝ) < 1)
  change dyadicRadius N < δ at hN
  refine ⟨N, hN, ?_⟩
  intro s hs
  by_cases hsmall : |s| ≤ 2*δ
  · exact Or.inl hsmall
  have hs0 : 0 < |s| := by linarith
  obtain ⟨j, hj1, hj2⟩ := exists_dyadic_band hs0 hs
  have hjδ : δ ≤ dyadicRadius j := by linarith
  have hjN : j < N := by
    by_contra! hNj
    have hp : dyadicRadius j ≤ dyadicRadius N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hNj
    linarith
  refine Or.inr ⟨j, hjN, hjδ, ?_⟩
  rcases le_total 0 s with hpos | hneg
  · exact Or.inl (by simpa only [mem_Icc, abs_of_nonneg hpos] using And.intro hj1 hj2)
  · exact Or.inr (by simpa only [mem_Icc, abs_of_nonpos hneg] using And.intro hj1 hj2)

end OAI.Geometry.Nikodym
