import Mathlib

namespace OAI.Analysis.PDE.Concentration

open Set Metric

/-- The continuous image of a compact convex parameter set has uniformly
bounded finite chains at every fixed spatial resolution. -/
theorem compact_convex_image_uniform_chain
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {F : Type*} [PseudoMetricSpace F] {K : Set P} (hK : IsCompact K)
    (hc : Convex ℝ K) {φ : P → F} (hφ : ContinuousOn φ K)
    {s : ℝ} (hs : 0 < s) : ∃ N : ℕ, 0 < N ∧
      ∀ p ∈ K, ∀ q ∈ K, ∃ γ : ℕ → F,
        γ 0 = φ p ∧ γ N = φ q ∧ (∀ k ≤ N, γ k ∈ φ '' K) ∧
        (∀ k < N, dist (γ (k + 1)) (γ k) ≤ s) := by
  obtain ⟨δ, hδ, hδmap⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hφ) s hs
  obtain ⟨M, hM, hMb⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * M / δ)
  have hNr : (0 : ℝ) < N := (by positivity : (0 : ℝ) < 2 * M / δ).trans hN
  have hNn : 0 < N := by exact_mod_cast hNr
  refine ⟨N, hNn, ?_⟩
  intro p hp q hq
  let v : ℕ → P := fun k => AffineMap.lineMap p q ((k : ℝ) / N)
  refine ⟨fun k => φ (v k), ?_, ?_, ?_, ?_⟩
  · simp [v]
  · simp [v, hNn.ne']
  · intro k hk
    refine ⟨v k, ?_, rfl⟩
    apply hc.lineMap_mem hp hq
    constructor
    · positivity
    · exact (div_le_one hNr).mpr (by exact_mod_cast hk)
  · intro k hk
    have hv (j : ℕ) (hj : j ≤ N) : v j ∈ K := by
      apply hc.lineMap_mem hp hq
      exact ⟨by positivity, (div_le_one hNr).mpr (by exact_mod_cast hj)⟩
    apply le_of_lt (hδmap _ (hv _ (Nat.succ_le_of_lt hk)) _ (hv _ hk.le) ?_)
    have hpq : dist p q ≤ 2 * M := by
      have hd := norm_sub_le p q
      rw [dist_eq_norm]
      linarith [hMb p hp, hMb q hq]
    have he : dist (((k + 1 : ℕ) : ℝ) / N) ((k : ℝ) / N) = 1 / N := by
      rw [Real.dist_eq]
      have ha : (((k + 1 : ℕ) : ℝ) / N) - ((k : ℝ) / N) = 1 / N := by
        push_cast
        ring
      rw [ha, abs_of_pos (by positivity)]
    change dist (AffineMap.lineMap p q _) (AffineMap.lineMap p q _) < δ
    rw [dist_lineMap_lineMap, he]
    calc
      1 / (N : ℝ) * dist p q ≤ 1 / (N : ℝ) * (2 * M) :=
        mul_le_mul_of_nonneg_left hpq (by positivity)
      _ < δ := by
        have h := (div_lt_iff₀ hδ).mp hN
        rw [div_mul_eq_mul_div, one_mul]
        apply (div_lt_iff₀ hNr).mpr
        nlinarith

end OAI.Analysis.PDE.Concentration
