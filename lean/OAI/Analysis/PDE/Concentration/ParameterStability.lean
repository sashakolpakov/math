import OAI.Analysis.PDE.Concentration.PatchVolume

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Green

theorem transverse_sum_sq_bound {d : ℕ} {v : Fin d → ℂ} {r : ℝ}
    (hb : ∀ i, ‖v i‖ ≤ r / (d + 1)) : (∑ i, ‖v i‖ ^ 2) ≤ r ^ 2 := by
  have hs : (∑ i, ‖v i‖ ^ 2) ≤ (d : ℝ) * (r / (d + 1)) ^ 2 := by
    have he := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      pow_le_pow_left₀ (norm_nonneg _) (hb i) 2)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using he
  apply hs.trans
  rw [div_pow, ← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((d : ℝ) + 1) ^ 2)).mpr
  have hd : (d : ℝ) ≤ ((d : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) d]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right hd (sq_nonneg r)

/-- A uniformly small displacement in the normalized coordinates stays in
the larger Gaussian-recovery patch and remains strictly inside the fiber. -/
theorem outputParameterPatch_stable {d : ℕ} {γ : ℝ}
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1 / 100) {u v : Option (Fin d) → ℂ}
    (hu : u ∈ outputParameterPatch d γ)
    (hclose : ‖v - u‖ ≤ γ / (4 * ((d : ℝ) + 1))) :
    ‖v none‖ ≤ 1 / 100 ∧ (∑ i : Fin d, ‖v (some i)‖ ^ 2) ≤ 4 * γ ^ 2 ∧
      v ∈ OAI.Analysis.PDE.Green.openFiberParameterBall d := by
  have hnorm (i : Option (Fin d)) : ‖v i‖ ≤ ‖u i‖ + ‖v - u‖ := by
    calc
      _ = ‖(v i - u i) + u i‖ := by rw [sub_add_cancel]
      _ ≤ ‖v i - u i‖ + ‖u i‖ := norm_add_le _ _
      _ ≤ ‖v - u‖ + ‖u i‖ := by
        have he : ‖v i - u i‖ ≤ ‖v - u‖ := norm_le_pi_norm (v - u) i
        linarith
      _ = _ := add_comm _ _
  have hden : 0 < (d : ℝ) + 1 := by positivity
  have hsmall : γ / (4 * ((d : ℝ) + 1)) ≤ 1 / 400 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hden)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hsmaller : γ / (4 * ((d : ℝ) + 1)) ≤ γ / ((d : ℝ) + 1) := by
    apply div_le_div_of_nonneg_left hγ hden
    nlinarith
  have hn : ‖v none‖ ≤ 1 / 100 := by
    have := (outputParameterPatch_mem.mp hu).1
    linarith [hnorm none, hclose.trans hsmall]
  have hv : ∀ i : Fin d, ‖v (some i)‖ ≤ (2 * γ) / ((d : ℝ) + 1) := by
    intro i
    have hi := (outputParameterPatch_mem.mp hu).2 i
    have hm := hnorm (some i)
    have hh := hclose.trans hsmaller
    rw [mul_div_assoc]
    linarith
  have hs : (∑ i : Fin d, ‖v (some i)‖ ^ 2) ≤ 4 * γ ^ 2 := by
    have he := transverse_sum_sq_bound hv
    nlinarith
  refine ⟨hn, hs, ?_⟩
  change (∑ i, ‖v i‖ ^ 2) < (1 / 100 : ℝ)
  rw [Fintype.sum_option]
  nlinarith [norm_nonneg (v none)]

end OAI.Analysis.PDE.Concentration
