import OAI.Analysis.Fourier.WavePackets.ShellDerivatives

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory Set FourierTransform
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def annularShellSchwartz {b : E → ℂ} (hb : ContDiff ℝ ∞ b)
    (hs : HasCompactSupport b) (hz : (0 : E) ∉ tsupport b)
    (φ : SchwartzMap ℝ ℂ) (r δ : ℝ) : SchwartzMap E ℂ :=
  (hasCompactSupport_annularShellSymbol hs φ r δ).toSchwartzMap
    (contDiff_annularShellSymbol hb hs hz φ r δ)

theorem uniform_annularShell_seminorm_bound {b : E → ℂ} (hb : ContDiff ℝ ∞ b)
    (hs : HasCompactSupport b) (hz : (0 : E) ∉ tsupport b)
    (φ : SchwartzMap ℝ ℂ) (k N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r δ : ℝ, 0 < δ → δ ≤ 1 →
      SchwartzMap.seminorm ℝ k N (annularShellSchwartz hb hs hz φ r δ) ≤ C * (δ⁻¹) ^ N := by
  obtain ⟨D, hD, hbnd⟩ := uniform_annularShell_derivative_bound hb hs hz φ N
  obtain ⟨R, hR, hRS⟩ := hs.isBounded.exists_pos_norm_le
  refine ⟨R ^ k * D, by positivity, ?_⟩
  intro r δ hδ hδone
  apply SchwartzMap.seminorm_le_bound _ _ _ _ (by positivity)
  intro x
  change ‖x‖ ^ k * ‖iteratedFDeriv ℝ N (annularShellSymbol b φ r δ) x‖ ≤ _
  by_cases hx : x ∈ tsupport b
  · calc
      _ ≤ R ^ k * (D * (δ⁻¹) ^ N) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hRS x hx) k)
          (hbnd r δ hδ hδone x) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · have hzD : iteratedFDeriv ℝ N (annularShellSymbol b φ r δ) x = 0 := by
      by_contra hn
      exact hx (tsupport_mul_subset_right (support_iteratedFDeriv_subset N hn))
    rw [hzD, norm_zero, mul_zero]
    positivity

theorem uniform_annularShell_finite_seminorm_bound {b : E → ℂ} (hb : ContDiff ℝ ∞ b)
    (hs : HasCompactSupport b) (hz : (0 : E) ∉ tsupport b)
    (φ : SchwartzMap ℝ ℂ) (s : Finset (ℕ × ℕ)) :
    ∃ Q : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ r δ : ℝ, 0 < δ → δ ≤ 1 →
      s.sup (schwartzSeminormFamily ℝ E ℂ) (annularShellSchwartz hb hs hz φ r δ) ≤
        C * (δ⁻¹) ^ Q := by
  choose C hC hbnd using fun m : ℕ × ℕ => uniform_annularShell_seminorm_bound hb hs hz φ m.1 m.2
  refine ⟨s.sup Prod.snd, ∑ m ∈ s, C m, Finset.sum_nonneg (fun m _ => hC m), ?_⟩
  intro r δ hδ hδone
  calc
    _ ≤ ∑ m ∈ s, schwartzSeminormFamily ℝ E ℂ m (annularShellSchwartz hb hs hz φ r δ) := by
      have h := (Seminorm.finset_sup_le_sum (schwartzSeminormFamily ℝ E ℂ) s)
        (annularShellSchwartz hb hs hz φ r δ)
      change _ ≤ FunLike.coeAddMonoidHom _ _ _ (∑ m ∈ s, schwartzSeminormFamily ℝ E ℂ m)
        (annularShellSchwartz hb hs hz φ r δ) at h
      simp only [map_sum, Finset.sum_apply] at h
      convert h using 1
      congr 1
    _ ≤ ∑ m ∈ s, C m * (δ⁻¹) ^ (s.sup Prod.snd) := by
      apply Finset.sum_le_sum
      intro m hm
      exact (hbnd m r δ hδ hδone).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ ((one_le_inv₀ hδ).2 hδone) (Finset.le_sup hm)) (hC m))
    _ = _ := by rw [Finset.sum_mul]

end OAI.Analysis.Fourier.WavePackets
