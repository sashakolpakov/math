import OAI.Analysis.Fourier.WavePackets.AngularRescaling

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter
open scoped ContDiff Topology ENNReal FourierTransform

theorem tsupport_angularChartSymbol_subset {d : ℕ}
    (b : Space (d + 1) → ℂ) (γ : ℝ) (c : Fin d → ℝ) :
    tsupport (angularChartSymbol b γ c) ⊆ tsupport b := by
  apply closure_minimal _ (isClosed_tsupport b)
  intro ξ hξ
  apply subset_tsupport b
  intro hz
  exact hξ (by simp [angularChartSymbol, hz])

theorem contDiff_angularChartSymbol {d : ℕ} {b : Space (d + 1) → ℂ}
    (hb : ContDiff ℝ ∞ b) {a : ℝ} (ha : 0 < a)
    (hs : ∀ ξ ∈ tsupport b, a ≤ ξ 0) {γ : ℝ} (hγ : γ ≠ 0) (c : Fin d → ℝ) :
    ContDiff ℝ ∞ (angularChartSymbol b γ c) := by
  have hb0 : ∀ ξ, ξ 0 = 0 → b ξ = 0 := by
    intro ξ hξ
    by_contra hn
    have h := hs ξ (subset_tsupport b hn)
    rw [hξ] at h
    linarith
  rw [angularChartSymbol_eq_rescaled hb0 hγ c]
  exact (contDiff_angularChartFamily hb ha hs).comp
    (contDiff_const.prodMk (angularChartLinearEquiv γ hγ c).symm.contDiff)

theorem angularChartSymbol_narrow {d : ℕ} {b : Space (d + 1) → ℂ}
    {a : ℝ} (ha : 0 < a) (hs : ∀ ξ ∈ tsupport b, a ≤ ξ 0)
    {γ : ℝ} (hγ : 0 < γ) (c : Fin d → ℝ) {ξ : Space (d + 1)}
    (hξ : ξ ∈ tsupport (angularChartSymbol b γ c)) (i : Fin d) :
    |ξ i.succ - c i * ξ 0| ≤ γ * ξ 0 := by
  have hclosed : IsClosed {η : Space (d + 1) | |η i.succ - c i * η 0| ≤ γ * η 0} := by
    apply isClosed_le <;> fun_prop
  apply closure_minimal ?_ hclosed hξ
  intro η hη
  have hb : b η ≠ 0 := by intro hz; exact hη (by simp [angularChartSymbol, hz])
  have h0 : 0 < η 0 := ha.trans_le (hs η (subset_tsupport b hb))
  have hg : angularGridProduct (fun j => (η j.succ / η 0 - c j) / γ) ≠ 0 := by
    intro hz
    exact hη (by simp [angularChartSymbol, hz])
  have hi := (angularGridProduct_ne_zero hg i).le
  rw [abs_div, abs_of_pos hγ] at hi
  have hi' : |η i.succ / η 0 - c i| ≤ γ := by
    simpa only [one_mul] using (div_le_iff₀ hγ).mp hi
  have he : η i.succ - c i * η 0 = (η i.succ / η 0 - c i) * η 0 := by
    field_simp
  change |η i.succ - c i * η 0| ≤ γ * η 0
  rw [he, abs_mul, abs_of_pos h0]
  exact mul_le_mul_of_nonneg_right hi' h0.le

theorem sum_angularChartSymbol {d : ℕ} {b : Space (d + 1) → ℂ}
    {R γ : ℝ} (hγ : 0 < γ)
    (hR : ∀ ξ ∈ tsupport b, ∀ i : Fin d, |ξ i.succ / ξ 0| ≤ R) :
    (fun ξ => ∑ k : Fin d → Fin (2 * angularGridSize R γ + 1),
      angularChartSymbol b γ (angularGridCenter R γ k) ξ) = b := by
  funext ξ
  by_cases hb : b ξ = 0
  · simp [angularChartSymbol, hb]
  · have hp := sum_scaled_angularGridProduct hγ (hR ξ (subset_tsupport b hb))
    simp only [angularChartSymbol, ← Finset.mul_sum, ← Complex.ofReal_sum]
    rw [hp]
    simp

/-- A fixed positive projective chart admits the sharp finite grid
decomposition, with uniform inverse-kernel norms and explicit sector
width. No family of multiplier bounds is assumed. -/
theorem angular_chart_partition {d : ℕ} {b : Space (d + 1) → ℂ}
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b) {a : ℝ} (ha : 0 < a)
    (hs : ∀ ξ ∈ tsupport b, a ≤ ξ 0) :
    ∃ R C : ℝ, 0 ≤ R ∧ 0 ≤ C ∧ ∀ γ : ℝ, 0 < γ → γ ≤ 1 →
      let I := Fin d → Fin (2 * angularGridSize R γ + 1)
      let φ := fun k : I => angularChartSymbol b γ (angularGridCenter R γ k)
      (Fintype.card I : ℝ) ≤ ((2 * R + 3) / γ) ^ d ∧
      (fun ξ => ∑ k : I, φ k ξ) = b ∧
      ∀ k : I, ContDiff ℝ ∞ (φ k) ∧ HasCompactSupport (φ k) ∧
        tsupport (φ k) ⊆ tsupport b ∧
        MeasureTheory.eLpNorm (𝓕⁻ (φ k)) 1 MeasureTheory.volume ≤ ENNReal.ofReal C ∧
        ∀ ξ ∈ tsupport (φ k), ∀ i : Fin d,
          |ξ i.succ - angularGridCenter R γ k i * ξ 0| ≤ γ * ξ 0 := by
  obtain ⟨B, hB, hbound⟩ := hc.isBounded.exists_pos_norm_le
  let R := B / a
  have hR : 0 ≤ R := div_nonneg hB.le ha.le
  have hratio : ∀ ξ ∈ tsupport b, ∀ i : Fin d, |ξ i.succ / ξ 0| ≤ R := by
    intro ξ hξ i
    have h0 : 0 < ξ 0 := ha.trans_le (hs ξ hξ)
    have hi : |ξ i.succ| ≤ B := by
      have hh : |ξ i.succ| ≤ ‖ξ‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le ξ i.succ
      exact hh.trans (hbound ξ hξ)
    rw [abs_div, abs_of_pos h0]
    exact div_le_div₀ hB.le hi ha (hs ξ hξ)
  obtain ⟨C, hC, hk⟩ := uniform_angularChartSymbol_kernel hb hc ha hs (R + 1)
  refine ⟨R, C, hR, hC, ?_⟩
  intro γ hγ hγ1
  dsimp only
  refine ⟨angularGrid_card_bound d hR hγ hγ1, sum_angularChartSymbol hγ hratio, ?_⟩
  intro k
  refine ⟨contDiff_angularChartSymbol hb ha hs hγ.ne' _, ?_,
    tsupport_angularChartSymbol_subset _ _ _, ?_, ?_⟩
  · exact hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_angularChartSymbol_subset _ _ _)
  · exact hk γ hγ hγ1 _ (angularGridCenter_bound hR hγ hγ1 k)
  · exact fun ξ hξ i => angularChartSymbol_narrow ha hs hγ _ hξ i

end OAI.Analysis.Fourier.WavePackets
