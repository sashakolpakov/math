import OAI.Analysis.Fourier.Restriction.Sparse.Index

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem indexedLocalizedKernel_gram_bound {n : ℕ} (hn : 2 ≤ n)
    (u : SchwartzMap (Space n) ℂ)
    (hu : ∀ ξ, ‖OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ‖ ≤ 1)
    (hr : ∀ ξ, star (OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ) = OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ)
    (hs : ∀ ξ, 1 / 8 ≤ ‖ξ‖ → OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ = 0) :
    ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ (N : ℕ) (R : ℝ), 1 ≤ R →
      ∀ z : Fin N → Space n,
      (∀ i j, i ≠ j → R ^ (16 * n) * (N : ℝ) ^ (16 * n) ≤ dist (z i) (z j)) →
      ∀ ν : Measure (Space n), SFinite ν → ν ≤ volume → ∀ x : Fin N × Space n,
      (∫⁻ y, ‖gramKernel (OAI.Analysis.Fourier.Restriction.sphereMeasure n) (indexedLocalizedKernel u R z) (x, y)‖ₑ
        ∂(Measure.count.prod ν)) ≤
        volume (ball (0 : Space n) 1) * ENNReal.ofReal (A * R) +
          ENNReal.ofReal B * ν univ := by
  obtain ⟨A, hA, HA⟩ := localizedFourierKernel_column (by omega : 1 ≤ n) u hu hs
  obtain ⟨B, hB, HB⟩ := localizedFourierKernel_gram_decay (by omega : 1 ≤ n) u hr
  refine ⟨A, B, hA, hB, ?_⟩
  intro N R hR z hsep ν hνfinite hν x
  let := hνfinite
  have hR0 : 0 < R := by linarith
  have hN : 1 ≤ N := Nat.succ_le_of_lt (Nat.zero_lt_of_lt x.1.isLt)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt x.1.isLt)
  have hNm : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let K := indexedLocalizedKernel u R z
  have hK : Measurable K := measurable_indexedLocalizedKernel u hR0 z
  have hG : Measurable (fun y : Fin N × Space n ↦ ‖gramKernel (OAI.Analysis.Fourier.Restriction.sphereMeasure n) K (x, y)‖ₑ) := by
    have := measurable_gramKernel (OAI.Analysis.Fourier.Restriction.sphereMeasure n) hK
    fun_prop
  rw [lintegral_prod _ hG.aemeasurable, lintegral_count, tsum_fintype]
  have hdiag : (∫⁻ η, ‖gramKernel (OAI.Analysis.Fourier.Restriction.sphereMeasure n) K (x, (x.1, η))‖ₑ ∂ν) ≤
      volume (ball (0 : Space n) 1) * ENNReal.ofReal (A * R) := by
    have hrow (ω : Space n) : (∫⁻ η, ‖localizedFourierKernel u R (z x.1) ω η‖ₑ ∂ν) ≤
        volume (ball (0 : Space n) 1) :=
      (lintegral_mono' hν le_rfl).trans (localizedFourierKernel_row u hu hs hR0 (z x.1) ω)
    exact lintegral_gramKernel_le_of_row_column ν (OAI.Analysis.Fourier.Restriction.sphereMeasure n)
      (K := fun p : Space n × Space n ↦ localizedFourierKernel u R (z x.1) p.1 p.2)
      (continuous_localizedFourierKernel u hR0 (z x.1)).measurable hrow (HA R hR0 (z x.1)) x.2
  have hoff (j : Fin N) (hj : j ≠ x.1) :
      (∫⁻ η, ‖gramKernel (OAI.Analysis.Fourier.Restriction.sphereMeasure n) K (x, (j, η))‖ₑ ∂ν) ≤
      ENNReal.ofReal (B / N) * ν univ := by
    calc
      _ ≤ ∫⁻ _η : Space n, ENNReal.ofReal (B / N) ∂ν := by
        apply lintegral_mono
        intro η
        dsimp only
        rw [← ofReal_norm]
        apply ENNReal.ofReal_le_ofReal
        have H := HB R hR (z x.1) (z j) x.2 η
        have hsep' : R ^ ((16 : ℝ) * n) * (N : ℝ) ^ ((16 : ℝ) * n) ≤ dist (z x.1) (z j) := by
          rw [show (16 : ℝ) * n = ((16 * n : ℕ) : ℝ) by push_cast; rfl,
            Real.rpow_natCast, Real.rpow_natCast]
          exact hsep x.1 j (Ne.symm hj)
        have Hd := sparse_dimension_decay hn hR hNm hsep'
        change ‖∫ ω, localizedFourierKernel u R (z x.1) ω x.2 *
          star (localizedFourierKernel u R (z j) ω η) ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n‖ ≤ B / N
        apply H.trans
        calc
          _ = B * ((R ^ n * R ^ (((n : ℝ) - 1) / 2)) ^ 2 *
            (1 + dist (z x.1) (z j)) ^ (-((n : ℝ) - 1) / 2)) := by ring
          _ ≤ B * (N : ℝ)⁻¹ := mul_le_mul_of_nonneg_left Hd hB
          _ = _ := by rw [div_eq_mul_inv]
      _ = _ := lintegral_const _
  have Hsum := finite_diagonal_sum_le x.1
    (fun j ↦ ∫⁻ η, ‖gramKernel (OAI.Analysis.Fourier.Restriction.sphereMeasure n) K (x, (j, η))‖ₑ ∂ν) hdiag hoff
  apply Hsum.trans
  have hscale : (N : ℝ≥0∞) * ENNReal.ofReal (B / N) = ENNReal.ofReal B := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
    field_simp
  rw [← mul_assoc, hscale]

end OAI.Analysis.Fourier.Restriction
