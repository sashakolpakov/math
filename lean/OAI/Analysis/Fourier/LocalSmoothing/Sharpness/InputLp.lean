import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.InputSup
import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.InputL1
import OAI.Analysis.Fourier.Restriction.Interpolation

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Filter
open scoped ENNReal
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

/-- The input estimate in `eq:initial-shell-bound`, obtained from the
sharp L1 kernel estimate and the explicit radial pointwise bound. -/
theorem focusing_packet_initial_Lp {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, 1 ≤ p → ∀ N : ℝ, 2 ≤ N →
      ∀ f : SchwartzMap (Space n) ℂ,
      (f : Space n → ℂ) = OAI.Analysis.Fourier.LocalSmoothing.angularInverse (focusingSymbol n N (3/2)) →
      eLpNorm f (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C*N^((n:ℝ)-radialOrder n-1/p)) := by
  obtain ⟨A,hA,hAb⟩ := focusing_packet_initial_sup hn
  obtain ⟨B,hB,hBb⟩ := focusing_packet_initial_L1 hn
  let C := A+B+1
  have hC : 0 < C := by dsimp [C]; linarith
  have hAC : A ≤ C := by dsimp [C]; linarith
  have hBC : B ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,fun p hp N hN f hf => ?_⟩
  have hpp : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hNp : 0 < N := by linarith
  have hs : ∀ᵐ x ∂volume, ‖f x‖ₑ ≤ ENNReal.ofReal (C*N^((n:ℝ)-radialOrder n)) := by
    apply Eventually.of_forall
    intro x
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal ((hAb N hN f hf x).trans
      (mul_le_mul_of_nonneg_right hAC (Real.rpow_nonneg hNp.le _)))
  have h1 : eLpNorm f 1 volume ≤ ENNReal.ofReal (C*N^(radialOrder n)) :=
    (hBb N (by linarith) f hf).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hBC (Real.rpow_nonneg hNp.le _)))
  have hα : 0 ≤ (p-1)/p := div_nonneg (sub_nonneg.mpr hp) hpp.le
  have hβ : 0 ≤ 1/p := (one_div_pos.mpr hpp).le
  have h := OAI.Analysis.Fourier.Restriction.eLpNorm_le_of_enorm_bound volume f.continuous.aestronglyMeasurable
    (by norm_num : (0:ℝ)<1) hp hs
  simp only [ENNReal.ofReal_one] at h
  refine h.trans ((mul_le_mul' le_rfl (ENNReal.rpow_le_rpow h1 hβ)).trans_eq ?_)
  rw [ENNReal.ofReal_rpow_of_pos (mul_pos hC (Real.rpow_pos_of_pos hNp _)),
    ENNReal.ofReal_rpow_of_pos (mul_pos hC (Real.rpow_pos_of_pos hNp _)),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
  congr 1
  rw [Real.mul_rpow hC.le (Real.rpow_nonneg hNp.le _),
    Real.mul_rpow hC.le (Real.rpow_nonneg hNp.le _),
    ← Real.rpow_mul hNp.le,← Real.rpow_mul hNp.le]
  have hsum : (p-1)/p+1/p = 1 := by field_simp; ring
  have hexp : ((n:ℝ)-radialOrder n)*((p-1)/p)+radialOrder n*(1/p) =
      (n:ℝ)-radialOrder n-1/p := by
    unfold radialOrder
    field_simp
    ring
  calc
    _ = (C^((p-1)/p)*C^(1/p)) *
        (N^(((n:ℝ)-radialOrder n)*((p-1)/p))*N^(radialOrder n*(1/p))) := by ring
    _ = _ := by rw [← Real.rpow_add hC,hsum,Real.rpow_one,← Real.rpow_add hNp,hexp]

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
