import OAI.Analysis.Fourier.Radial.BREndpoints
import OAI.Analysis.Fourier.BochnerRiesz.LowerRange

/-! The complete Bochner--Riesz consequence, including p=1 and p=∞. -/

open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Radial

theorem bochnerRieszIndex_one {n : ℕ} (hn : 1 ≤ n) :
    OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszIndex n 1 = ((n : ℝ) - 1) / 2 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  norm_num [OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszIndex]
  rw [max_eq_left (by linarith)]
  ring

theorem bochnerRieszIndex_top {n : ℕ} (hn : 1 ≤ n) :
    OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszIndex n ∞ = ((n : ℝ) - 1) / 2 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  norm_num [OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszIndex]
  rw [max_eq_left (by linarith)]
  ring

/-- The local-smoothing conjecture implies the full strict Bochner--Riesz
conjecture, with the endpoint cases supplied by sharp kernel integrability. -/
theorem localSmoothing_bochnerRieszConjecture (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing) :
    OAI.Analysis.Fourier.BochnerRiesz.BochnerRieszConjecture := by
  intro n hn p hp δ hδ
  have hn1 : 1 ≤ n := by omega
  by_cases ht : p = ∞
  · subst p
    rw [bochnerRieszIndex_top hn1] at hδ
    obtain ⟨C, hC, h⟩ := bochnerRiesz_high_order_all_exponents hn1 hδ
    exact ⟨C, hC, fun R hR f => h ∞ (by simp) R hR f⟩
  by_cases h1 : p = 1
  · subst p
    rw [bochnerRieszIndex_one hn1] at hδ
    obtain ⟨C, hC, h⟩ := bochnerRiesz_high_order_all_exponents hn1 hδ
    exact ⟨C, hC, fun R hR f => h 1 le_rfl R hR f⟩
  exact OAI.Analysis.Fourier.BochnerRiesz.localSmoothing_bochnerRiesz_strict_finite hls hn
    (lt_of_le_of_ne hp (Ne.symm h1)) ht hδ

end OAI.Analysis.Fourier.Radial
