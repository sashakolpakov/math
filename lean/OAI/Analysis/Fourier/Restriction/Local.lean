import OAI.Analysis.Fourier.Restriction.LocalCritical

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem localSmoothing_local_restriction (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R → ∀ f : Space n → ℂ,
      Measurable f → Integrable f → (∀ x, R < ‖x‖ → f x = 0) →
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (ENNReal.ofReal (restrictionInputExponent n)) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        C * ENNReal.ofReal (R ^ ε) * eLpNorm f (ENNReal.ofReal (restrictionInputExponent n)) volume := by
  obtain ⟨C, hC, H⟩ := localSmoothing_local_restriction_critical hls hn hε
  refine ⟨C + 1, by finiteness, ?_⟩
  intro R hR f hfm hfi hfs
  by_cases hp : MemLp f (ENNReal.ofReal (restrictionInputExponent n)) volume
  · exact (H R hR f hfm hfi hp hfs).trans (by gcongr; exact le_self_add)
  · have he : eLpNorm f (ENNReal.ofReal (restrictionInputExponent n)) volume = ⊤ :=
      top_le_iff.mp (not_lt.mp hp)
    have hpos : 0 < R ^ ε := Real.rpow_pos_of_pos (by linarith) ε
    have hc0 : C + 1 ≠ 0 := by positivity
    rw [he, ENNReal.mul_top (mul_ne_zero hc0 (ENNReal.ofReal_pos.mpr hpos).ne')]
    exact le_top

end OAI.Analysis.Fourier.Restriction
