import OAI.Analysis.Fourier.WavePackets.Half.Wave.NormalizedKernel
import Mathlib.Analysis.Analytic.IsolatedZeros

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter _root_.MeasureTheory
open scoped ContDiff Topology FourierTransform ENNReal

theorem contDiff_exp_dslope : ContDiff ℝ ∞ (dslope Complex.exp 0) := by
  have H : ContDiff ℂ ∞ (dslope Complex.exp 0) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z = 0
    · subst z
      obtain ⟨p,hp⟩ := (analyticAt_cexp : AnalyticAt ℂ Complex.exp 0)
      exact hp.has_fpower_series_dslope_fslope.analyticAt.contDiffAt
    · apply ContDiffAt.congr_of_eventuallyEq _ (dslope_eventuallyEq_slope_of_ne Complex.exp hz)
      change ContDiffAt ℂ ∞ (fun x : ℂ => (x-0)⁻¹ • (Complex.exp x-Complex.exp 0)) z
      simpa only [sub_zero, smul_eq_mul] using!
        (contDiffAt_id.inv hz).smul
          (Complex.contDiff_exp.contDiffAt.sub (contDiffAt_const (c := Complex.exp 0)))
  exact H.restrict_scalars ℝ

/-- The removable exponential quotient, already divided by its small parameter. -/
def lowWaveFamily {n : ℕ} (b χ : Space n → ℂ)
    (p : (ℝ × ℝ) × Space n) : ℂ :=
  b p.2 * χ (p.1.2 • p.2) * (-Complex.I * (p.1.1 * ‖p.2‖ : ℝ)) *
    dslope Complex.exp 0 (-Complex.I * (p.1.1 * p.1.2 * ‖p.2‖ : ℝ))

theorem lowWaveFamily_identity {n : ℕ} (b χ : Space n → ℂ)
    (T r : ℝ) (ξ : Space n) :
    (r : ℂ) * lowWaveFamily b χ ((T,r),ξ) =
      b ξ * χ (r • ξ) * (Complex.exp (-Complex.I * (T*r*‖ξ‖ : ℝ)) - 1) := by
  have h := sub_smul_dslope Complex.exp (0 : ℂ) (-Complex.I * (T*r*‖ξ‖ : ℝ))
  simp only [sub_zero, smul_eq_mul, Complex.exp_zero] at h
  unfold lowWaveFamily
  rw [← h]
  push_cast
  ring

theorem contDiff_lowWaveFamily {n : ℕ} {b χ : Space n → ℂ}
    (hb : ContDiff ℝ ∞ b) (hχ : ContDiff ℝ ∞ χ) (hz : 0 ∉ tsupport b) :
    ContDiff ℝ ∞ (lowWaveFamily b χ) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.2 = 0
  · have he := (notMem_tsupport_iff_eventuallyEq.mp (hp ▸ hz)).comp_tendsto
      (continuous_snd.continuousAt : ContinuousAt (fun q : (ℝ × ℝ) × Space n => q.2) p)
    apply (contDiffAt_const : ContDiffAt ℝ ∞
      (fun _ : (ℝ × ℝ) × Space n => (0 : ℂ)) p).congr_of_eventuallyEq
    filter_upwards [he] with q hq
    change b q.2 = 0 at hq
    simp only [lowWaveFamily,hq,zero_mul]
  · have hnorm := (contDiffAt_snd : ContDiffAt ℝ ∞
        (fun q : (ℝ × ℝ) × Space n => q.2) p).norm ℝ hp
    have hsmall : ContDiffAt ℝ ∞ (fun q : (ℝ × ℝ) × Space n =>
        -Complex.I * (q.1.1*q.1.2*‖q.2‖ : ℝ)) p :=
      contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp p
        ((contDiffAt_fst.fst.mul contDiffAt_fst.snd).mul hnorm))
    have hlarge : ContDiffAt ℝ ∞ (fun q : (ℝ × ℝ) × Space n =>
        -Complex.I * (q.1.1*‖q.2‖ : ℝ)) p :=
      contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp p
        (contDiffAt_fst.fst.mul hnorm))
    exact (((hb.comp contDiff_snd).contDiffAt.mul
      (hχ.comp (contDiff_fst.snd.smul contDiff_snd)).contDiffAt).mul hlarge).mul
      (contDiff_exp_dslope.contDiffAt.comp p hsmall)

theorem lowWaveFamily_support {n : ℕ} (b χ : Space n → ℂ) :
    tsupport (lowWaveFamily b χ) ⊆ univ ×ˢ tsupport b := by
  intro p hp
  have hsub : tsupport (lowWaveFamily b χ) ⊆ tsupport (fun q : (ℝ × ℝ) × Space n => b q.2) := by
    unfold lowWaveFamily
    exact tsupport_mul_subset_left.trans (tsupport_mul_subset_left.trans tsupport_mul_subset_left)
  exact ⟨mem_univ _,tsupport_comp_subset_preimage b continuous_snd (hsub hp)⟩

end OAI.Analysis.Fourier.WavePackets
