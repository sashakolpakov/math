import OAI.Analysis.Fourier.WavePackets.Half.Wave.CapPhase

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter
open scoped ContDiff Topology

theorem contDiffAt_capPhaseRemainder {d : ℕ}
    (p : (ℝ × (Fin d → ℝ)) × Space (d+1)) (hp : 0 < p.2 0) :
    ContDiffAt ℝ ∞ (fun q : (ℝ × (Fin d → ℝ)) × Space (d+1) =>
      capPhaseRemainder q.1.1 q.1.2 q.2) p := by
  have haxis : ContDiff ℝ ∞ (fun q : (ℝ × (Fin d → ℝ)) × Space (d+1) => capAxis q.1.2) :=
    (contDiff_capAxis d).comp contDiff_fst.snd
  have haxisnorm := haxis.contDiffAt.norm ℝ (capAxis_ne_zero p.1.2)
  have hzero : ContDiff ℝ ∞ (fun q : (ℝ × (Fin d → ℝ)) × Space (d+1) => q.2 0) := by
    fun_prop
  have htrans := (contDiff_capTransverse d).comp
    (contDiff_snd : ContDiff ℝ ∞ (fun q : (ℝ × (Fin d → ℝ)) × Space (d+1) => q.2))
  have htranssq := htrans.norm_sq ℝ
  have hq := (haxis.contDiffAt.inner ℝ htrans.contDiffAt).div haxisnorm
    (norm_ne_zero_iff.mpr (capAxis_ne_zero p.1.2))
  have hneq : angularChartRescale p.1.1 p.1.2 p.2 ≠ 0 := by
    intro he
    have := congrArg (fun z : Space (d+1) => z 0) he
    simpa only [angularChartRescale_zero,PiLp.zero_apply] using hp.ne' this
  have hN := (contDiff_angularChartRescale d).contDiffAt.norm ℝ hneq
  have hr := hzero.contDiffAt.mul haxisnorm
  have hD := hN.add hr
  have hD0 : ‖angularChartRescale p.1.1 p.1.2 p.2‖+p.2 0*‖capAxis p.1.2‖ ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (norm_nonneg _)
      (mul_pos hp (norm_pos_iff.mpr (capAxis_ne_zero p.1.2))))
  unfold capPhaseRemainder
  exact (htranssq.contDiffAt.div hD hD0).sub
    ((hq.mul (((contDiffAt_const.mul hr).mul hq).add
      (contDiffAt_fst.fst.mul htranssq.contDiffAt))).div (hD.pow 2) (pow_ne_zero 2 hD0))

def capWaveFamily {d : ℕ} (b : Space (d+1) → ℂ)
    (p : (ℝ × (ℝ × (Fin d → ℝ))) × Space (d+1)) : ℂ :=
  angularChartFamily b (p.1.2,p.2) *
    Complex.exp (-Complex.I * (p.1.1*capPhaseRemainder p.1.2.1 p.1.2.2 p.2 : ℝ))

theorem contDiff_capWaveFamily {d : ℕ} {b : Space (d+1) → ℂ}
    (hb : ContDiff ℝ ∞ b) {a : ℝ} (ha : 0 < a)
    (hs : ∀ ξ ∈ tsupport b, a ≤ ξ 0) : ContDiff ℝ ∞ (capWaveFamily b) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  have harg : ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × (Fin d → ℝ))) × Space (d+1) =>
      (q.1.2,q.2)) := contDiff_fst.snd.prodMk contDiff_snd
  by_cases hp : 0 < p.2 0
  · have hphase := (contDiffAt_capPhaseRemainder (p.1.2,p.2) hp).comp p harg.contDiffAt
    apply ((contDiff_angularChartFamily hb ha hs).comp harg).contDiffAt.mul
    exact (contDiffAt_const.mul
      (Complex.ofRealCLM.contDiff.contDiffAt.comp p (contDiffAt_fst.fst.mul hphase))).cexp
  · have hnot : angularChartRescale p.1.2.1 p.1.2.2 p.2 ∉ tsupport b := by
      intro hx
      have := hs _ hx
      rw [angularChartRescale_zero] at this
      exact hp (ha.trans_le this)
    have he := (notMem_tsupport_iff_eventuallyEq.mp hnot).comp_tendsto
      ((contDiff_angularChartRescale d).comp harg).continuous.continuousAt
    apply (contDiffAt_const : ContDiffAt ℝ ∞
      (fun _ : (ℝ × (ℝ × (Fin d → ℝ))) × Space (d+1) => (0 : ℂ)) p).congr_of_eventuallyEq
    filter_upwards [he] with q hq
    change b (angularChartRescale q.1.2.1 q.1.2.2 q.2) = 0 at hq
    simp only [capWaveFamily,angularChartFamily,hq,zero_mul]

end OAI.Analysis.Fourier.WavePackets
