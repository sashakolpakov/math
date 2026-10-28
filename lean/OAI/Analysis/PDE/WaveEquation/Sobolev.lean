import OAI.Analysis.PDE.WaveEquation.SobolevHigh

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.PDE.WaveEquation

/-- Source `cor:wave-data`, with the precise one-derivative shift for velocity. -/
def WaveDataSobolevEstimate : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ p ε : ℝ, 2 ≤ p → (0<ε ∨ (p=2 ∧ ε=0)) →
    ∃ C : ℝ, 0 < C ∧ ∀ f g : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ ↦ waveDataSolution z.2 f g z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal C *
        (eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.besselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p+ε) f) (ENNReal.ofReal p) volume +
         eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.besselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p+ε-1) g) (ENNReal.ofReal p) volume)

theorem waveDataSobolevEstimate_of_localSmoothing (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing) :
    WaveDataSobolevEstimate := by
  intro n hn p ε hp hε
  obtain ⟨A,hA,ha⟩ := localSmoothing_waveDisplacement hls hn hp hε
  obtain ⟨C,hC,hc⟩ := localSmoothing_waveHighVelocity hls hn hp hε
  obtain ⟨D,hD,hd⟩ := logarithmicSobolev_lowVelocity (n := n) (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p+ε-1) 0
  simp only [logBesselPotential_zero_log] at hd
  refine ⟨A+(C+D),by positivity,fun f g ↦ ?_⟩
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    simpa only [← ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (show (1:ℝ)≤p by linarith)
  simp only [waveDataSolution_eq_split]
  calc
    _ ≤ eLpNorm (fun z : Space n × ℝ ↦ waveDisplacement z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) +
        eLpNorm (fun z : Space n × ℝ ↦ waveHighVelocity z.2 g z.1 + waveLowVelocity z.2 g z.1)
          (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) := eLpNorm_add_le hp1
    _ ≤ ENNReal.ofReal A * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.besselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p+ε) f)
          (ENNReal.ofReal p) volume +
        (ENNReal.ofReal C * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.besselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p+ε-1) g)
          (ENNReal.ofReal p) volume +
         ENNReal.ofReal D * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.besselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p+ε-1) g)
          (ENNReal.ofReal p) volume) :=
      add_le_add (ha f) ((eLpNorm_add_le hp1).trans (add_le_add (hc g) (hd g p (by linarith))))
    _ ≤ _ := by
      rw [← add_mul,← ENNReal.ofReal_add hC.le hD.le,mul_add]
      exact add_le_add
        (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith : A ≤ A+(C+D))) le_rfl)
        (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith : C+D ≤ A+(C+D))) le_rfl)

/-- Actual spacetime membership for displacement and velocity data. -/
theorem waveData_sobolev_memLp (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2≤n) {p ε : ℝ} (hp : 2≤p) (hε : 0<ε ∨ (p=2 ∧ ε=0))
    (f g : SchwartzMap (Space n) ℂ) :
    MemLp (fun z : Space n × ℝ ↦ waveDataSolution z.2 f g z.1)
      (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) := by
  obtain ⟨C,hC,hbound⟩ := waveDataSobolevEstimate_of_localSmoothing hls n hn p ε hp hε
  exact lt_of_le_of_lt (hbound f g) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.add_lt_top.mpr ⟨(OAI.Analysis.Fourier.BesselPotential.memLp_besselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p+ε) f _).eLpNorm_lt_top,
      (OAI.Analysis.Fourier.BesselPotential.memLp_besselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p+ε-1) g _).eLpNorm_lt_top⟩))

end OAI.Analysis.PDE.WaveEquation
