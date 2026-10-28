import OAI.Analysis.PDE.WaveEquation.Formula

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.PDE.WaveEquation

/-- The actual displacement/velocity Fourier solution, with the removable
sine quotient assigned its value `t` at zero frequency. -/
def waveDataSolution {n : ℕ} (t : ℝ) (f g : Space n → ℂ) (x : Space n) : ℂ :=
  OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ (Real.cos (t*‖ξ‖):ℂ) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ) x +
    waveVelocity t g x

theorem waveDataSolution_eq_split {n : ℕ} (t : ℝ)
    (f g : SchwartzMap (Space n) ℂ) (x : Space n) :
    waveDataSolution t f g x =
      waveDisplacement t f x + (waveHighVelocity t g x + waveLowVelocity t g x) := by
  rw [waveDisplacement_eq_cosine,← waveVelocity_eq_high_add_low]
  rfl

/-- Source `cor:wave-data`, with the precise one-derivative shift for velocity. -/
def WaveDataLogarithmicEstimate : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ p B : ℝ, 2 < p → 2*n+6 < B →
    ∃ C : ℝ, 0 < C ∧ ∀ f g : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ ↦ waveDataSolution z.2 f g z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal C *
        (eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p) B f) (ENNReal.ofReal p) volume +
         eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p-1) B g) (ENNReal.ofReal p) volume)

theorem waveDataLogarithmicEstimate_of_logarithmicSobolev (hlog : OAI.Analysis.Fourier.LocalSmoothing.LogarithmicSobolev) :
    WaveDataLogarithmicEstimate := by
  intro n hn p B hp hB
  obtain ⟨A,hA,ha⟩ := logarithmicSobolev_displacement hlog hn hp hB
  obtain ⟨C,hC,hc⟩ := logarithmicSobolev_highVelocity hlog hn hp hB
  obtain ⟨D,hD,hd⟩ := logarithmicSobolev_lowVelocity (n := n) (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p-1) B
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
    _ ≤ ENNReal.ofReal A * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p) B f)
          (ENNReal.ofReal p) volume +
        (ENNReal.ofReal C * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p-1) B g)
          (ENNReal.ofReal p) volume +
         ENNReal.ofReal D * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p-1) B g)
          (ENNReal.ofReal p) volume) :=
      add_le_add (ha f) ((eLpNorm_add_le hp1).trans (add_le_add (hc g) (hd g p (by linarith))))
    _ ≤ _ := by
      rw [← add_mul,← ENNReal.ofReal_add hC.le hD.le,mul_add]
      exact add_le_add
        (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith : A ≤ A+(C+D))) le_rfl)
        (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith : C+D ≤ A+(C+D))) le_rfl)

end OAI.Analysis.PDE.WaveEquation
