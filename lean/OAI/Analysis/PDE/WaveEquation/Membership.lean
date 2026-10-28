import OAI.Analysis.PDE.WaveEquation.Estimate

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.PDE.WaveEquation

/-- The displacement/velocity estimate also gives actual spacetime membership. -/
theorem waveData_logarithmic_memLp (hlog : OAI.Analysis.Fourier.LocalSmoothing.LogarithmicSobolev)
    {n : ℕ} (hn : 2≤n) {p B : ℝ} (hp : 2<p) (hB : 2*(n:ℝ)+6<B)
    (f g : SchwartzMap (Space n) ℂ) :
    MemLp (fun z : Space n × ℝ ↦ waveDataSolution z.2 f g z.1)
      (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) := by
  obtain ⟨C,hC,hbound⟩ := waveDataLogarithmicEstimate_of_logarithmicSobolev hlog n hn p B hp hB
  exact lt_of_le_of_lt (hbound f g) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.add_lt_top.mpr ⟨(OAI.Analysis.Fourier.BesselPotential.memLp_logBesselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p) B f _).eLpNorm_lt_top,
      (OAI.Analysis.Fourier.BesselPotential.memLp_logBesselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p-1) B g _).eLpNorm_lt_top⟩))

end OAI.Analysis.PDE.WaveEquation
