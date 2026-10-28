import OAI.Analysis.Fourier.LocalSmoothing.Main
import OAI.Analysis.PDE.WaveEquation.Estimate

/-! # Logarithmic estimates for displacement and velocity data -/

noncomputable section
namespace OAI.Analysis.PDE.WaveEquation

/-- The logarithmic estimate for the actual displacement/velocity wave solution. -/
theorem wave_data : WaveDataLogarithmicEstimate :=
  waveDataLogarithmicEstimate_of_logarithmicSobolev
    OAI.Analysis.Fourier.LocalSmoothing.logarithmic_sobolev

end OAI.Analysis.PDE.WaveEquation
