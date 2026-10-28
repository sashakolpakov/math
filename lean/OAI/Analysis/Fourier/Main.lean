import OAI.Analysis.Fourier.LocalSmoothing.Main
import OAI.Analysis.PDE.WaveEquation.Main
import OAI.Analysis.Fourier.BochnerRiesz.Main
import OAI.Analysis.Fourier.Restriction.Main
import OAI.Analysis.Fourier.Cone.Main
import OAI.MeasureTheory.Kakeya.Main
import OAI.Analysis.Fourier.SquareFunction.Main

namespace OAI.Analysis.Fourier

/-- The analytic main statements and requested consequences, without a
packet-solvability or local-smoothing hypothesis. -/
theorem main_theorems :
    LocalSmoothing.LogarithmicRefinement ∧ LocalSmoothing.EuclideanLocalSmoothing ∧ LocalSmoothing.LogarithmicSobolev ∧
      OAI.Analysis.Fourier.BochnerRiesz.BochnerRieszMainTheorem ∧ OAI.Analysis.Fourier.Restriction.SphericalRestrictionConjecture ∧
      OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture ∧ OAI.Analysis.Fourier.SquareFunction.SteinSquareConjecture ∧
      OAI.Analysis.Fourier.SquareFunction.SteinSquareFullLp ∧ OAI.Analysis.Fourier.Cone.ConeExtensionEstimates ∧
      OAI.Analysis.PDE.WaveEquation.WaveDataLogarithmicEstimate ∧ OAI.MeasureTheory.Kakeya.KakeyaConjecture :=
  ⟨LocalSmoothing.logarithmic_refinement, LocalSmoothing.euclidean_local_smoothing, LocalSmoothing.logarithmic_sobolev,
    OAI.Analysis.Fourier.BochnerRiesz.bochner_riesz, OAI.Analysis.Fourier.Restriction.spherical_restriction, OAI.MeasureTheory.Kakeya.kakeya_maximal, OAI.Analysis.Fourier.SquareFunction.stein_square,
    OAI.Analysis.Fourier.SquareFunction.stein_square_fullLp, OAI.Analysis.Fourier.Cone.cone_extension, OAI.Analysis.PDE.WaveEquation.wave_data, OAI.MeasureTheory.Kakeya.kakeya⟩

end OAI.Analysis.Fourier
