import OAI.Analysis.Fourier.LocalSmoothing.FromLogarithmic
import OAI.Analysis.Fourier.WavePackets.AllScales
import OAI.Analysis.Fourier.WavePackets.PositivePacketSolvability

/-! # Euclidean wave local smoothing and its logarithmic refinement -/

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing

/-- Theorem `thm:main` in `sections/introduction.tex`. -/
theorem logarithmic_refinement : LogarithmicRefinement :=
  WavePackets.logarithmicRefinement_of_packet_solvability WavePackets.positive_packet_solvability

/-- Theorem `thm:local-smoothing`, including the zero-loss `p = 2` endpoint. -/
theorem euclidean_local_smoothing : EuclideanLocalSmoothing :=
  euclideanLocalSmoothing_of_logarithmicRefinement logarithmic_refinement

/-- Corollary `cor:log-sobolev`, at the exact Sobolev order. -/
theorem logarithmic_sobolev : LogarithmicSobolev :=
  logarithmicSobolev_of_logarithmicRefinement logarithmic_refinement

end OAI.Analysis.Fourier.LocalSmoothing
