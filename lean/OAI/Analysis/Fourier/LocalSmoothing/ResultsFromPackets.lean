import OAI.Analysis.Fourier.LocalSmoothing.FromLogarithmic
import OAI.Analysis.Fourier.WavePackets.AllScales
import OAI.Analysis.Fourier.LocalSmoothing.Implications
import OAI.Analysis.Fourier.BochnerRiesz.MainTheorem

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing

/-- The analytic main results and all requested consequences, with the
single remaining geometric input made explicit. -/
theorem main_results_of_packet_solvability
    (hsolve : ∀ n : ℕ, OAI.Analysis.Fourier.WavePackets.PositivePacketSolvability n) :
    LogarithmicRefinement ∧ EuclideanLocalSmoothing ∧ LogarithmicSobolev ∧
      OAI.Analysis.Fourier.BochnerRiesz.BochnerRieszConjecture ∧ OAI.Analysis.Fourier.Restriction.SphericalRestrictionConjecture ∧
      OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture ∧ OAI.Analysis.Fourier.SquareFunction.SteinSquareConjecture ∧
      OAI.MeasureTheory.Kakeya.KakeyaConjecture := by
  have hlog := OAI.Analysis.Fourier.WavePackets.logarithmicRefinement_of_packet_solvability hsolve
  have hls := euclideanLocalSmoothing_of_logarithmicRefinement hlog
  exact ⟨hlog, hls, logarithmicSobolev_of_logarithmicRefinement hlog,
    OAI.Analysis.Fourier.LocalSmoothing.localSmoothing_all_consequences hls⟩

/-- The main results with every clause of the introduction's Bochner--Riesz
theorem: full-space bounded operators, maximal bounds, and convergence. -/
theorem main_theorems_of_packet_solvability
    (hsolve : ∀ n : ℕ, OAI.Analysis.Fourier.WavePackets.PositivePacketSolvability n) :
    LogarithmicRefinement ∧ EuclideanLocalSmoothing ∧ LogarithmicSobolev ∧
      OAI.Analysis.Fourier.BochnerRiesz.BochnerRieszMainTheorem ∧ OAI.Analysis.Fourier.Restriction.SphericalRestrictionConjecture ∧
      OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture ∧ OAI.Analysis.Fourier.SquareFunction.SteinSquareConjecture ∧
      OAI.MeasureTheory.Kakeya.KakeyaConjecture := by
  obtain ⟨hlog, hls, hsob, _, hsphere, hkmax, hsquare, hkakeya⟩ :=
    main_results_of_packet_solvability hsolve
  exact ⟨hlog, hls, hsob, OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszMainTheorem_of_localSmoothing hls,
    hsphere, hkmax, hsquare, hkakeya⟩

end OAI.Analysis.Fourier.LocalSmoothing
