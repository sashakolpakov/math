import OAI.Analysis.Fourier.LocalSmoothing.Main
import OAI.Analysis.Fourier.BochnerRiesz.MainTheorem
import OAI.Analysis.Fourier.Radial.BRConjecture

/-! # Bochner–Riesz estimates throughout the strict range -/

noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

/-- Theorem `thm:bochner-riesz`: uniform full-`Lᵖ` operators, maximal estimates,
norm convergence for finite exponents, and almost-everywhere convergence. -/
theorem bochner_riesz : BochnerRieszMainTheorem :=
  bochnerRieszMainTheorem_of_localSmoothing LocalSmoothing.euclidean_local_smoothing

/-- The Fourier-integral formulation of the uniform Bochner--Riesz estimate. -/
theorem bochner_riesz_schwartz : BochnerRieszConjecture :=
  Radial.localSmoothing_bochnerRieszConjecture LocalSmoothing.euclidean_local_smoothing

end OAI.Analysis.Fourier.BochnerRiesz
