import OAI.Analysis.Fourier.LocalSmoothing.Main
import OAI.Analysis.Fourier.Restriction.LocalSmoothing

/-! # Spherical restriction throughout the strict mixed range -/

noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- Corollary `cor:spherical-restriction`, throughout its strict mixed range. -/
theorem spherical_restriction : SphericalRestrictionConjecture :=
  localSmoothing_sphericalRestrictionConjecture LocalSmoothing.euclidean_local_smoothing

end OAI.Analysis.Fourier.Restriction
