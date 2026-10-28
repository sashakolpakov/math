import OAI.Analysis.Fourier.LocalSmoothing.Main
import OAI.Analysis.Fourier.Cone.Extension

/-! # Cone extension throughout the strict mixed range -/

noncomputable section
namespace OAI.Analysis.Fourier.Cone

/-- The truncated-cone extension estimate throughout the strict mixed range. -/
theorem cone_extension : ConeExtensionEstimates :=
  localSmoothing_coneExtension LocalSmoothing.euclidean_local_smoothing

end OAI.Analysis.Fourier.Cone
