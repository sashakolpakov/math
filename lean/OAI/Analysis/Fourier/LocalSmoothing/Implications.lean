import OAI.Analysis.Fourier.Restriction.LocalSmoothing
import OAI.Analysis.Fourier.Radial.BRConjecture
import OAI.Analysis.Fourier.SquareFunction.LocalSmoothing
import OAI.Analysis.Fourier.SquareFunction.Maximal.BR

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing

/-- All analytic and geometric consequences requested for the Euclidean
wave local-smoothing theorem. Each component uses the actual operator or
Hausdorff-dimension definition, with its stated conjectured strict range. -/
theorem localSmoothing_all_consequences (hls : EuclideanLocalSmoothing) :
    OAI.Analysis.Fourier.BochnerRiesz.BochnerRieszConjecture ∧ OAI.Analysis.Fourier.Restriction.SphericalRestrictionConjecture ∧
      OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture ∧ OAI.Analysis.Fourier.SquareFunction.SteinSquareConjecture ∧ OAI.MeasureTheory.Kakeya.KakeyaConjecture :=
  ⟨OAI.Analysis.Fourier.Radial.localSmoothing_bochnerRieszConjecture hls,
    OAI.Analysis.Fourier.Restriction.localSmoothing_sphericalRestrictionConjecture hls,
    OAI.Analysis.Fourier.Restriction.localSmoothing_kakeyaMaximalConjecture hls,
    OAI.Analysis.Fourier.SquareFunction.localSmoothing_steinSquareConjecture hls,
    OAI.Analysis.Fourier.Restriction.localSmoothing_kakeyaConjecture hls⟩

/-- The maximal Bochner–Riesz bounds are also available from the same
local-smoothing hypothesis. -/
theorem localSmoothing_maximalBochnerRiesz (hls : EuclideanLocalSmoothing) :
    OAI.Analysis.Fourier.BochnerRiesz.MaximalBochnerRieszConjecture :=
  OAI.Analysis.Fourier.SquareFunction.localSmoothing_maximalBochnerRieszConjecture hls

end OAI.Analysis.Fourier.LocalSmoothing
