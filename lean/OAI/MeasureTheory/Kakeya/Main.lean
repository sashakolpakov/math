import OAI.Analysis.Fourier.LocalSmoothing.Main
import OAI.Analysis.Fourier.Restriction.LocalSmoothing
import OAI.MeasureTheory.Kakeya.Hausdorff

/-! # Kakeya maximal estimates and full Hausdorff dimension -/

open OAI.Analysis.Fourier

noncomputable section
namespace OAI.MeasureTheory.Kakeya

/-- Corollary `cor:kakeya`, with every positive epsilon loss. -/
theorem kakeya_maximal : KakeyaMaximalConjecture :=
  Restriction.localSmoothing_kakeyaMaximalConjecture LocalSmoothing.euclidean_local_smoothing

/-- Corollary `cor:kakeya-dimension`, for arbitrary Kakeya sets. -/
theorem kakeya : KakeyaConjecture :=
  kakeyaMaximal_implies_kakeya kakeya_maximal

end OAI.MeasureTheory.Kakeya
