import OAI.Analysis.Fourier.Restriction.Sparse.Bound
import OAI.Analysis.Fourier.Restriction.Extension
import OAI.Analysis.Fourier.Restriction.Diagonal
import OAI.MeasureTheory.Kakeya.Hausdorff

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem restriction_dual_exponent {n : ℕ} (hn : 2 ≤ n) {s : ℝ}
    (hs : OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n < s) :
    1 < s ∧ 1 ≤ s / (s - 1) ∧ s / (s - 1) < restrictionInputExponent n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hs1 : 1 < s := by have := (OAI.MeasureTheory.Kakeya.criticalExponent_gt_two hn).trans hs; linarith
  refine ⟨hs1, ?_, ?_⟩
  · apply (le_div_iff₀ (by linarith : 0 < s - 1)).mpr
    linarith
  · unfold restrictionInputExponent
    apply (div_lt_div_iff₀ (by linarith : 0 < s - 1) (by linarith : 0 < (n : ℝ) + 1)).mpr
    have H : 2 * (n : ℝ) < s * ((n : ℝ) - 1) := by
      apply (div_lt_iff₀ (by linarith : 0 < (n : ℝ) - 1)).mp
      exact hs
    nlinarith

/-- The Euclidean wave local-smoothing conjecture implies all conjectured
strict spherical restriction estimates, including mixed input/output
exponents and essentially bounded sphere data. -/
theorem localSmoothing_sphericalRestrictionConjecture (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing) :
    OAI.Analysis.Fourier.Restriction.SphericalRestrictionConjecture := by
  apply sphericalRestriction_of_diagonal
  intro n hn s hs
  obtain ⟨hs1, hq1, hqc⟩ := restriction_dual_exponent hn hs
  obtain ⟨C, hC, HC⟩ := localSmoothing_global_restriction hls hn hq1 hqc
  refine ⟨C.toReal + 1, by positivity, ?_⟩
  intro g hg
  have H := (sphericalExtension_bound_of_restriction hs1 hC (fun f hf _ ↦ HC f hf) hg).2
  apply H.trans
  apply mul_le_mul' _ le_rfl
  calc
    C = ENNReal.ofReal C.toReal := (ENNReal.ofReal_toReal hC).symm
    _ ≤ ENNReal.ofReal (C.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)

/-- Local smoothing implies the actual Kakeya maximal estimates with every
positive loss. -/
theorem localSmoothing_kakeyaMaximalConjecture (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing) :
    OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture :=
  OAI.MeasureTheory.Kakeya.restriction_implies_kakeyaMaximal (localSmoothing_sphericalRestrictionConjecture hls)

/-- Local smoothing implies full Hausdorff dimension for every Kakeya set. -/
theorem localSmoothing_kakeyaConjecture (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing) :
    OAI.MeasureTheory.Kakeya.KakeyaConjecture :=
  OAI.MeasureTheory.Kakeya.kakeyaMaximal_implies_kakeya (localSmoothing_kakeyaMaximalConjecture hls)

end OAI.Analysis.Fourier.Restriction
