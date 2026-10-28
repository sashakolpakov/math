import OAI.Analysis.Fourier.SquareFunction.BoundarySquare
import OAI.Analysis.Fourier.SquareFunction.SmoothRadiusLp
import OAI.Analysis.Fourier.SquareFunction.Square.Dyadic
import OAI.Analysis.Fourier.BochnerRiesz.FiniteFourier

open OAI.Analysis.Fourier.Wave

/-! Exact decomposition of the differentiated Bochner--Riesz operator
into the singular boundary part and its smooth interior remainder. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform Set
open scoped ENNReal

theorem boundary_add_smooth_remainder {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : Continuous A) (hc : HasCompactSupport A) (α : ℝ) (r : RadiusInterval)
    (heq : ∀ ξ : Space n, A (r, ξ) = (radiusMultiplier α ‖ξ‖ r : ℂ) *
      (1 - (OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff (4 * ((r : ℝ) - ‖ξ‖)) : ℂ)))
    (f : SchwartzMap (Space n) ℂ)
    (hi : Integrable (fun ξ : Space n => (radiusMultiplier α ‖ξ‖ r : ℂ) * (𝓕 f) ξ))
    (x : Space n) :
    boundaryRadiusDerivative α r f x + smoothRadiusOutput A hA f x r =
      radiusDerivativeCycles α r f x := by
  let b : Space n → ℂ := fun ξ => (radiusMultiplier α ‖ξ‖ r : ℂ) *
    (OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff (4 * ((r : ℝ) - ‖ξ‖)) : ℂ) * (𝓕 f) ξ
  let q : Space n → ℂ := fun ξ => A (r, ξ) * (𝓕 f) ξ
  have hq : Integrable q :=
    ((hA.comp (continuous_const.prodMk continuous_id)).mul (𝓕 f).continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_radius_slice hc r).mul_right
  have hb : Integrable b := (hi.sub hq).congr (Filter.Eventually.of_forall fun ξ => by
    dsimp only [Pi.sub_apply, b, q]
    rw [heq ξ]
    ring)
  have hs : (fun ξ => b ξ + q ξ) =
      (fun ξ : Space n => (radiusMultiplier α ‖ξ‖ r : ℂ) * (𝓕 f) ξ) := by
    funext ξ
    dsimp only [b, q]
    rw [heq ξ]
    ring
  rw [smoothRadiusOutput_apply A hA hc f.integrable, ← SchwartzMap.fourier_coe]
  change 𝓕⁻ b x + 𝓕⁻ q x = _
  rw [← congrFun (OAI.Analysis.Fourier.BochnerRiesz.fourierInv_add_integrable hb hq) x, hs]
  rfl

theorem dyadic_smooth_remainder_radius_norm {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : Continuous A) (hc : HasCompactSupport A) (f : SchwartzMap (Space n) ℂ)
    (x : Space n) :
    dyadicRadiusNorm (volume.restrict (Icc (1 : ℝ) 2)) (fun k r =>
      𝓕⁻ (fun ξ : Space n => A (r, ξ) * 𝓕
        (OAI.Analysis.Fourier.BochnerRiesz.schwartzDilate ((2 : ℝ) ^ k)⁻¹ (by positivity) f : Space n → ℂ) ξ)
        ((2 : ℝ) ^ k • x)) =
      dyadicSmoothRadiusSquare A hA f x := by
  unfold dyadicRadiusNorm dyadicSmoothRadiusSquare countableSquareNorm
  congr 1
  apply tsum_congr
  intro k
  congr 1
  dsimp only
  rw [convolve_dilatedKernel _ _ (by positivity)]
  let g := OAI.Analysis.Fourier.BochnerRiesz.schwartzDilate ((2 : ℝ) ^ k)⁻¹ (by positivity) f
  change _ = ‖convolveKernel (smoothRadiusKernel A hA) g ((2 : ℝ) ^ k • x)‖ₑ
  rw [convolve_smoothRadiusKernel A hA hc g.integrable,
    enorm_smoothRadiusOutput A hA hc g.integrable]

theorem steinSquareFunction_le_boundary_add_remainder {n : ℕ} [NeZero n]
    {A : ℝ × Space n → ℂ} (hA : Continuous A) (hc : HasCompactSupport A)
    {α : ℝ} (hα : 1 / 2 < α)
    (heq : ∀ r ∈ Icc (1 : ℝ) 2, ∀ ξ : Space n,
      A (r, ξ) = (radiusMultiplier α ‖ξ‖ r : ℂ) *
        (1 - (OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff (4 * (r - ‖ξ‖)) : ℂ)))
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    OAI.Analysis.Fourier.SquareFunction.steinSquareFunction α f x ≤
      dyadicBoundarySquare α f x + dyadicSmoothRadiusSquare A hA f x := by
  let g (k : ℤ) := OAI.Analysis.Fourier.BochnerRiesz.schwartzDilate ((2 : ℝ) ^ k)⁻¹ (by positivity) f
  let b (k : ℤ) (r : ℝ) := boundaryRadiusDerivative α r (g k) ((2 : ℝ) ^ k • x)
  let q (k : ℤ) (r : ℝ) :=
    𝓕⁻ (fun ξ : Space n => A (r, ξ) * 𝓕 (g k : Space n → ℂ) ξ) ((2 : ℝ) ^ k • x)
  have he : ∀ k : ℤ, (fun r => radiusDerivativeCycles α ((2 : ℝ) ^ k * r) f x) =ᵐ[
      volume.restrict (Icc (1 : ℝ) 2)] (fun r => b k r + q k r) := by
    intro k
    have hs : Icc (1 : ℝ) 2 ⊆ Ioi 0 := fun r hr => lt_of_lt_of_le (by norm_num) hr.1
    have hi := ae_restrict_of_ae_restrict_of_subset hs (ae_integrable_radius_symbol_schwartz hα (g k))
    filter_upwards [hi, ae_restrict_mem measurableSet_Icc] with r hir hr
    have H := boundary_add_smooth_remainder hA hc α ⟨r, hr⟩ (heq r hr) (g k) hir ((2 : ℝ) ^ k • x)
    rw [smoothRadiusOutput_apply A hA hc (g k).integrable] at H
    change b k r + q k r = radiusDerivativeCycles α r (g k) ((2 : ℝ) ^ k • x) at H
    exact (radiusDerivativeCycles_dilate α r (a := (2 : ℝ) ^ k)
      (by positivity) f x).symm.trans H.symm
  apply (steinSquareFunction_le_dyadic_radius_norms α f x).trans
  change dyadicRadiusNorm _ _ ≤ _
  rw [dyadicRadiusNorm_congr_ae he]
  apply (dyadicRadiusNorm_add_le _ b q).trans_eq
  rw [show dyadicRadiusNorm (volume.restrict (Icc (1 : ℝ) 2)) q =
      dyadicSmoothRadiusSquare A hA f x from dyadic_smooth_remainder_radius_norm hA hc f x]
  rfl

end OAI.Analysis.Fourier.SquareFunction
