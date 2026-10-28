import OAI.Analysis.Fourier.Restriction.FiniteFourier
import OAI.Analysis.Fourier.Restriction.Sparse.PartitionNorm

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem sparse_annulus_measure_le {n : ℕ} {R : ℝ} (hR : 1 ≤ R) :
    volume (sphericalAnnulus (n := n) ((2 * R)⁻¹)) ≤ volume (closedBall (0 : Space n) 2) := by
  exact measure_mono (sphericalAnnulus_subset_closedBall (by have := (sparse_annulus_width hR).2; linarith))

theorem sparse_annulus_finite {n : ℕ} {R : ℝ} (hR : 1 ≤ R) :
    IsFiniteMeasure (volume.restrict (sphericalAnnulus (n := n) ((2 * R)⁻¹))) := by
  constructor
  rw [Measure.restrict_apply_univ]
  exact (sparse_annulus_measure_le hR).trans_lt (measure_closedBall_lt_top)

theorem sparse_fourier_identity {n N : ℕ} (u : SchwartzMap (Space n) ℂ)
    {c R : ℝ} (hc : 0 < c) (hR : 1 ≤ R)
    (hu : ∀ x, ‖x‖ ≤ 1 → c ≤ ‖u x‖)
    (hF : ∀ ξ, ‖OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ‖ ≤ 1)
    (hFs : ∀ ξ, 1 / 8 ≤ ‖ξ‖ → OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ = 0)
    (z : Fin N → Space n)
    (hd : Pairwise (fun i j ↦ Disjoint (ball (z i) R) (ball (z j) R)))
    {f : Space n → ℂ} (hfm : Measurable f) (hfi : Integrable f)
    (hfs : ∀ x, (∀ i, x ∉ ball (z i) R) → f x = 0)
    (ω : Space n) (hω : ‖ω‖ = 1) :
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ω = (((2 * Real.pi) ^ n)⁻¹ : ℝ) •
      integralKernel (Measure.count.prod (volume.restrict (sphericalAnnulus ((2 * R)⁻¹))))
        (indexedLocalizedKernel u R z)
        (fun p : Fin N × Space n ↦ OAI.Analysis.Fourier.LocalSmoothing.angularFourier (sparsePiece u R (z p.1) f) p.2) ω := by
  let g (i : Fin N) := sparsePiece u R (z i) f
  let ν := volume.restrict (sphericalAnnulus (n := n) ((2 * R)⁻¹))
  have : IsFiniteMeasure ν := sparse_annulus_finite hR
  have hR0 : 0 < R := by linarith
  have hg (i : Fin N) : Integrable (g i) := integrable_sparsePiece u hc hR0 hu (z i) hfm hfi
  have hrecover (i : Fin N) : (fun x ↦ g i (x - z i) * u (R⁻¹ • (x - z i))) = (ball (z i) R).indicator f := by
    funext x
    exact sparsePiece_recover u hc hR0 hu (z i) f x
  calc
    _ = OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ ∑ i, (ball (z i) R).indicator f x) ω := by
      congr 1
      funext x
      exact (sum_ball_indicators_eq z R hd f hfs x).symm
    _ = ∑ i, OAI.Analysis.Fourier.LocalSmoothing.angularFourier ((ball (z i) R).indicator f) ω :=
      angularFourier_sum Finset.univ _ (fun i _ ↦ hfi.indicator measurableSet_ball) ω
    _ = ∑ i, (((2 * Real.pi) ^ n)⁻¹ : ℝ) •
        ∫ ξ, localizedFourierKernel u R (z i) ω ξ * OAI.Analysis.Fourier.LocalSmoothing.angularFourier (g i) ξ ∂ν := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← hrecover i]
      exact localizedFourierKernel_annulus_reconstruction (hg i) u hFs hR0 (z i) ω hω
    _ = (((2 * Real.pi) ^ n)⁻¹ : ℝ) •
        ∑ i, ∫ ξ, localizedFourierKernel u R (z i) ω ξ * OAI.Analysis.Fourier.LocalSmoothing.angularFourier (g i) ξ ∂ν := by
      rw [Finset.smul_sum]
    _ = _ := by
      congr 1
      exact (integralKernel_finite_sum u hF hR0 z ν (integrable_finite_fourier g hg ν) ω).symm

end OAI.Analysis.Fourier.Restriction
