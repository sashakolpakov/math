import OAI.Analysis.PDE.Schauder.Boundary.Jet.LiftRegularization
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.KernelIntegral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! The actual moving-scale smoothing kernel and its change-of-variables formula. -/

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped ContDiff Topology
namespace OAI.Analysis.PDE.Schauder

def boundarySmoothingKernel (m : ℕ)
    (q : (ℝ × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin m)) : ℝ :=
  (|q.1.1| ^ m)⁻¹ * (boundaryMollifier m).normed volume (q.1.1⁻¹ • (q.1.2 - q.2))

theorem regularizedTrace_kernel {m : ℕ} (h : EuclideanSpace ℝ (Fin m) → ℝ)
    {t : ℝ} (ht : t ≠ 0) (z : EuclideanSpace ℝ (Fin m)) :
    regularizedTrace h t z = ∫ y, boundarySmoothingKernel m ((t, z), y) * h y := by
  let f := fun y : EuclideanSpace ℝ (Fin m) =>
    (boundaryMollifier m).normed volume (t⁻¹ • y) * h (z - y)
  have hi := Measure.integral_comp_smul volume f t
  have he : (fun y => f (t • y)) =
      (fun y => (boundaryMollifier m).normed volume y * h (z - t • y)) := by
    funext y
    simp only [f, inv_smul_smul₀ ht]
  rw [he] at hi
  change regularizedTrace h t z = _ at hi
  rw [finrank_euclideanSpace, Fintype.card_fin, abs_inv, abs_pow, smul_eq_mul] at hi
  rw [hi]
  have hs := integral_sub_left_eq_self f volume z
  rw [← hs, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  simp only [boundarySmoothingKernel, f, sub_sub_cancel]
  ring

theorem contDiffOn_boundarySmoothingKernel (m : ℕ) :
    ContDiffOn ℝ ∞ (boundarySmoothingKernel m) {q | q.1.1 ≠ 0} := by
  intro q hq
  have ht : ContDiffAt ℝ ∞ (fun p : (ℝ × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin m) => p.1.1) q :=
    contDiffAt_fst.fst
  have hz : ContDiffAt ℝ ∞ (fun p : (ℝ × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin m) => p.1.2 - p.2) q :=
    contDiffAt_fst.snd.sub contDiffAt_snd
  have harg := (ht.inv hq).smul hz
  have hρ : ContDiff ℝ ∞ ((boundaryMollifier m).normed volume) :=
    (boundaryMollifier m).contDiff_normed (μ := volume)
  exact (((ht.abs hq).pow m).inv (pow_ne_zero _ (abs_ne_zero.mpr hq))).mul
    (hρ.contDiffAt.comp q harg) |>.contDiffWithinAt

theorem boundarySmoothingKernel_eq_zero {m : ℕ} {t : ℝ} (ht : t ≠ 0)
    (z y : EuclideanSpace ℝ (Fin m)) (hy : |t| + ‖z‖ < ‖y‖) :
    boundarySmoothingKernel m ((t, z), y) = 0 := by
  suffices hzero : (boundaryMollifier m).normed volume (t⁻¹ • (z - y)) = 0 by
    simp only [boundarySmoothingKernel, hzero, mul_zero]
  by_contra hn
  have hm : t⁻¹ • (z - y) ∈ ball (0 : EuclideanSpace ℝ (Fin m)) 1 := by
    change t⁻¹ • (z - y) ∈ ball (0 : EuclideanSpace ℝ (Fin m)) (boundaryMollifier m).rOut
    rw [← (boundaryMollifier m).support_normed_eq (μ := volume)]
    exact hn
  have hb : ‖z - y‖ < |t| := by
    have hh := mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hm) (abs_pos.mpr ht)
    rw [← Real.norm_eq_abs t, ← norm_smul, smul_inv_smul₀ ht, mul_one] at hh
    simpa only [Real.norm_eq_abs] using hh
  have hn := norm_sub_le z (z - y)
  rw [sub_sub_cancel] at hn
  linarith

end OAI.Analysis.PDE.Schauder
