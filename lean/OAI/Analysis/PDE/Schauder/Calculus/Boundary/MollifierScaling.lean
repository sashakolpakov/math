import OAI.Analysis.PDE.Schauder.Calculus.Boundary.MollifierSmooth
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.AffineDerivatives

/-! Exact affine covariance and cancellation for the boundary regularization. -/

noncomputable section
open _root_.MeasureTheory Set
namespace OAI.Analysis.PDE.Schauder

theorem regularizedTrace_sub_const {m : ℕ} (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : Continuous h) (c t : ℝ) (z : EuclideanSpace ℝ (Fin m)) :
    regularizedTrace (fun y => h y - c) t z = regularizedTrace h t z - c := by
  unfold regularizedTrace
  simp_rw [mul_sub]
  rw [integral_sub (integrable_regularizedTrace h hh t z)
    ((boundaryMollifier m).integrable_normed.mul_const c), integral_mul_const,
    (boundaryMollifier m).integral_normed, one_mul]

theorem regularizedTrace_affine_data {m : ℕ} (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (t s : ℝ) (z x : EuclideanSpace ℝ (Fin m)) :
    regularizedTrace (fun y => h (z + t • y)) s x =
      regularizedTrace h (t * s) (z + t • x) := by
  unfold regularizedTrace
  apply integral_congr_ae
  filter_upwards with y
  congr 2
  simp only [smul_sub, smul_smul]
  abel

theorem regularizedTrace_affine_cancel {m : ℕ} (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : Continuous h) (t : ℝ) (z : EuclideanSpace ℝ (Fin m)) :
    (fun p : ℝ × EuclideanSpace ℝ (Fin m) =>
      regularizedTrace (fun y => h (z + t • y) - h z) p.1 p.2) =
    (fun p => regularizedTrace h (t • p + (0, z)).1 (t • p + (0, z)).2 - h z) := by
  funext p
  have hc : Continuous (fun y : EuclideanSpace ℝ (Fin m) => h (z + t • y)) :=
    hh.comp (continuous_const.add (continuous_id.const_smul t))
  rw [regularizedTrace_sub_const (fun y => h (z + t • y)) hc, regularizedTrace_affine_data]
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, add_zero,
    add_comm z]

theorem regularizedTrace_derivative_scaling {m : ℕ} (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : Continuous h) {t : ℝ} (ht : t ≠ 0) (z : EuclideanSpace ℝ (Fin m))
    {n : ℕ} (hn : n ≠ 0) :
    ‖iteratedFDeriv ℝ n (fun p : ℝ × EuclideanSpace ℝ (Fin m) =>
      regularizedTrace (fun y => h (z + t • y) - h z) p.1 p.2) (1, 0)‖ =
    |t| ^ n * ‖iteratedFDeriv ℝ n (fun p : ℝ × EuclideanSpace ℝ (Fin m) =>
      regularizedTrace h p.1 p.2) (t, z)‖ := by
  rw [regularizedTrace_affine_cancel h hh t z, norm_iteratedFDeriv_sub_const _ _ _ hn]
  have hs := norm_iteratedFDeriv_affine_scalar
    (fun p : ℝ × EuclideanSpace ℝ (Fin m) => regularizedTrace h p.1 p.2) ht (0, z) (1, 0) n
  simpa only [Prod.smul_mk, smul_eq_mul, mul_one, smul_zero, Prod.mk_add_mk, add_zero, zero_add] using hs

end OAI.Analysis.PDE.Schauder
