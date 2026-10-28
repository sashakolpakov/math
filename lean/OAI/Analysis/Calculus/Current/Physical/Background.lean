import OAI.Analysis.Calculus.Current.Physical.Hessian

/-! Uniform nondegeneracy of the background on physical spatial fibers. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

open OAI.Analysis.Calculus.Quaternion
open scoped Matrix

def physicalPhaseRow {d : ℕ} (z : Index d → ℂ) : Option (Fin d) → ℂ
  | none => (Real.sqrt 2)⁻¹ • (1 - fiberQuadratic (ratio z) / 2)
  | some i => ratio z i

theorem physicalPhaseRow_eq_jacobian {d : ℕ} (z : Index d → ℂ) :
    physicalPhaseRow z = physicalFiberJacobian 1 10 z none := by
  funext b
  cases b with
  | none =>
    simp [physicalPhaseRow, physicalFiberJacobian, fiberJacobian, phaseRow, fiberQuadratic]
    ring
  | some i => simp [physicalPhaseRow, physicalFiberJacobian, fiberJacobian, phaseRow]

theorem fderiv_physicalPhi_single {d : ℕ} (τ : ℂ) (q : Option (Fin d) → ℂ)
    (hY : physicalEmbedding τ q none ≠ 0) (b : Option (Fin d)) :
    fderiv ℂ (fun p => phi (physicalEmbedding τ p)) q (Pi.single b 1) =
      physicalPhaseRow (physicalEmbedding τ q) b := by
  have he : (fun p : Option (Fin d) → ℂ => fiberMap 1 10 (physicalEmbedding τ p) none) =
      (fun p => phi (physicalEmbedding τ p)) := by funext p; simp [fiberMap]
  rw [physicalPhaseRow_eq_jacobian, ← he]
  exact fderiv_physicalFiberMap_single 1 10 τ q hY none b

def physicalBackgroundHessian {d : ℕ} (τ : ℂ) (q : Option (Fin d) → ℂ) :
    Matrix (Option (Fin d)) (Option (Fin d)) OAI.Analysis.Calculus.Quaternion.Q :=
  OAI.Analysis.Calculus.Quaternion.imaginaryHessian (fun p => ‖phi (physicalEmbedding τ p)‖ ^ 2) q

theorem physicalBackgroundHessian_diag {d : ℕ} (τ : ℂ) (q : Option (Fin d) → ℂ)
    (hY : physicalEmbedding τ q none ≠ 0) (b : Option (Fin d)) :
    (physicalBackgroundHessian τ q b b).re = 4 * ‖physicalPhaseRow (physicalEmbedding τ q) b‖ ^ 2 := by
  have he : (fun p : Option (Fin d) → ℂ => fiberMap 1 10 (physicalEmbedding τ p) none) =
      (fun p => phi (physicalEmbedding τ p)) := by funext p; simp [fiberMap]
  have hf : ContDiffAt ℂ 2 (fun p => phi (physicalEmbedding τ p)) q := by
    rw [← he]
    exact (contDiffAt_fiberMap_complex 1 10 (physicalEmbedding τ q) hY none).comp q
      (contDiff_physicalEmbedding_complex τ).contDiffAt
  rw [physicalBackgroundHessian, OAI.Analysis.Calculus.Quaternion.imaginaryHessian_norm_sq hf,
    fderiv_physicalPhi_single τ q hY b]
  simp [complexK, Complex.mul_re, pow_two]
  simpa only [Complex.normSq_apply, pow_two] using
    Complex.normSq_eq_norm_sq (physicalPhaseRow (physicalEmbedding τ q) b)

theorem physicalBackgroundHessian_trace_formula {d : ℕ} (τ : ℂ) (q : Option (Fin d) → ℂ)
    (hY : physicalEmbedding τ q none ≠ 0) :
    (∑ b, (physicalBackgroundHessian τ q b b).re) =
      2 * ‖1 - fiberQuadratic (ratio (physicalEmbedding τ q)) / 2‖ ^ 2 +
        4 * ∑ i, ‖ratio (physicalEmbedding τ q) i‖ ^ 2 := by
  simp only [physicalBackgroundHessian_diag τ q hY, Fintype.sum_option, physicalPhaseRow,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
    mul_pow, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), ← Finset.mul_sum]
  ring

theorem physicalBackgroundHessian_trace_bounds {d : ℕ} (a : ℝ) (τ : ℂ)
    (q : Option (Fin d) → ℂ) (hY : physicalEmbedding τ q none ≠ 0)
    (hr : physicalFiberDefining (1 / 10) a τ q ≤ 0) :
    1 ≤ (∑ b, (physicalBackgroundHessian τ q b b).re) ∧
      (∑ b, (physicalBackgroundHessian τ q b b).re) ≤ 3 := by
  let z := physicalEmbedding τ q
  have hW := fiber_ratio_bound (1 / 10) a z (by norm_num) hr
  have hW0 : 0 ≤ ∑ i, ‖ratio z i‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hQ := (norm_fiberQuadratic_le (ratio z)).trans hW
  have hq : ‖fiberQuadratic (ratio z) / 2‖ ≤ (1 / 200 : ℝ) := by
    rw [norm_div]
    norm_num
    linarith
  have hu := norm_sub_le (1 : ℂ) (fiberQuadratic (ratio z) / 2)
  have hl := norm_sub_norm_le (1 : ℂ) (fiberQuadratic (ratio z) / 2)
  simp only [norm_one] at hu hl
  have hNl : (199 / 200 : ℝ) ≤ ‖1 - fiberQuadratic (ratio z) / 2‖ := by linarith
  have hNu : ‖1 - fiberQuadratic (ratio z) / 2‖ ≤ (201 / 200 : ℝ) := by linarith
  rw [physicalBackgroundHessian_trace_formula τ q hY]
  change 1 ≤ 2 * ‖1 - fiberQuadratic (ratio z) / 2‖ ^ 2 + 4 * ∑ i, ‖ratio z i‖ ^ 2 ∧
    2 * ‖1 - fiberQuadratic (ratio z) / 2‖ ^ 2 + 4 * ∑ i, ‖ratio z i‖ ^ 2 ≤ 3
  constructor <;> nlinarith [norm_nonneg (1 - fiberQuadratic (ratio z) / 2)]

end OAI.Analysis.Calculus.Current
