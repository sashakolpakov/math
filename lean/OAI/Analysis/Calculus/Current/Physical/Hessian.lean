import OAI.Analysis.Calculus.Current.Physical.Fiber
import OAI.Analysis.Calculus.Current.Fiber.Ellipticity

/-! The actual quaternionic Hessian of the physically normalized fixed-time fiber. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

open OAI.Analysis.Calculus.Quaternion
open scoped Matrix Matrix.Norms.Elementwise

def physicalComplexLift (d : ℕ) : (Option (Fin d) → ℂ) →L[ℂ] (Index d → ℂ) :=
  ContinuousLinearMap.pi fun b => match b with
    | none => ((Real.sqrt 2 : ℂ)⁻¹) • ContinuousLinearMap.proj none
    | some none => ((Real.sqrt 2 : ℂ)⁻¹) • ContinuousLinearMap.proj none
    | some (some i) => ContinuousLinearMap.proj (some i)

theorem physicalComplexLift_apply {d : ℕ} (v : Option (Fin d) → ℂ) :
    physicalComplexLift d v = physicalLift d v := by
  funext b
  cases b with
  | none => simp [physicalComplexLift, physicalLift, Complex.real_smul]
  | some b => cases b <;> simp [physicalComplexLift, physicalLift, Complex.real_smul]

theorem hasFDerivAt_physicalEmbedding_complex {d : ℕ} (τ : ℂ) (q : Option (Fin d) → ℂ) :
    HasFDerivAt (physicalEmbedding τ) (physicalComplexLift d) q := by
  simpa only [physicalComplexLift_apply, physicalEmbedding] using!
    (physicalComplexLift d).hasFDerivAt.add_const (physicalTimeOffset τ)

theorem contDiff_physicalEmbedding_complex {d : ℕ} (τ : ℂ) :
    ContDiff ℂ 2 (physicalEmbedding (d := d) τ) := by
  simpa only [physicalComplexLift_apply, physicalEmbedding] using!
    (physicalComplexLift d).contDiff.add (contDiff_const (c := physicalTimeOffset τ))

def physicalFiberJacobian {d : ℕ} (w a : ℝ) (z : Index d → ℂ) :
    Matrix (Option (Fin d)) (Option (Fin d)) ℂ := fun i b => match b with
  | none => (Real.sqrt 2)⁻¹ • (fiberJacobian w a z i none + fiberJacobian w a z i (some none))
  | some j => fiberJacobian w a z i (some (some j))

theorem fderiv_physicalFiberMap_single {d : ℕ} (w a : ℝ) (τ : ℂ)
    (q : Option (Fin d) → ℂ) (hY : physicalEmbedding τ q none ≠ 0)
    (i b : Option (Fin d)) :
    fderiv ℂ (fun p => fiberMap w a (physicalEmbedding τ p) i) q (Pi.single b 1) =
      physicalFiberJacobian w a (physicalEmbedding τ q) i b := by
  have hf := (contDiffAt_fiberMap_complex w a (physicalEmbedding τ q) hY i).differentiableAt (by norm_num)
  have he := hasFDerivAt_physicalEmbedding_complex τ q
  have hh := hf.hasFDerivAt.comp q he
  change fderiv ℂ ((fun z => fiberMap w a z i) ∘ physicalEmbedding τ) q (Pi.single b 1) = _
  rw [hh.fderiv, ContinuousLinearMap.comp_apply, fderiv_fiberMap w a _ _ hY i]
  cases b with
  | none =>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_option, physicalComplexLift,
      physicalFiberJacobian, Complex.real_smul]
    ring
  | some b =>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_option, physicalComplexLift,
      physicalFiberJacobian, Pi.single_apply]

def physicalQuaternionJacobian {d : ℕ} (w a : ℝ) (z : Index d → ℂ) :
    Matrix (Option (Fin d)) (Option (Fin d)) OAI.Analysis.Calculus.Quaternion.Q := fun i b => complexK (physicalFiberJacobian w a z i b)

def physicalFiberHessian {d : ℕ} (w a : ℝ) (τ : ℂ) (q : Option (Fin d) → ℂ) :
    Matrix (Option (Fin d)) (Option (Fin d)) OAI.Analysis.Calculus.Quaternion.Q := OAI.Analysis.Calculus.Quaternion.imaginaryHessian (physicalFiberDefining w a τ) q

theorem physicalFiberHessian_factorization {d : ℕ} (w a : ℝ) (τ : ℂ)
    (q : Option (Fin d) → ℂ) (hY : physicalEmbedding τ q none ≠ 0) :
    physicalFiberHessian w a τ q = (4 : ℝ) •
      ((physicalQuaternionJacobian w a (physicalEmbedding τ q))ᴴ *
        physicalQuaternionJacobian w a (physicalEmbedding τ q)) := by
  change OAI.Analysis.Calculus.Quaternion.imaginaryHessian (fun p => (∑ i, ‖fiberMap w a (physicalEmbedding τ p) i‖ ^ 2) - 1) q = _
  rw [OAI.Analysis.Calculus.Quaternion.imaginaryHessian_sub_const]
  have hh := OAI.Analysis.Calculus.Quaternion.imaginaryHessian_holomorphic_squares
    (fun i p => fiberMap w a (physicalEmbedding τ p) i)
    (fun i => (contDiffAt_fiberMap_complex w a (physicalEmbedding τ q) hY i).comp q
      (contDiff_physicalEmbedding_complex τ).contDiffAt)
  simpa only [fderiv_physicalFiberMap_single w a τ q hY, physicalQuaternionJacobian,
    Matrix.of_apply] using! hh

def physicalQuaternionScale {d : ℕ} (v : Option (Fin d) → OAI.Analysis.Calculus.Quaternion.Q) : Option (Fin d) → OAI.Analysis.Calculus.Quaternion.Q
  | none => (Real.sqrt 2)⁻¹ • v none
  | some i => v (some i)

def physicalQuaternionLift {d : ℕ} (v : Option (Fin d) → OAI.Analysis.Calculus.Quaternion.Q) : Index d → OAI.Analysis.Calculus.Quaternion.Q :=
  fiberSpatialLift (physicalQuaternionScale v)

theorem complexK_smul_real (c : ℝ) (z : ℂ) : complexK (c • z) = c • complexK z := by
  simpa only [complexKCLM_apply] using complexKCLM.map_smul c z

theorem physicalQuaternionJacobian_mulVec {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (v : Option (Fin d) → OAI.Analysis.Calculus.Quaternion.Q) :
    physicalQuaternionJacobian w a z *ᵥ v = quaternionFiberJacobian w a z *ᵥ physicalQuaternionLift v := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_option, physicalQuaternionJacobian,
    physicalFiberJacobian, physicalQuaternionLift, fiberSpatialLift, physicalQuaternionScale,
    quaternionFiberJacobian, complexK_smul_real, map_add, add_mul, smul_mul_assoc, mul_smul_comm]
  module

theorem physicalFiberHessian_quadratic {d : ℕ} (w a : ℝ) (τ : ℂ)
    (q : Option (Fin d) → ℂ) (hY : physicalEmbedding τ q none ≠ 0)
    (v : Option (Fin d) → OAI.Analysis.Calculus.Quaternion.Q) :
    (star v ⬝ᵥ (physicalFiberHessian w a τ q *ᵥ v)).re =
      (star (physicalQuaternionLift v) ⬝ᵥ
        (fiberHessian w a (physicalEmbedding τ q) *ᵥ physicalQuaternionLift v)).re := by
  rw [physicalFiberHessian_factorization w a τ q hY,
    fiberHessian_factorization w a (physicalEmbedding τ q) hY]
  simp only [Matrix.smul_mulVec, dotProduct_smul, Quaternion.re_smul, smul_eq_mul,
    OAI.Analysis.Calculus.Quaternion.quaternionGram_quadratic, physicalQuaternionJacobian_mulVec]

theorem physicalQuaternionScale_norm_lower {d : ℕ} (v : Option (Fin d) → OAI.Analysis.Calculus.Quaternion.Q) :
    ‖v‖ ≤ 2 * ‖physicalQuaternionScale v‖ := by
  have hs0 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hs : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_iff]; norm_num
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro b
  cases b with
  | none =>
    have he : v none = Real.sqrt 2 • physicalQuaternionScale v none := by
      simp [physicalQuaternionScale, smul_smul, hs0]
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul hs (norm_le_pi_norm _ none) (norm_nonneg _) (by norm_num)
  | some i =>
    have hi : ‖v (some i)‖ ≤ ‖physicalQuaternionScale v‖ :=
      norm_le_pi_norm (physicalQuaternionScale v) (some i)
    nlinarith [norm_nonneg (physicalQuaternionScale v)]

theorem physicalFiberHessian_uniform_lower (d : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : ℝ) (τ : ℂ) (q : Option (Fin d) → ℂ),
      0 < a → a ≤ ‖τ‖ → ‖τ‖ ≤ 4 → physicalFiberDefining (1 / 10) a τ q ≤ 0 →
      ∀ v : Option (Fin d) → OAI.Analysis.Calculus.Quaternion.Q,
        c * ‖v‖ ^ 2 ≤ (star v ⬝ᵥ (physicalFiberHessian (1 / 10) a τ q *ᵥ v)).re := by
  obtain ⟨c, hc, hb⟩ := fiberHessian_uniform_spatial_lower d
  refine ⟨c / 4, by positivity, ?_⟩
  intro a τ q ha ht ht' hr v
  have hay := fiber_height_ge_scale a ha (physicalEmbedding τ q) hr
    (by simpa only [imaginaryTime_physicalEmbedding] using ht)
  have hY : physicalEmbedding τ q none ≠ 0 := norm_ne_zero_iff.mp (ha.trans_le hay).ne'
  have hh := hb a (physicalEmbedding τ q) ha hr
    (by simpa only [imaginaryTime_physicalEmbedding] using ht)
    (by simpa only [imaginaryTime_physicalEmbedding] using ht') (physicalQuaternionScale v)
  rw [physicalFiberHessian_quadratic _ _ _ _ hY]
  change c / 4 * ‖v‖ ^ 2 ≤ fiberSpatialForm a (physicalEmbedding τ q) (physicalQuaternionScale v)
  have hn := physicalQuaternionScale_norm_lower v
  have hs : ‖v‖ ^ 2 ≤ 4 * ‖physicalQuaternionScale v‖ ^ 2 := by
    nlinarith [norm_nonneg v, norm_nonneg (physicalQuaternionScale v)]
  nlinarith

theorem physicalFiberHessian_small_time_lower (d : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : ℝ) (τ : ℂ) (q : Option (Fin d) → ℂ),
      0 < a → a ≤ ‖τ‖ → ‖τ‖ ≤ 4 * a → physicalFiberDefining (1 / 10) a τ q ≤ 0 →
      ∀ v : Option (Fin d) → OAI.Analysis.Calculus.Quaternion.Q,
        (c / a ^ 2) * ‖v‖ ^ 2 ≤ (star v ⬝ᵥ (physicalFiberHessian (1 / 10) a τ q *ᵥ v)).re := by
  obtain ⟨c, hc, hb⟩ := fiberHessian_small_time_spatial_lower d
  refine ⟨c / 4, by positivity, ?_⟩
  intro a τ q ha ht ht' hr v
  have hay := fiber_height_ge_scale a ha (physicalEmbedding τ q) hr
    (by simpa only [imaginaryTime_physicalEmbedding] using ht)
  have hY : physicalEmbedding τ q none ≠ 0 := norm_ne_zero_iff.mp (ha.trans_le hay).ne'
  have hh := hb a (physicalEmbedding τ q) ha hr
    (by simpa only [imaginaryTime_physicalEmbedding] using ht)
    (by simpa only [imaginaryTime_physicalEmbedding] using ht') (physicalQuaternionScale v)
  rw [physicalFiberHessian_quadratic _ _ _ _ hY]
  change c / 4 / a ^ 2 * ‖v‖ ^ 2 ≤ fiberSpatialForm a (physicalEmbedding τ q) (physicalQuaternionScale v)
  have hn := physicalQuaternionScale_norm_lower v
  have hs : ‖v‖ ^ 2 ≤ 4 * ‖physicalQuaternionScale v‖ ^ 2 := by
    nlinarith [norm_nonneg v, norm_nonneg (physicalQuaternionScale v)]
  have hp : 0 < c / a ^ 2 := by positivity
  have hm := mul_le_mul_of_nonneg_left hs hp.le
  have he : c / 4 / a ^ 2 = (c / a ^ 2) / 4 := by ring
  rw [he]
  nlinarith

end OAI.Analysis.Calculus.Current
