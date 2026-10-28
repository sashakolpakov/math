import OAI.Analysis.Calculus.Current.Fiber.Coercivity
import OAI.Analysis.Calculus.Current.Fiber.TimeBounds

/-! Exact row scaling from the compact model to the actual fiber Hessian. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

open OAI.Analysis.Calculus.Quaternion
open scoped Matrix Matrix.Norms.Elementwise

def fiberRowScale {d : ℕ} (a : ℝ) (z : Index d → ℂ) : Option (Fin d) → ℂ
  | none => (a : ℂ) / 10
  | some _ => z none / 10

theorem baseFiberJacobian_entry {d : ℕ} (a : ℝ) (ha : a ≠ 0)
    (z : Index d → ℂ) (hY : z none ≠ 0) (i : Option (Fin d)) (b : Index d) :
    baseFiberJacobian (ratio z) i b = complexK (fiberRowScale a z i) *
      quaternionFiberJacobian (1 / 10) a z i b := by
  classical
  change complexK (fiberJacobian 1 10 (modelFiberPoint (ratio z)) i b) =
    complexK (fiberRowScale a z i) * complexK (fiberJacobian (1 / 10) a z i b)
  rw [← map_mul]
  congr 1
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  cases i with
  | none => simp [fiberJacobian, fiberRowScale, ratio_modelFiberPoint]; field_simp
  | some i =>
    cases b with
    | none => simp [fiberJacobian, fiberRowScale, ratioRow, ratio_modelFiberPoint, modelFiberPoint]; field_simp
    | some b =>
      cases b with
      | none => simp [fiberJacobian, fiberRowScale, ratioRow]
      | some j => by_cases hji : j = i <;>
          simp [fiberJacobian, fiberRowScale, ratioRow, modelFiberPoint, hji] ; field_simp

theorem baseFiberJacobian_mulVec {d : ℕ} (a : ℝ) (ha : a ≠ 0)
    (z : Index d → ℂ) (hY : z none ≠ 0) (v : Index d → OAI.Analysis.Calculus.Quaternion.Q) :
    baseFiberJacobian (ratio z) *ᵥ v = fun i => complexK (fiberRowScale a z i) *
      (quaternionFiberJacobian (1 / 10) a z *ᵥ v) i := by
  funext i
  simp only [Matrix.mulVec, dotProduct, baseFiberJacobian_entry a ha z hY]
  simp only [Finset.mul_sum, mul_assoc]

theorem baseFiberJacobian_mulVec_norm_le {d : ℕ} (a : ℝ) (ha : 0 < a)
    (z : Index d → ℂ) (hay : a ≤ ‖z none‖) (v : Index d → OAI.Analysis.Calculus.Quaternion.Q) :
    ‖baseFiberJacobian (ratio z) *ᵥ v‖ ≤ (‖z none‖ / 10) *
      ‖quaternionFiberJacobian (1 / 10) a z *ᵥ v‖ := by
  have hY : z none ≠ 0 := norm_pos_iff.mp (ha.trans_le hay)
  rw [baseFiberJacobian_mulVec a ha.ne' z hY]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [norm_mul, complexK_norm]
  have hs : ‖fiberRowScale a z i‖ ≤ ‖z none‖ / 10 := by
    cases i with
    | none => simpa [fiberRowScale, norm_div, abs_of_pos ha] using
        div_le_div_of_nonneg_right hay (by norm_num : (0 : ℝ) ≤ 10)
    | some i => simp [fiberRowScale]
  exact mul_le_mul hs (norm_le_pi_norm _ i) (norm_nonneg _) (by positivity)

theorem pi_norm_sq_le_sum {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    (v : ι → E) : ‖v‖ ^ 2 ≤ ∑ i, ‖v i‖ ^ 2 := by
  have hs : 0 ≤ ∑ i, ‖v i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hn : ‖v‖ ≤ Real.sqrt (∑ i, ‖v i‖ ^ 2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    have hi : ‖v i‖ ^ 2 ≤ ∑ j, ‖v j‖ ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖v j‖) (Finset.mem_univ i)
    nlinarith [Real.sq_sqrt hs, Real.sqrt_nonneg (∑ i, ‖v i‖ ^ 2), norm_nonneg (v i)]
  nlinarith [Real.sq_sqrt hs, norm_nonneg v]

theorem fiberHessian_form_lower_jacobian {d : ℕ} (a : ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) (v : Index d → OAI.Analysis.Calculus.Quaternion.Q) :
    4 * ‖quaternionFiberJacobian (1 / 10) a z *ᵥ v‖ ^ 2 ≤
      (star v ⬝ᵥ (fiberHessian (1 / 10) a z *ᵥ v)).re := by
  rw [fiberHessian_factorization _ _ _ hY, Matrix.smul_mulVec, dotProduct_smul,
    Quaternion.re_smul, smul_eq_mul, OAI.Analysis.Calculus.Quaternion.quaternionGram_quadratic]
  have h := pi_norm_sq_le_sum (quaternionFiberJacobian (1 / 10) a z *ᵥ v)
  simp only [Quaternion.normSq_eq_norm_mul_self, ← pow_two]
  linarith

theorem fiberHessian_uniform_weighted_lower (d : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : ℝ) (z : Index d → ℂ), 0 < a → a ≤ ‖z none‖ →
      fiberDefining (1 / 10) a z ≤ 0 → ∀ v : Option (Fin d) → OAI.Analysis.Calculus.Quaternion.Q,
      c * ‖v‖ ^ 2 ≤ ‖z none‖ ^ 2 *
        (star (fiberSpatialLift v) ⬝ᵥ (fiberHessian (1 / 10) a z *ᵥ fiberSpatialLift v)).re := by
  obtain ⟨c, hc, hbase⟩ := baseFiberJacobian_uniform_lower d
  refine ⟨400 * c, by positivity, ?_⟩
  intro a z ha hay hr v
  have hW : ratio z ∈ admissibleRatios d := fiber_ratio_bound (1 / 10) a z (by norm_num) hr
  have h₁ := hbase (ratio z) hW v
  have h₂ := pow_le_pow_left₀ (norm_nonneg _) (baseFiberJacobian_mulVec_norm_le a ha z hay (fiberSpatialLift v)) 2
  have h₃ := fiberHessian_form_lower_jacobian a z (norm_pos_iff.mp (ha.trans_le hay)) (fiberSpatialLift v)
  have h₄ := mul_le_mul_of_nonneg_left h₃ (sq_nonneg ‖z none‖)
  nlinarith

end OAI.Analysis.Calculus.Current
