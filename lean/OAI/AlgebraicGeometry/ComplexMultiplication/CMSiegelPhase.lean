import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # CM Siegel Phase -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM

noncomputable section

/-!
# Positive complex quadratic phases in real position space

A symmetric complex bilinear form on a finite-dimensional real position
space, whose imaginary part is positive definite, is the basis-independent
form of a Siegel period matrix. Its Gaussian is the actual expression
`exp (π i B(x,x))`. Positivity implies a proved uniform Gaussian bound.
-/

open Filter _root_.Topology _root_.Metric

variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]

structure SiegelPhase where
  form : V →L[ℝ] V →L[ℝ] ℂ
  symmetric : ∀ x y, form x y = form y x
  positive : ∀ x : V, x ≠ 0 → 0 < (form x x).im

namespace SiegelPhase

variable {V} (Z : SiegelPhase V)

def imaginaryQuadratic (x : V) : ℝ := (Z.form x x).im

theorem imaginaryQuadratic_zero : Z.imaginaryQuadratic 0 = 0 := by
  simp [SiegelPhase.imaginaryQuadratic]

theorem imaginaryQuadratic_smul (r : ℝ) (x : V) :
    Z.imaginaryQuadratic (r • x) = r ^ 2 * Z.imaginaryQuadratic x := by
  simp only [SiegelPhase.imaginaryQuadratic, map_smul, smul_apply,
    Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero]
  ring

theorem imaginaryQuadratic_continuous : Continuous Z.imaginaryQuadratic :=
  Complex.continuous_im.comp (Z.form.continuous.clm_apply continuous_id)

theorem imaginaryQuadratic_nonneg (x : V) : 0 ≤ Z.imaginaryQuadratic x := by
  by_cases hx : x = 0
  · rw [hx, Z.imaginaryQuadratic_zero]
  · exact (Z.positive x hx).le

/-- Compactness of the unit sphere supplies a positive quadratic lower
bound, including the zero-dimensional position space. -/
theorem exists_lower_bound [FiniteDimensional ℝ V] :
    ∃ c : ℝ, 0 < c ∧ ∀ x : V, c * ‖x‖ ^ 2 ≤ Z.imaginaryQuadratic x := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact ⟨1, zero_lt_one, fun x => by
      rw [Subsingleton.elim x 0, norm_zero, zero_pow (by decide), mul_zero,
        Z.imaginaryQuadratic_zero]⟩
  · obtain ⟨y, hy, hmin⟩ := (isCompact_sphere (0 : V) 1).exists_isMinOn
      (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1))
      Z.imaginaryQuadratic_continuous.continuousOn
    have hyn : ‖y‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hy
    have hy0 : y ≠ 0 := by intro h; simp [h] at hyn
    refine ⟨Z.imaginaryQuadratic y, Z.positive y hy0, fun x => ?_⟩
    by_cases hx : x = 0
    · simp only [hx, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, mul_zero, Z.imaginaryQuadratic_zero, le_refl]
    · have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      have hunit : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
          inv_mul_cancel₀ hxn]
      have hb := hmin (show (‖x‖⁻¹ : ℝ) • x ∈ sphere (0 : V) 1 from by
        simpa only [mem_sphere, dist_zero_right] using hunit)
      have hb' := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖x‖)
      rw [Z.imaginaryQuadratic_smul] at hb'
      have heq : (‖x‖⁻¹ ^ 2 * Z.imaginaryQuadratic x) * ‖x‖ ^ 2 =
          Z.imaginaryQuadratic x := by field_simp
      rwa [heq] at hb'

variable [FiniteDimensional ℝ V]

def lowerBound : ℝ := Z.exists_lower_bound.choose

theorem lowerBound_pos : 0 < Z.lowerBound := Z.exists_lower_bound.choose_spec.1

theorem imaginaryQuadratic_lower_bound (x : V) :
    Z.lowerBound * ‖x‖ ^ 2 ≤ Z.imaginaryQuadratic x := Z.exists_lower_bound.choose_spec.2 x

def gaussianWeight (x : V) : ℂ := Complex.exp ((Real.pi : ℂ) * Complex.I * Z.form x x)

omit [FiniteDimensional ℝ V] in
theorem gaussianWeight_ne_zero (x : V) : Z.gaussianWeight x ≠ 0 := Complex.exp_ne_zero _

omit [FiniteDimensional ℝ V] in
theorem gaussianWeight_norm (x : V) :
    ‖Z.gaussianWeight x‖ = Real.exp (-Real.pi * Z.imaginaryQuadratic x) := by
  rw [SiegelPhase.gaussianWeight, Complex.norm_exp]
  congr 1
  simp [SiegelPhase.imaginaryQuadratic, Complex.mul_re, Complex.mul_im]

theorem gaussianWeight_norm_le (x : V) :
    ‖Z.gaussianWeight x‖ ≤ Real.exp (-(Real.pi * Z.lowerBound) * ‖x‖ ^ 2) := by
  rw [Z.gaussianWeight_norm]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (Z.imaginaryQuadratic_lower_bound x) Real.pi_pos.le
  nlinarith

end SiegelPhase

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM
