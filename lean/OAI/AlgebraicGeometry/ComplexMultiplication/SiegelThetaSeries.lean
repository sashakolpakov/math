import OAI.AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase
import OAI.AlgebraicGeometry.ComplexMultiplication.LatticeGaussian
import Mathlib.Analysis.Calculus.SmoothSeries

/-! # Siegel Theta Series -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication

noncomputable section

section

/-!
# Actual theta terms and their first derivatives

The summand is `exp (π i B(x,x) + 2π i P(x)(z))` for real position `x`,
a positive complex quadratic phase `B`, and a real-linear pairing `P`
with the complex Jacobi variable `z`. Uniform Gaussian bounds on bounded
sets control both the summands and their actual complex derivatives.
-/

open Filter _root_.Topology _root_.Metric

variable {V U : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup U] [NormedSpace ℂ U]
  (Z : CMSiegelPhase.CM.SiegelPhase V) (P : V →L[ℝ] (U →L[ℂ] ℂ))

def CMSiegelPhase.CM.SiegelPhase.thetaTerm (x : V) (z : U) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * Z.form x x +
    (2 * (Real.pi : ℂ) * Complex.I) * P x z)

theorem CMSiegelPhase.CM.SiegelPhase.thetaTerm_zero (x : V) : Z.thetaTerm P x 0 = Z.gaussianWeight x := by
  simp only [CMSiegelPhase.CM.SiegelPhase.thetaTerm, map_zero, mul_zero, add_zero, CMSiegelPhase.CM.SiegelPhase.gaussianWeight]

theorem CMSiegelPhase.CM.SiegelPhase.thetaTerm_norm (x : V) (z : U) :
    ‖Z.thetaTerm P x z‖ =
      Real.exp (-Real.pi * Z.imaginaryQuadratic x - 2 * Real.pi * (P x z).im) := by
  rw [CMSiegelPhase.CM.SiegelPhase.thetaTerm, Complex.norm_exp]
  congr 1
  simp [CMSiegelPhase.CM.SiegelPhase.imaginaryQuadratic, Complex.add_re, Complex.mul_re, Complex.mul_im]
  ring

def CMSiegelPhase.CM.SiegelPhase.thetaTermDerivative (x : V) (z : U) : U →L[ℂ] ℂ :=
  Z.thetaTerm P x z • ((2 * (Real.pi : ℂ) * Complex.I) • P x)

theorem CMSiegelPhase.CM.SiegelPhase.thetaTerm_hasFDerivAt (x : V) (z : U) :
    HasFDerivAt (Z.thetaTerm P x) (Z.thetaTermDerivative P x z) z := by
  have h := ((P x).hasFDerivAt (x := z)).const_smul (2 * (Real.pi : ℂ) * Complex.I)
  exact (h.const_add ((Real.pi : ℂ) * Complex.I * Z.form x x)).cexp

theorem CMSiegelPhase.CM.SiegelPhase.pairing_norm_le (x : V) (z : U) : ‖P x z‖ ≤ ‖P‖ * ‖x‖ * ‖z‖ :=
  ((P x).le_opNorm z).trans (mul_le_mul_of_nonneg_right (P.le_opNorm x) (norm_nonneg z))

variable [FiniteDimensional ℝ V]

def CMSiegelPhase.CM.SiegelPhase.thetaMajorant (R : ℝ) (x : V) : ℝ :=
  Real.exp (-(Real.pi * Z.lowerBound) * ‖x‖ ^ 2 + (2 * Real.pi * ‖P‖ * R) * ‖x‖)

theorem CMSiegelPhase.CM.SiegelPhase.thetaTerm_norm_le (R : ℝ) (x : V) (z : U) (hz : ‖z‖ ≤ R) :
    ‖Z.thetaTerm P x z‖ ≤ Z.thetaMajorant P R x := by
  rw [Z.thetaTerm_norm]
  apply Real.exp_le_exp.mpr
  have hlin : -(P x z).im ≤ ‖P‖ * ‖x‖ * R :=
    (neg_le_abs _).trans ((Complex.abs_im_le_norm _).trans
      ((CMSiegelPhase.CM.SiegelPhase.pairing_norm_le P x z).trans
        (mul_le_mul_of_nonneg_left hz (mul_nonneg (norm_nonneg P) (norm_nonneg x)))))
  have hq := mul_le_mul_of_nonneg_left (Z.imaginaryQuadratic_lower_bound x) Real.pi_pos.le
  have hl := mul_le_mul_of_nonneg_left hlin (show 0 ≤ 2 * Real.pi by positivity)
  change -Real.pi * Z.imaginaryQuadratic x - 2 * Real.pi * (P x z).im ≤
    -(Real.pi * Z.lowerBound) * ‖x‖ ^ 2 + (2 * Real.pi * ‖P‖ * R) * ‖x‖
  nlinarith

theorem CMSiegelPhase.CM.SiegelPhase.thetaMajorant_summable (L : Submodule ℤ V) [DiscreteTopology L] (R : ℝ) :
    Summable (fun x : L => Z.thetaMajorant P R x) :=
  LatticeGaussian.CM.lattice_gaussian_summable L (Real.pi * Z.lowerBound) (2 * Real.pi * ‖P‖ * R)
    (mul_pos Real.pi_pos Z.lowerBound_pos)

theorem CMSiegelPhase.CM.SiegelPhase.thetaTerm_norm_summable (L : Submodule ℤ V) [DiscreteTopology L] (z : U) :
    Summable (fun x : L => ‖Z.thetaTerm P x z‖) :=
  (Z.thetaMajorant_summable P L ‖z‖).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun x => Z.thetaTerm_norm_le P ‖z‖ x z le_rfl)

def CMSiegelPhase.CM.SiegelPhase.thetaDerivativeMajorant (R : ℝ) (x : V) : ℝ :=
  (2 * Real.pi * ‖P‖) * (‖x‖ * Z.thetaMajorant P R x)

theorem CMSiegelPhase.CM.SiegelPhase.thetaDerivativeMajorant_summable (L : Submodule ℤ V) [DiscreteTopology L] (R : ℝ) :
    Summable (fun x : L => Z.thetaDerivativeMajorant P R x) := by
  simpa only [CMSiegelPhase.CM.SiegelPhase.thetaDerivativeMajorant, CMSiegelPhase.CM.SiegelPhase.thetaMajorant, pow_one] using!
    (LatticeGaussian.CM.lattice_gaussian_poly_summable L (Real.pi * Z.lowerBound) (2 * Real.pi * ‖P‖ * R)
      (mul_pos Real.pi_pos Z.lowerBound_pos) 1).mul_left (2 * Real.pi * ‖P‖)

theorem CMSiegelPhase.CM.SiegelPhase.thetaTermDerivative_norm_le (R : ℝ) (x : V) (z : U) (hz : ‖z‖ ≤ R) :
    ‖Z.thetaTermDerivative P x z‖ ≤ Z.thetaDerivativeMajorant P R x := by
  have hc : ‖2 * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by simp
  rw [CMSiegelPhase.CM.SiegelPhase.thetaTermDerivative, norm_smul, norm_smul, hc]
  calc
    ‖Z.thetaTerm P x z‖ * (2 * Real.pi * ‖P x‖) ≤
        Z.thetaMajorant P R x * (2 * Real.pi * (‖P‖ * ‖x‖)) := by
      gcongr
      · exact (Real.exp_pos _).le
      · exact Z.thetaTerm_norm_le P R x z hz
      · exact P.le_opNorm x
    _ = Z.thetaDerivativeMajorant P R x := by unfold CMSiegelPhase.CM.SiegelPhase.thetaDerivativeMajorant; ring

end

/-!
# Convergent theta series with support in a lattice subset

The series and its derivative are actual sums of the explicit exponential
terms. In particular this includes the positive-degree sparse cosets
used as finite-input supports in the manuscript's nonvanishing argument.
The present theorem concerns the complex Jacobi variable at a fixed phase.
-/

open scoped Classical
open Filter _root_.Topology _root_.Metric

variable {V U : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup U] [NormedSpace ℂ U]
  (Z : CMSiegelPhase.CM.SiegelPhase V) (P : V →L[ℝ] (U →L[ℂ] ℂ))
  (L : Submodule ℤ V) (S : Set L)

def CMSiegelPhase.CM.SiegelPhase.thetaTermOn (x : L) (z : U) : ℂ := if x ∈ S then Z.thetaTerm P x z else 0

def CMSiegelPhase.CM.SiegelPhase.thetaTermOnDerivative (x : L) (z : U) : U →L[ℂ] ℂ :=
  if x ∈ S then Z.thetaTermDerivative P x z else 0

theorem CMSiegelPhase.CM.SiegelPhase.thetaTermOn_hasFDerivAt (x : L) (z : U) :
    HasFDerivAt (Z.thetaTermOn P L S x) (Z.thetaTermOnDerivative P L S x z) z := by
  by_cases hx : x ∈ S
  · have heq : Z.thetaTermOn P L S x = Z.thetaTerm P x := by
      funext w
      simp only [CMSiegelPhase.CM.SiegelPhase.thetaTermOn, ite_eq_left hx]
    rw [heq, CMSiegelPhase.CM.SiegelPhase.thetaTermOnDerivative, ite_eq_left hx]
    exact Z.thetaTerm_hasFDerivAt P x z
  · have heq : Z.thetaTermOn P L S x = fun _ => 0 := by
      funext w
      simp only [CMSiegelPhase.CM.SiegelPhase.thetaTermOn, ite_eq_right hx]
    rw [heq, CMSiegelPhase.CM.SiegelPhase.thetaTermOnDerivative, ite_eq_right hx]
    exact hasFDerivAt_const (0 : ℂ) z

def CMSiegelPhase.CM.SiegelPhase.thetaSeriesOn (z : U) : ℂ := ∑' x : L, Z.thetaTermOn P L S x z

def CMSiegelPhase.CM.SiegelPhase.thetaSeriesOnDerivative (z : U) : U →L[ℂ] ℂ :=
  ∑' x : L, Z.thetaTermOnDerivative P L S x z

variable [FiniteDimensional ℝ V] [DiscreteTopology L]

theorem CMSiegelPhase.CM.SiegelPhase.thetaTermOn_norm_summable (z : U) :
    Summable (fun x : L => ‖Z.thetaTermOn P L S x z‖) := by
  apply (Z.thetaTerm_norm_summable P L z).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro x
  unfold CMSiegelPhase.CM.SiegelPhase.thetaTermOn
  split_ifs <;> simp

omit [DiscreteTopology L] in
theorem CMSiegelPhase.CM.SiegelPhase.thetaTermOnDerivative_norm_le (R : ℝ) (x : L) (z : U) (hz : ‖z‖ ≤ R) :
    ‖Z.thetaTermOnDerivative P L S x z‖ ≤ Z.thetaDerivativeMajorant P R x := by
  unfold CMSiegelPhase.CM.SiegelPhase.thetaTermOnDerivative
  split_ifs
  · exact Z.thetaTermDerivative_norm_le P R x z hz
  · rw [norm_zero]
    unfold CMSiegelPhase.CM.SiegelPhase.thetaDerivativeMajorant CMSiegelPhase.CM.SiegelPhase.thetaMajorant
    positivity

/-- Differentiation under the actual theta sum, justified by a summable
uniform derivative bound on a neighborhood of every Jacobi variable. -/
theorem CMSiegelPhase.CM.SiegelPhase.thetaSeriesOn_hasFDerivAt (z : U) :
    HasFDerivAt (Z.thetaSeriesOn P L S) (Z.thetaSeriesOnDerivative P L S z) z := by
  let R : ℝ := ‖z‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hz : z ∈ ball (0 : U) R := by
    simp only [mem_ball, dist_zero_right]
    dsimp [R]
    linarith
  exact hasFDerivAt_tsum_of_isPreconnected
    (Z.thetaDerivativeMajorant_summable P L R) isOpen_ball
    (convex_ball (0 : U) R).isPreconnected
    (fun x w _ => Z.thetaTermOn_hasFDerivAt P L S x w)
    (fun x w hw => Z.thetaTermOnDerivative_norm_le P L S R x w
      (show ‖w‖ < R by simpa only [mem_ball, dist_zero_right] using hw).le)
    (mem_ball_self hR) (Z.thetaTermOn_norm_summable P L S 0).of_norm hz

theorem CMSiegelPhase.CM.SiegelPhase.thetaSeriesOn_differentiable : Differentiable ℂ (Z.thetaSeriesOn P L S) :=
  fun z => (Z.thetaSeriesOn_hasFDerivAt P L S z).differentiableAt

/-- The formal derivative is identified with the actual `fderiv`. -/
theorem CMSiegelPhase.CM.SiegelPhase.fderiv_thetaSeriesOn (z : U) :
    fderiv ℂ (Z.thetaSeriesOn P L S) z = Z.thetaSeriesOnDerivative P L S z :=
  (Z.thetaSeriesOn_hasFDerivAt P L S z).fderiv

end

end OAI.AlgebraicGeometry.ComplexMultiplication
