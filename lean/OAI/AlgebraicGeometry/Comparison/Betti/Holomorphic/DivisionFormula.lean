import OAI.AlgebraicGeometry.Comparison.Betti.PolynomialDivisionKernel
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt

/-! # Division Formula -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DivisionFormula.Weierstrass

noncomputable section

/-! Exact holomorphic division by a polynomial with no boundary zeros.
The quotient and the strictly bounded remainder are actual contour integrals. -/

open Set Filter _root_.Metric _root_.Complex _root_.Polynomial
open scoped _root_.Topology BigOperators

open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder

def divisionQuotient (P : Polynomial ℂ) (g : ℂ → ℂ) (c : ℂ) (R : ℝ) (w : ℂ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ * ∮ z in C(c, R), g z / (P.eval z * (z - w))

theorem remainderPolynomial_coeff_zero (P : Polynomial ℂ) (g : ℂ → ℂ) (c : ℂ) (R : ℝ)
    (k : ℕ) (hk : P.natDegree ≤ k) :
    (ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.remainderPolynomial P.natDegree P g c R).coeff k = 0 := by
  rw [ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.remainderPolynomial_coeff]
  split_ifs
  · have he : (fun z => g z / P.eval z * ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.kernelCoeff P.natDegree P z k) = 0 := by
      funext z
      rw [ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.kernelCoeff_eq P rfl, PolynomialDivisionKernel.Weierstrass.division_kernel_coeff_zero P z k hk, mul_zero]
      rfl
    unfold ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.remainderCoeff
    rw [he]
    simp [circleIntegral]
  · rfl

theorem continuous_division_kernel (P : Polynomial ℂ) (w : ℂ) :
    Continuous (fun z => (P /ₘ (X - C z)).eval w) := by
  have he : (fun z => (P /ₘ (X - C z)).eval w) =
      fun z => ∑ k ∈ Finset.range (P.natDegree + 1), ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.kernelCoeff P.natDegree P z k * w ^ k := by
    funext z
    exact ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.kernel_eval_eq P rfl z w
  rw [he]
  exact continuous_finsetSum _ (fun k _ => (ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.continuous_kernelCoeff P.natDegree P k).mul_const _)

theorem remainderPolynomial_eval_integral (P : Polynomial ℂ) (g : ℂ → ℂ)
    (c : ℂ) (R : ℝ) (w : ℂ) (hR : 0 ≤ R) (hg : ContinuousOn g (sphere c R))
    (hP : ∀ z ∈ sphere c R, P.eval z ≠ 0) :
    (ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.remainderPolynomial P.natDegree P g c R).eval w =
      (2 * Real.pi * I : ℂ)⁻¹ * ∮ z in C(c, R), g z / P.eval z * (P /ₘ (X - C z)).eval w := by
  have hc (k : ℕ) : CircleIntegrable
      (fun z => g z / P.eval z * ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.kernelCoeff P.natDegree P z k * w ^ k) c R :=
    (((hg.div P.continuous.continuousOn hP).mul
      (ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.continuous_kernelCoeff P.natDegree P k).continuousOn).mul_const _).circleIntegrable hR
  calc
    _ = ∑ k ∈ Finset.range (P.natDegree + 1), ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.remainderCoeff P.natDegree P g c R k * w ^ k := by
      simp only [ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.remainderPolynomial, eval_finsetSum, eval_monomial]
    _ = (2 * Real.pi * I : ℂ)⁻¹ * ∑ k ∈ Finset.range (P.natDegree + 1),
        (∮ z in C(c, R), g z / P.eval z * ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.kernelCoeff P.natDegree P z k * w ^ k) := by
      simp only [ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.remainderCoeff, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      have h := circleIntegral.integral_smul_const
        (fun z => g z / P.eval z * ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.kernelCoeff P.natDegree P z k) (w ^ k) c R
      simp only [smul_eq_mul] at h
      rw [h, mul_assoc]
    _ = (2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(c, R),
        ∑ k ∈ Finset.range (P.natDegree + 1), g z / P.eval z * ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.kernelCoeff P.natDegree P z k * w ^ k) := by
      rw [circleIntegral.integral_fun_sum (fun k _ => hc k)]
    _ = _ := by
      congr 1
      apply circleIntegral.integral_congr hR
      intro z _
      dsimp only
      rw [ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.kernel_eval_eq P rfl]
      simp only [Finset.mul_sum, mul_assoc]

theorem holomorphic_division_formula (P : Polynomial ℂ) (g : ℂ → ℂ)
    (c : ℂ) (R : ℝ) (w : ℂ) (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (closedBall c R))
    (hP : ∀ z ∈ sphere c R, P.eval z ≠ 0) (hw : w ∈ ball c R) :
    g w = (ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.remainderPolynomial P.natDegree P g c R).eval w + P.eval w * divisionQuotient P g c R w := by
  have hzw (z : ℂ) (hz : z ∈ sphere c R) : z - w ≠ 0 := by
    intro h
    have h' := sub_eq_zero.mp h
    exact (ne_of_lt (mem_ball.mp hw)) (h' ▸ mem_sphere.mp hz)
  have hgc : ContinuousOn g (sphere c R) := hg.continuousOn.mono sphere_subset_closedBall
  have hA : CircleIntegrable (fun z => g z / P.eval z * (P /ₘ (X - C z)).eval w) c R :=
    ((hgc.div P.continuous.continuousOn hP).mul (continuous_division_kernel P w).continuousOn).circleIntegrable hR.le
  have hQ : CircleIntegrable (fun z => g z / (P.eval z * (z - w))) c R :=
    (hgc.div (P.continuous.continuousOn.mul (continuous_id.sub continuous_const).continuousOn)
      (fun z hz => mul_ne_zero (hP z hz) (hzw z hz))).circleIntegrable hR.le
  have hC := hg.circleIntegral_sub_inv_smul hw
  simp only [smul_eq_mul] at hC
  rw [remainderPolynomial_eval_integral P g c R w hR.le hgc hP]
  unfold divisionQuotient
  have hi : (∮ z in C(c, R), g z / P.eval z * (P /ₘ (X - C z)).eval w) +
      P.eval w * (∮ z in C(c, R), g z / (P.eval z * (z - w))) =
        ∮ z in C(c, R), (z - w)⁻¹ * g z := by
    have hB : CircleIntegrable (fun z => P.eval w * (g z / (P.eval z * (z - w)))) c R := by
      simpa only [smul_eq_mul] using hQ.const_fun_smul (a := P.eval w)
    rw [← circleIntegral.integral_const_mul, ← circleIntegral.integral_add hA hB]
    apply circleIntegral.integral_congr hR.le
    intro z hz
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using
      PolynomialDivisionKernel.Weierstrass.polynomial_division_kernel_fraction P (g z) z w (hP z hz) (hzw z hz)
  calc
    g w = (2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(c, R), (z - w)⁻¹ * g z) := by
      rw [hC, ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]
    _ = _ := by rw [← hi]; ring

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DivisionFormula.Weierstrass
