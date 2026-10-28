import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DivisionFormula

/-! # Division Quotient Unit -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.DivisionQuotientUnit.Weierstrass

noncomputable section

/-! If a fiber already factors by a holomorphic unit, the actual contour
quotient recovers that unit at every interior point, including multiple roots. -/

open Set Filter _root_.Metric _root_.Complex _root_.Polynomial
open scoped _root_.Topology

theorem divisionQuotient_eq_of_boundary (P : Polynomial ℂ) (g u : ℂ → ℂ)
    (c : ℂ) (R : ℝ) (w : ℂ) (hR : 0 ≤ R)
    (hu : DifferentiableOn ℂ u (closedBall c R))
    (hP : ∀ z ∈ sphere c R, P.eval z ≠ 0)
    (hg : ∀ z ∈ sphere c R, g z = P.eval z * u z) (hw : w ∈ ball c R) :
    Holomorphic.DivisionFormula.Weierstrass.divisionQuotient P g c R w = u w := by
  have he : (∮ z in C(c, R), g z / (P.eval z * (z - w))) =
      ∮ z in C(c, R), (z - w)⁻¹ * u z := by
    apply circleIntegral.integral_congr hR
    intro z hz
    dsimp only
    rw [hg z hz, mul_div_mul_left _ _ (hP z hz), div_eq_mul_inv, mul_comm]
  unfold Holomorphic.DivisionFormula.Weierstrass.divisionQuotient
  rw [he]
  have hC := hu.circleIntegral_sub_inv_smul hw
  simp only [smul_eq_mul] at hC
  rw [hC, ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]

end

end OAI.AlgebraicGeometry.Comparison.Betti.DivisionQuotientUnit.Weierstrass
