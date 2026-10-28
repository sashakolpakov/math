import OAI.ArithmeticGeometry.Descent.CMVariety.ExponentialScaling
import OAI.ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative

/-! # Chart Exponential Powers -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.ChartExponentialPowers

noncomputable section

open scoped _root_.Manifold ContDiff

theorem chartExponential_inv_nat_smul_pow
    {L V G : Type} [NormedAddCommGroup L] [NormedSpace ℝ L] [CompleteSpace L]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace G] [ChartedSpace L G] [CommGroup G]
    [LieGroup (𝓘(ℝ, L)) ∞ G] [T2Space G]
    (c : OpenPartialHomeomorph G V) (n : ℕ) (hn : 0 < n) (v : V) :
    ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L) c ((n : ℝ)⁻¹ • v) ^ n = ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L) c v := by
  change HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.exp (E := L) (G := G) (ArithmeticGeometry.Descent.CMVariety.ExponentialChartODE.Abelian.chartVelocity (E := L) c ((n : ℝ)⁻¹ • v)) ^ n =
    HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.exp (E := L) (G := G) (ArithmeticGeometry.Descent.CMVariety.ExponentialChartODE.Abelian.chartVelocity (E := L) c v)
  rw [← ArithmeticGeometry.Descent.CMVariety.ExponentialScaling.Abelian.exp_nat_smul, ArithmeticGeometry.Descent.CMVariety.ExponentialScaling.Abelian.chartVelocity_smul, smul_smul,
    mul_inv_cancel₀ (show (n : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hn)), one_smul]

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.ChartExponentialPowers
