import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.Vacuum
import OAI.RepresentationTheory.Theta.Convergence
import OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier

/-! # Nonzero -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Nonzero.CM

noncomputable section

/-! The actual rational theta functional is nonzero, detected on the
standard Gaussian tensor the integral finite vacuum. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.Vacuum.CM
variable (I : Type*) [Fintype I]

theorem vacuum_real (x : I → ℝ) :
    (Constructed.Vacuum.CM.vacuum I).val x = (Real.exp (-(Real.pi * ∑ i, (x i) ^ 2)) : ℂ) := by
  rw [Constructed.Vacuum.CM.vacuum_apply, Complex.ofReal_exp]
  congr 1
  push_cast
  rfl

def test : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor (Constructed.Vacuum.CM.vacuum I) RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction

theorem term_nonneg (x : I → ℚ) : 0 ≤ ((test I).val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.diagonal x)).re := by
  change 0 ≤ ((Constructed.Vacuum.CM.vacuum I).val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.rationalReal x) * RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x)).re
  by_cases hx : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors
  · rw [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator_of_mem hx, mul_one, vacuum_real, Complex.ofReal_re]
    exact (Real.exp_pos _).le
  · rw [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator_of_notMem hx, mul_zero, Complex.zero_re]

theorem term_zero : ((test I).val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.diagonal (0 : I → ℚ))).re = 1 := by
  change ((Constructed.Vacuum.CM.vacuum I).val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.rationalReal 0) * RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal 0)).re = 1
  have hr : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.rationalReal (0 : I → ℚ) = 0 := by funext i; exact Rat.cast_zero
  have hf : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (0 : I → ℚ) = 0 := by funext i; exact map_zero _
  rw [hr, hf, Constructed.Vacuum.CM.vacuum_zero, RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator_of_mem RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors.zero_mem, one_mul, Complex.one_re]

theorem theta_pos : 0 < (RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional (test I)).re := by
  have hs := RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.adelic_rational_summable (test I)
  change 0 < (∑' x : I → ℚ, (test I).val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.diagonal x)).re
  rw [Complex.re_tsum hs]
  exact (Complex.hasSum_re hs.hasSum).summable.tsum_pos (term_nonneg I) 0 (by rw [term_zero]; exact zero_lt_one)

theorem theta_ne_zero : RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional (test I) ≠ 0 := by
  intro h
  have hp := theta_pos I
  rw [h, Complex.zero_re] at hp
  exact lt_irrefl _ hp

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Nonzero.CM
