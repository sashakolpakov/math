import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.TopCup
import OAI.AlgebraicTopology.Products.CupGradedCommutativity

/-! # Top Alternating -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.TopAlternating.CM.Construction

noncomputable section

/-! Rational linear functionals on the actual top cup product give
alternating forms on genuine rational H¹. -/

open OAI.AlgebraicTopology.Products.CupGradedCommutativity

theorem rationalH1_cup_skew (X : TopCat.{0})
    (a b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X 1) :
    AlgebraicTopology.Products.CupCohomology.singularCohomologyCup X 1 1 a b = -AlgebraicTopology.Products.CupCohomology.singularCohomologyCup X 1 1 b a := by
  simpa only [Nat.mul_one, pow_one, AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast, LinearMap.id_apply, neg_one_smul] using
    AlgebraicTopology.Products.CupGradedCommutativity.singularCohomologyCup_graded_comm X a b

theorem rationalH1_cup_self (X : TopCat.{0})
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X 1) :
    AlgebraicTopology.Products.CupCohomology.singularCohomologyCup X 1 1 a a = 0 := by
  let t := AlgebraicTopology.Products.CupCohomology.singularCohomologyCup X 1 1 a a
  have ht : t = -t := rationalH1_cup_skew X a a
  have hsum : t + t = 0 := by
    conv_lhs => lhs; rw [ht]
    exact neg_add_cancel t
  have hz : (2 : ℚ) • t = 0 := by rw [two_smul]; exact hsum
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

theorem rationalH1TopCup_self (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ)
    (a : V.rationalCohomology 1) : TopCup.CM.Construction.rationalH1TopCup V k a a = 0 := by
  change (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace V.toOver) 2 (k + k)).flip
    (Powers.CM.Construction.fubiniStudyPowerQ V k) (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace V.toOver) 1 1 a a) = 0
  rw [rationalH1_cup_self, map_zero]

def rationalH1TopForm (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ)
    (trace : V.rationalCohomology (2 + (k + k)) →ₗ[ℚ] ℚ) :
    LinearMap.BilinForm ℚ (V.rationalCohomology 1) :=
  (TopCup.CM.Construction.rationalH1TopCup V k).compr₂ trace

theorem rationalH1TopForm_alternating (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ)
    (trace : V.rationalCohomology (2 + (k + k)) →ₗ[ℚ] ℚ) :
    (rationalH1TopForm V k trace).IsAlt := by
  intro a
  change trace (TopCup.CM.Construction.rationalH1TopCup V k a a) = 0
  rw [rationalH1TopCup_self, map_zero]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.TopAlternating.CM.Construction
