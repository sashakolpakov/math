import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.ProjectivePairing
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.CycleResolution

/-! # Cycle Push Pairing -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.CyclePushPairing.CM.Abelian

noncomputable section

/-! Evaluate a properly pushed class by pulling back the test class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem projectivePairing_cohomologyPushforward {R X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : R.toOver ⟶ X.toOver) (hf : IsProper f.left) (p q n : ℕ)
    (hdeg : p + X.complexDimension = q + R.complexDimension)
    (hp : p ≤ R.complexDimension)
    (hR : (p + p) + n = 2 * R.complexDimension)
    (hX : (q + q) + n = 2 * X.complexDimension)
    (a : R.rationalCohomology (p + p)) (b : X.complexCohomology n) :
    ProjectivePairing.CM.Abelian.projectiveComplexPairing X (q + q) n hX
      (X.rationalCohomologyInclusion (q + q) (Cycles.Functoriality.UnitCap.cohomologyPushforward f hf p q hdeg a)) b =
      ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology (TopCat.of R.analyticSpace) n
        (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback f n b)
        ((R.poincareDuality (p + p) n hR).hom a) := by
  have hn : n = 2 * (R.complexDimension - p) := by omega
  subst n
  rw [ProjectivePairing.CM.Abelian.projectiveComplexPairing_rational_cap,
    Cycles.Functoriality.UnitCap.cohomologyPushforward_eq_poincare f hf p q hdeg hp]
  change ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology (TopCat.of X.analyticSpace) _ b
      ((X.poincareDuality (q + q) _ hX).toLinearEquiv
        ((X.poincareDuality (q + q) _ hX).toLinearEquiv.symm
          (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) _
            ((R.poincareDuality (p + p) _ hR).hom a)))) = _
  exact (congrArg (ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology (TopCat.of X.analyticSpace) _ b)
    ((X.poincareDuality (q + q) _ hX).toLinearEquiv.apply_symm_apply _)).trans
      (ComplexPairing.CM.Abelian.evaluateComplexOnRationalHomology_naturality
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) _ b _).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.CyclePushPairing.CM.Abelian
