import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.BilinearRational
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerTopTrace

/-! # Cup Scalar Extension -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CupScalarExtension.CM.Construction

noncomputable section

/-! The actual rational top cup pairing has the required complex
scalar extension under the canonical Betti coefficient map. -/

open scoped TensorProduct

theorem rationalH1TopCup_scalarExtension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ)
    (u v : WeightOne.CM.Complexification (V.rationalCohomology 1)) :
    CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) (2 + (k + k))
      (LinearMap.BilinMap.baseChange ℂ (TopCup.CM.Construction.rationalH1TopCup V k) u v) =
    TopCup.CM.Construction.complexH1TopCup V k
      (CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1 u)
      (CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1 v) := by
  apply (BilinearRational.CM.Construction.bilinearScalarExtension_comparison (TopCup.CM.Construction.rationalH1TopCup V k) (TopCup.CM.Construction.complexH1TopCup V k)
    (CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1)
    (CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) (2 + (k + k))) ?_ u v).symm
  intro x y
  simp only [CohomologyBaseChange.CM.singularCohomologyComplexification_tmul, one_smul]
  exact (TopCup.CM.Construction.rationalH1TopCup_comparison V k x y).symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CupScalarExtension.CM.Construction
