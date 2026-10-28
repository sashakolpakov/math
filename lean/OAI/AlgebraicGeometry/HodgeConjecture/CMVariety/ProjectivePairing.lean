import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.ComplexPairing
import OAI.AlgebraicTopology.Duality.Pairing
import OAI.AlgebraicTopology.Duality.Poincare.Manifold
import OAI.AlgebraicTopology.Kunneth.ProjectiveFinitenessLe

/-! # Projective Pairing -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.ProjectivePairing.CM.Abelian

noncomputable section

/-! The cup pairing on the actual projective variety is nondegenerate and equals canonical cap evaluation. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Duality.Poincare.Manifold

def projectiveFundamentalInDegree (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k l : ℕ)
    (h : k + l = 2 * X.complexDimension) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of X.analyticSpace)).homology (k + l) :=
  AlgebraicTopology.Duality.Poincare.CompactMeaning.complexFundamentalClassInDegree X.complexDimension (M := X.analyticSpace) (k + l) h

def projectiveComplexPairing (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k l : ℕ)
    (h : k + l = 2 * X.complexDimension) :
    X.complexCohomology k →ₗ[ℂ] X.complexCohomology l →ₗ[ℂ] ℂ :=
  ComplexPairing.CM.Abelian.complexCupPairing (TopCat.of X.analyticSpace) k l
    (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) (TopCat.of X.analyticSpace) (k + l)
      (projectiveFundamentalInDegree X k l h))

theorem projectiveRationalPairing_injective (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k l : ℕ)
    (h : k + l = 2 * X.complexDimension) :
    Function.Injective (ComplexPairing.CM.Abelian.rationalCupPairing (TopCat.of X.analyticSpace) k l
      (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) (TopCat.of X.analyticSpace) (k + l)
        (projectiveFundamentalInDegree X k l h))) := by
  apply (LinearMap.ker_eq_bot).mp
  apply eq_bot_iff.mpr
  intro a ha
  change a = 0
  apply AlgebraicTopology.Duality.Pairing.Constructions.Poincare.fundamentalPairing_left_of_cap_injective
    (TopCat.of X.analyticSpace) k l (projectiveFundamentalInDegree X k l h)
    (X.poincareDuality k l h).toLinearEquiv.injective a
  intro b
  exact LinearMap.congr_fun ha b

theorem projectiveComplexPairing_left_nondegenerate (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k l : ℕ)
    (h : k + l = 2 * X.complexDimension) (a : X.complexCohomology k)
    (ha : ∀ b, projectiveComplexPairing X k l h a b = 0) : a = 0 := by
  let : Module.Finite ℚ (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of X.analyticSpace) k) :=
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.integralProjective_cohomology_finite X k
  let : Module.Finite ℚ (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of X.analyticSpace) l) :=
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.integralProjective_cohomology_finite X l
  exact ComplexPairing.CM.Abelian.complexCupPairing_left_nondegenerate (TopCat.of X.analyticSpace) k l _
    (projectiveRationalPairing_injective X k l h) a ha

theorem projectiveComplexPairing_rational_cap (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k l : ℕ)
    (h : k + l = 2 * X.complexDimension) (a : X.rationalCohomology k)
    (b : X.complexCohomology l) :
    projectiveComplexPairing X k l h (X.rationalCohomologyInclusion k a) b =
      ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology (TopCat.of X.analyticSpace) l b
        ((X.poincareDuality k l h).hom a) := by
  let : Module.Finite ℚ (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of X.analyticSpace) l) :=
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.integralProjective_cohomology_finite X l
  exact ComplexPairing.CM.Abelian.complexCupPairing_rational_cap (TopCat.of X.analyticSpace) k l
    (projectiveFundamentalInDegree X k l h) a b

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.ProjectivePairing.CM.Abelian
