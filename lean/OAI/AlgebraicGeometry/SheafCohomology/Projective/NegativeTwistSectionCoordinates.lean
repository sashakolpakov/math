import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistShiftedMap
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedCoproductPolynomialSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistShiftedMapEvaluation

/-! # Negative Twist Section Coordinates -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistSectionCoordinates

noncomputable section

open _root_.MvPolynomial

/-! Polynomial coordinates on the sections of an individually twisted negative summand. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra
local instance negativeSectionCoordinatesMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

theorem negativeTwistPolynomialSectionEquiv_map (j : σ) (a b N : ℕ)
    (hba : b ≤ a) (ha : a ≤ N) (hb : b ≤ N)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b)
    (x : (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
      ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j N).functor.obj
        (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a))) :
    (TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistPolynomialSectionEquiv j b N hb
      ((AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).map
        ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j N).functor.map f) x)).val =
      (NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials (R := R) j a b hba f).val *
        (TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistPolynomialSectionEquiv j a N ha x).val := by
  let e := TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE (R := R) j a N ha
  let d := TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE (R := R) j b N hb
  have h := NegativeTwistShiftedMap.MvPolynomial.coordinateNegativeTwistShiftedMap_polynomial (R := R) j a b N hba ha hb f
    (e.hom.val.app (op ⊤) x)
  have ht := TwistShiftedMapEvaluation.MvPolynomial.coordinateNegativeTwistShiftedMap_apply_hom (R := R) j a b N ha hb f ⊤ x
  have ht' := congrArg (fun y : Γ(TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (N - b), ⊤) =>
    (DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j (N - b) y).val) ht
  set_option backward.dsimp.proofs true in
    dsimp +instances only [e, d, Scheme.Opens,
      SheafedSpace.instTopologicalSpaceCarrierCarrier] at h ht'
  have h' := ht'.symm.trans h
  have hf : (PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j N).functor.map f =
      f ⊗ₘ 𝟙 (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j N) :=
    TensorFunctorSectionEvaluation.invertibleRightTensorEquivalence_map_tensor
      (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j N)
      (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower_isInvertible (R := R) j N) f
  rw [TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistPolynomialSectionEquiv_apply (R := R) j b N hb,
    TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistPolynomialSectionEquiv_apply (R := R) j a N ha]
  rw [TensorFunctorSectionEvaluation.baseGlobalSectionsFunctor_map_apply, hf]
  set_option backward.dsimp.proofs true in
    dsimp +instances only [e, d, Scheme.Opens, SheafedSpace.instTopologicalSpaceCarrierCarrier,
      TwistShiftedMapEvaluation.MvPolynomial.shiftedMapEvaluationMonoidal, negativeSectionCoordinatesMonoidal,
      PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence,
      InvertibleTensorEquivalence.invertibleRightTensorEquivalence, CategoryTheory.Equivalence.changeFunctor,
      MonoidalCategory.tensorRight, MonoidalCategory.curriedTensor, Functor.flip] at h' ⊢
  convert h' using 1

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistSectionCoordinates
