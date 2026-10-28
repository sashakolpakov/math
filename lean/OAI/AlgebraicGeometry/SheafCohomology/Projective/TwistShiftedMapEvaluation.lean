import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistShiftedMapSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorFunctorSectionEvaluation
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleCompositionEvaluation

/-! # Twist Shifted Map Evaluation -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistShiftedMapEvaluation

noncomputable section

open _root_.MvPolynomial

/-! Composition and evaluation of the concrete projective shifted map. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
local instance shiftedMapEvaluationMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

theorem coordinateNegativeTwistShiftedMap_comp (j : σ) (a b N : ℕ)
    (ha : a ≤ N) (hb : b ≤ N)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b) :
    (TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE (R := R) j a N ha).hom ≫
      TwistShiftedMapSections.MvPolynomial.coordinateNegativeTwistShiftedMap (R := R) j a b N ha hb f =
      (f ⊗ₘ 𝟙 (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j N)) ≫
        (TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE (R := R) j b N hb).hom := by
  simp only [TwistShiftedMapSections.MvPolynomial.coordinateNegativeTwistShiftedMap, TensorConjugatedMapSections.tensorConjugatedMap, Iso.hom_inv_id_assoc]

theorem coordinateNegativeTwistShiftedMap_apply_hom (j : σ) (a b N : ℕ)
    (ha : a ≤ N) (hb : b ≤ N)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b)
    (U : (Proj (homogeneousSubmodule σ R)).Opens)
    (x : Γ(TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⊗
      TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j N, U)) :
    (TwistShiftedMapSections.MvPolynomial.coordinateNegativeTwistShiftedMap (R := R) j a b N ha hb f).val.app (op U)
      ((TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE (R := R) j a N ha).hom.val.app
        (op U) x) =
      (TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE (R := R) j b N hb).hom.val.app
        (op U) ((f ⊗ₘ 𝟙 (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j N)).val.app (op U) x) := by
  exact ModuleCompositionEvaluation.module_comp_eq_apply
    (X := Proj (homogeneousSubmodule σ R))
    (TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE (R := R) j a N ha).hom
    (TwistShiftedMapSections.MvPolynomial.coordinateNegativeTwistShiftedMap (R := R) j a b N ha hb f)
    (f ⊗ₘ 𝟙 (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j N))
    (TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE (R := R) j b N hb).hom
    (coordinateNegativeTwistShiftedMap_comp (R := R) j a b N ha hb f) U x

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistShiftedMapEvaluation
