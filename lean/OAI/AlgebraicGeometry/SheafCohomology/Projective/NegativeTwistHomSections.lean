import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomPolynomials
import OAI.AlgebraicGeometry.SheafCohomology.Projective.HomSectionEquivEvaluation

/-! # Negative Twist Hom Sections -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomSections

noncomputable section

open _root_.MvPolynomial

/-! The actual positive-twist section associated to a map between ordered negative twists. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite OAI.AlgebraicGeometry.SheafCohomology.Projective.HomSectionEquivEvaluation
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
local instance negativeTwistHomSectionMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

def coordinateNegativeTwistHomUnitMap (j : σ) (a b : ℕ) (hba : b ≤ a)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b) :
    Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)) ⟶
      TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (a - b) :=
  (TwistShiftIso.MvPolynomial.coordinateHyperplanePowerCancellationIso (R := R) j a ≪≫ TensorSections.monoidalUnitObjIso _).inv ≫
    (PairedTwistEquivalence.MvPolynomial.coordinateHyperplaneTwistPairEquivalence (R := R) j a).functor.map f ≫
    (TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE (R := R) j b a hba).hom

def coordinateNegativeTwistHomSection (j : σ) (a b : ℕ) (hba : b ≤ a)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b) :
    Γ(TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (a - b), ⊤) :=
  (coordinateNegativeTwistHomUnitMap j a b hba f).val.app (op ⊤)
    (show Γ(Proj (homogeneousSubmodule σ R), ⊤) from 1)

theorem coordinateNegativeTwistHomUnitMap_eq_tensor (j : σ) (a b : ℕ) (hba : b ≤ a)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b) :
    coordinateNegativeTwistHomUnitMap j a b hba f =
      (TwistShiftIso.MvPolynomial.coordinateHyperplanePowerCancellationIso (R := R) j a ≪≫ TensorSections.monoidalUnitObjIso _).inv ≫
        (f ⊗ₘ 𝟙 (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j a)) ≫
        (TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE (R := R) j b a hba).hom := by
  rw [tensorHom_id]
  rfl

theorem coordinateNegativeTwistHomEquivPolynomials_apply [Fintype σ] [LinearOrder σ]
    (j : σ) (a b : ℕ) (hba : b ≤ a)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b) :
    NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials (R := R) j a b hba f =
      DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j (a - b)
        (coordinateNegativeTwistHomSection (R := R) j a b hba f) := by
  unfold NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials
  simp only [Equiv.trans_apply, HomSectionEquivEvaluation.isoHomCongr_apply,
    HomSectionEquivEvaluation.unitHomTopSectionsEquiv_apply]
  change (DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j (a - b)) _ =
    (DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j (a - b)) _
  congr 1

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomSections
