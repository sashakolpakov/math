import OAI.AlgebraicGeometry.SheafCohomology.Projective.PowerFrameScalar

/-! # Twist Frame Scalar -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistFrameScalar.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-! Scalar changes of a local generator in every positive and negative power. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
local instance twistFrameScalarMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

theorem coordinateHyperplanePoleSheafPowerTrivializationOf_scalar
    (U : (Proj (homogeneousSubmodule σ R)).Opens) (j : σ)
    (e g : (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j).restrict U.ι ≅
      Invertible.Scheme.Modules.unitObj U.toScheme)
    (r : Γ(U.toScheme, ⊤))
    (h : e.hom = g.hom ≫ UnitScalar.unitEndomorphismOfTopSection r)
    (n : ℕ) :
    (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivializationOf U j e n).hom =
      (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivializationOf U j g n).hom ≫
        UnitScalar.unitEndomorphismOfTopSection (r ^ n) :=
  PowerFrameScalar.recursiveTensorTrivialization_hom_eq_comp_scalar U
    (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivializationOf U j)
    (fun m => TensorSections.restrictMonoidalTensorIso U.ι
      (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m)
      (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j))
    (fun _ _ => rfl) (fun _ _ => rfl) e g r h n

theorem coordinateHyperplaneIdealModulePowerTrivializationOf_scalar
    (U : (Proj (homogeneousSubmodule σ R)).Opens) (j : σ)
    (e g : (IdealModule.idealModule
      (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)).restrict U.ι ≅
      Invertible.Scheme.Modules.unitObj U.toScheme)
    (r : Γ(U.toScheme, ⊤))
    (h : e.hom = g.hom ≫ UnitScalar.unitEndomorphismOfTopSection r)
    (n : ℕ) :
    (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivializationOf U j e n).hom =
      (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivializationOf U j g n).hom ≫
        UnitScalar.unitEndomorphismOfTopSection (r ^ n) :=
  PowerFrameScalar.recursiveTensorTrivialization_hom_eq_comp_scalar U
    (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivializationOf U j)
    (fun m => TensorSections.restrictMonoidalTensorIso U.ι
      (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j m)
      (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)))
    (fun _ _ => rfl) (fun _ _ => rfl) e g r h n

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistFrameScalar.MvPolynomial
