import OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductCoordinates
import OAI.AlgebraicGeometry.SheafCohomology.Projective.WeightedFreeDegreeComponents
import OAI.AlgebraicGeometry.SheafCohomology.Projective.DegreeZeroPolynomials
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistShiftIso
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PositiveTwistEquivalence

/-! # Twisted Coproduct Polynomial Sections -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedCoproductPolynomialSections

noncomputable section

open _root_.MvPolynomial

/-! Actual sections of sufficiently twisted negative-twist sums are weighted polynomial pieces. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra
local instance polynomialCoproductBiproducts (X : Scheme.{u}) :
    HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts

def negativeTwistCoproductTensorIso (j : σ) {r : ℕ} (d : Fin r → ℕ)
    (n : ℕ) (hd : ∀ i, d i ≤ n) :
    (PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.obj
      (∐ fun i => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d i)) ≅
      (∐ fun i => TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (n - d i)) :=
  PreservesCoproduct.iso
    (PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor _ ≪≫
      Sigma.mapIso (fun i =>
        TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE (R := R) j (d i) n (hd i))

def negativeTwistPolynomialSectionEquiv (j : σ) (a N : ℕ) (ha : a ≤ N) :
    (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
      ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j N).functor.obj
        (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a)) ≃ₗ[
          Γ(Spec (CommRingCat.of R), ⊤)]
      homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) (N - a) :=
  (((AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).mapIso
    (TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE (R := R) j a N ha)).toLinearEquiv).trans
      (DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j (N - a))

theorem negativeTwistPolynomialSectionEquiv_apply (j : σ) (a N : ℕ) (ha : a ≤ N)
    (x : (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
      ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j N).functor.obj
        (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a))) :
    negativeTwistPolynomialSectionEquiv j a N ha x =
      DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j (N - a)
        ((TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE (R := R) j a N ha).hom.val.app
          (op ⊤) x) := by
  unfold negativeTwistPolynomialSectionEquiv
  simp only [LinearEquiv.trans_apply]
  congr 1

def negativeTwistCoproductPolynomialSectionsIso (j : σ) {r : ℕ} (d : Fin r → ℕ)
    (n : ℕ) (hd : ∀ i, d i ≤ n) :
    (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
      ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.obj
        (∐ fun i => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d i))) ≅
      ModuleCat.of Γ(Spec (CommRingCat.of R), ⊤)
        (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading (σ := σ) Γ(Spec (CommRingCat.of R), ⊤)
          (fun i => (d i : ℤ)) (n : ℤ)) := by
  let G := AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
  let F := (PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor
  letI : F.Additive := Functor.additive_of_preserves_binary_products F
  letI : (F ⋙ G).Additive := by
    dsimp only [G]
    infer_instance
  let M := fun i : Fin r => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d i)
  let V := fun i : Fin r => ModuleCat.of Γ(Spec (CommRingCat.of R), ⊤)
    (homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) (n - d i))
  exact ((AdditiveCoproductCoordinates.additiveCoproductCoordinates (F ⋙ G) M V
    (fun i => negativeTwistPolynomialSectionEquiv j (d i) n (hd i))).trans
      (WeightedFreeDegreeComponents.weightedFreeDegreeComponentsEquiv d n hd).symm).toModuleIso

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedCoproductPolynomialSections
