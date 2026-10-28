import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartFrameCoefficient
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartInjective

/-! # Polynomial Section Product Criterion -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialSectionProductCriterion

noncomputable section

open _root_.MvPolynomial

/-! Multiplication of chart coefficients determines multiplication of the corresponding polynomials. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

def coordinateTwistChartCoefficient (i j : σ) (n : ℕ)
    (x : Γ(TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n, ⊤)) :
    Γ(Proj (homogeneousSubmodule σ R), MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) :=
  FrameSections.overTrivializationCoefficient (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
    (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSheafPowerOverFrame (R := R) i j n) x

theorem coordinateTwistPolynomial_eq_mul_of_coefficient (i j : σ) (m n : ℕ)
    (x : Γ(TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m, ⊤))
    (y : Γ(TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n, ⊤))
    (z : Γ(TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (m + n), ⊤))
    (h : coordinateTwistChartCoefficient i j (m + n) z =
      coordinateTwistChartCoefficient i j m x * coordinateTwistChartCoefficient i j n y) :
    (DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j (m + n) z).val =
      (DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j m x).val *
        (DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j n y).val := by
  let a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) 0 :=
    ⟨fun _ => ⟨i⟩, Subsingleton.strictMono (α := Fin 1) _⟩
  let px := DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j m x
  let py := DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j n y
  let pz := DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j (m + n) z
  let p : homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) (m + n) :=
    ⟨px.val * py.val, px.property.mul py.property⟩
  have hp : pz = p := by
    apply PolynomialChartInjective.MvPolynomial.polynomialChartRingHom_injective_homogeneous
      Γ(Spec (CommRingCat.of R), ⊤) (fun k => (a.val k).down) (m + n)
    change PolynomialChartMap.MvPolynomial.polynomialChartRingHom Γ(Spec (CommRingCat.of R), ⊤) (fun k => (a.val k).down) pz.val =
      PolynomialChartMap.MvPolynomial.polynomialChartRingHom Γ(Spec (CommRingCat.of R), ⊤) (fun k => (a.val k).down) (px.val * py.val)
    rw [map_mul]
    have hx := PolynomialChartFrameCoefficient.MvPolynomial.coordinateTwistPolynomial_chartCoefficientRingHom j m x a
    have hy := PolynomialChartFrameCoefficient.MvPolynomial.coordinateTwistPolynomial_chartCoefficientRingHom j n y a
    have hz := PolynomialChartFrameCoefficient.MvPolynomial.coordinateTwistPolynomial_chartCoefficientRingHom j (m + n) z a
    change PolynomialChartMap.MvPolynomial.polynomialChartRingHom Γ(Spec (CommRingCat.of R), ⊤) (fun k => (a.val k).down) px.val =
      PolynomialChartFrameCoefficient.MvPolynomial.coordinateChartCoefficientRingHom (R := R) a.val
      (coordinateTwistChartCoefficient i j m x) at hx
    change PolynomialChartMap.MvPolynomial.polynomialChartRingHom Γ(Spec (CommRingCat.of R), ⊤) (fun k => (a.val k).down) py.val =
      PolynomialChartFrameCoefficient.MvPolynomial.coordinateChartCoefficientRingHom (R := R) a.val
      (coordinateTwistChartCoefficient i j n y) at hy
    change PolynomialChartMap.MvPolynomial.polynomialChartRingHom Γ(Spec (CommRingCat.of R), ⊤) (fun k => (a.val k).down) pz.val =
      PolynomialChartFrameCoefficient.MvPolynomial.coordinateChartCoefficientRingHom (R := R) a.val
      (coordinateTwistChartCoefficient i j (m + n) z) at hz
    rw [hx, hy, hz, h, map_mul]
  exact congrArg Subtype.val hp

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialSectionProductCriterion
