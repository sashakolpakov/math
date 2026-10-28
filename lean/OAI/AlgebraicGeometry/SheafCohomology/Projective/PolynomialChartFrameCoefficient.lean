import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartCoordinates
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PositivePowerChartGenerator

/-! # Polynomial Chart Frame Coefficient -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartFrameCoefficient

noncomputable section

open _root_.MvPolynomial

/-! Polynomial dehomogenization in terms of the canonical chart-frame coefficient. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite OAI.AlgebraicGeometry.SheafCohomology.Projective.PositivePowerChartGenerator
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

def coordinateChartCoefficientRingHom {m : ℕ} (a : Fin (m + 1) → ULift.{u} σ) :
    Γ(Proj (homogeneousSubmodule σ R), MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) (a 0).down) →+*
      AddMonoidAlgebra Γ(Spec (CommRingCat.of R), ⊤)
        (LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid (StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => (a k).down))) :=
  (StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := R) a).toRingHom.comp
    ((Proj (homogeneousSubmodule σ R)).presheaf.map
      (homOfLE (StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) a 0)).op).hom

theorem coordinateTwistBaseCechFactor_globalCoefficient {m : ℕ}
    (a : Fin (m + 1) → ULift.{u} σ) (j : σ) (n : ℕ)
    (x : Γ(TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n, ⊤)) :
    (TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := R) a j (n : ℤ)).hom
      ((TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n).presheaf.map
        (homOfLE (le_top : StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a ≤ ⊤)).op x) =
    (Proj (homogeneousSubmodule σ R)).presheaf.map
      (homOfLE (StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) a 0)).op
      (FrameSections.overTrivializationCoefficient (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
        (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) (a 0).down)
        (PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSheafPowerOverFrame (R := R) (a 0).down j n) x) := by
  change FrameSections.overTrivializationCoefficient (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
    (StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a)
    (Invertible.Scheme.Modules.overTrivializationOfRestrictIso _ _
      (OpenFrames.Scheme.Modules.restrictOpenTrivialization (StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) a 0)
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivialization (R := R) (a 0).down j n))) x = _
  rw [OpenFrames.Scheme.Modules.overTrivializationOfRestrictOpenTrivialization]
  exact FrameSections.overTrivializationCoefficient_restrict _ _ _ x

theorem coordinateTwistPolynomial_chartCoefficient [Fintype σ] [LinearOrder σ]
    (j : σ) (n : ℕ) (x : Γ(TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n, ⊤))
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) 0) :
    PolynomialChartMap.MvPolynomial.polynomialChartRingHom Γ(Spec (CommRingCat.of R), ⊤) (fun k => (a.val k).down)
      (DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j n x).val =
    StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentLinearEquiv (R := R) a.val
      ((Proj (homogeneousSubmodule σ R)).presheaf.map
        (homOfLE (StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) a.val 0)).op
        (FrameSections.overTrivializationCoefficient (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
          (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) (a.val 0).down)
          (PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSheafPowerOverFrame (R := R) (a.val 0).down j n) x)) := by
  rw [← PolynomialChartCoordinates.MvPolynomial.coordinateTwistGlobalSections_polynomial_chart,
    coordinateTwistBaseCechFactor_globalCoefficient]

theorem coordinateTwistPolynomial_chartCoefficientRingHom [Fintype σ] [LinearOrder σ]
    (j : σ) (n : ℕ) (x : Γ(TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n, ⊤))
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) 0) :
    PolynomialChartMap.MvPolynomial.polynomialChartRingHom Γ(Spec (CommRingCat.of R), ⊤) (fun k => (a.val k).down)
      (DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j n x).val =
    coordinateChartCoefficientRingHom (R := R) a.val
      (FrameSections.overTrivializationCoefficient (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
        (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) (a.val 0).down)
        (PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSheafPowerOverFrame (R := R) (a.val 0).down j n) x) :=
  coordinateTwistPolynomial_chartCoefficient j n x a

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartFrameCoefficient
