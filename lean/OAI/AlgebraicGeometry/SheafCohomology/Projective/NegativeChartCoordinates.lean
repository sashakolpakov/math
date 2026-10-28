import OAI.AlgebraicGeometry.SheafCohomology.Projective.DistinguishedChartCancellation
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FramedTensorMap
import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistMaps

/-! # Negative Chart Coordinates -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeChartCoordinates

noncomputable section

open _root_.MvPolynomial

/-! Coordinates of local negative-twist sections supplied by the normalized power pairing. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite OAI.AlgebraicGeometry.SheafCohomology.Projective.FramedTensorMap
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
local instance negativeChartCoordinatesMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

def coordinateHyperplaneNegativeChartCoefficient (j : σ) (n : ℕ)
    (x : Γ(TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n, MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)) :
    Γ(Proj (homogeneousSubmodule σ R), MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) :=
  (PowerCancellationPairing.MvPolynomial.coordinateHyperplanePowerPairing (R := R) j n).val.app (op (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j))
    (TensorSections.tensorSection _ _ (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) x
      ((TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n).presheaf.map
        (homOfLE le_top).op (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j n)))

theorem coordinateHyperplaneNegativeChartCoefficient_smul (j : σ) (n : ℕ)
    (r : Γ(Proj (homogeneousSubmodule σ R), MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j))
    (x : Γ(TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n, MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)) :
    coordinateHyperplaneNegativeChartCoefficient j n (r • x) =
      r * coordinateHyperplaneNegativeChartCoefficient j n x := by
  unfold coordinateHyperplaneNegativeChartCoefficient
  rw [TensorSectionBilinear.tensorSection_smul_left, map_smul]
  rfl

theorem coordinateHyperplaneNegativeChartCoefficient_generator (j : σ) (n : ℕ) :
    coordinateHyperplaneNegativeChartCoefficient j n
      (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j n) = 1 :=
  DistinguishedChartCancellation.MvPolynomial.coordinateHyperplanePowerPairing_chart_one j n

theorem coordinateHyperplaneIdealChartPowerSection_generates (j : σ) (n : ℕ)
    (x : Γ(TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n, MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)) :
    x = coordinateHyperplaneNegativeChartCoefficient j n x •
      DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j n :=
  FramedTensorMap.rankOne_eq_smul_of_normalized_functional
    (RankOneMapCoordinates.overFrameSectionEquiv (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n)
      (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame (R := R) j j n))
    (coordinateHyperplaneNegativeChartCoefficient j n)
    (coordinateHyperplaneNegativeChartCoefficient_smul j n)
    (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j n)
    (coordinateHyperplaneNegativeChartCoefficient_generator j n) x

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeChartCoordinates
