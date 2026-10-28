import OAI.AlgebraicGeometry.SheafCohomology.Projective.PowerFrameSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OpenFrames
import OAI.AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates

/-! # Positive Power Chart Generator -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PositivePowerChartGenerator

noncomputable section

open _root_.MvPolynomial

/-! The canonical positive-power section is a generator on its distinguished chart. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u
section

theorem overCoefficient_eq_localCoefficient {X : Scheme.{u}}
    (M : X.Modules) (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ Invertible.Scheme.Modules.unitObj U.1.toScheme)
    (x : Γ(M, ⊤)) :
    FrameSections.overTrivializationCoefficient M U.1
      (Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U.1 e) x =
        FrameSections.localTrivializationCoefficient M U e x := by
  rw [FrameSectionComparison.overTrivializationCoefficient_eq_local_of_overIso,
    OpenFrames.restrictTrivializationOfOverTrivializationOfRestrictIso]

theorem restrict_eq_coefficient_smul_generator {X : Scheme.{u}}
    (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (s x : Γ(M, ⊤)) (hs : FrameSections.overTrivializationCoefficient M U e s = 1) :
    M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op x =
      FrameSections.overTrivializationCoefficient M U e x •
        M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s := by
  let q := RankOneMapCoordinates.overFrameSectionEquiv M U e
  apply q.symm.injective
  change FrameSections.overTrivializationCoefficient M U e x =
    q.symm (FrameSections.overTrivializationCoefficient M U e x •
      M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s)
  rw [q.symm.map_smul]
  change FrameSections.overTrivializationCoefficient M U e x =
    FrameSections.overTrivializationCoefficient M U e x * FrameSections.overTrivializationCoefficient M U e s
  rw [hs, mul_one]

end

namespace MvPolynomial
open OAI.AlgebraicGeometry.SheafCohomology.Projective.PositivePowerChartGenerator
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

def coordinateHyperplanePoleSheafPowerOverFrame (i j : σ) (n : ℕ) :
    (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n).over (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) ≅
      SheafOfModules.unit ((Proj (homogeneousSubmodule σ R)).ringCatSheaf.over
        (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)) :=
  Invertible.Scheme.Modules.overTrivializationOfRestrictIso
    (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n) (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivialization (R := R) i j n)

theorem coordinateHyperplanePoleSectionPower_coefficient_self (j : σ) (n : ℕ) :
    FrameSections.overTrivializationCoefficient (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
      (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) (coordinateHyperplanePoleSheafPowerOverFrame (R := R) j j n)
      (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j n) = 1 := by
  rw [coordinateHyperplanePoleSheafPowerOverFrame,
    overCoefficient_eq_localCoefficient _ ⟨_, MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen j⟩]
  unfold FrameSections.localTrivializationCoefficient
  rw [PowerFrameSections.MvPolynomial.coordinateHyperplanePoleSectionPower_localTrivializationTopSection,
    CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_self]
  simp only [FrameSections.affineOpenTopSection, map_one, one_pow, FrameSections.affineOpenAmbientSection]

theorem coordinateHyperplanePoleSectionPower_generates_chart (j : σ) (n : ℕ)
    (x : Γ(TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n, ⊤)) :
    (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n).presheaf.map
        (homOfLE (le_top : MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j ≤ ⊤)).op x =
      FrameSections.overTrivializationCoefficient (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
        (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) (coordinateHyperplanePoleSheafPowerOverFrame (R := R) j j n) x •
      (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n).presheaf.map
        (homOfLE le_top).op (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j n) :=
  restrict_eq_coefficient_smul_generator _ _ _ _ x
    (coordinateHyperplanePoleSectionPower_coefficient_self j n)

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PositivePowerChartGenerator
