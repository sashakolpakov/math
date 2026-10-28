import OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistFrameNormalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.MapRestriction
import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomChart
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ChartPolynomialMap

/-! # Negative Twist Chart Action -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistChartAction

noncomputable section

/-! The actual negative-twist sheaf map is polynomial multiplication in
the standard frame on the distinguished chart and all its subopens. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.MvPolynomial

open OAI.AlgebraicGeometry.SheafCohomology.Projective.ChartPolynomialMap.Dimension OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistFrameNormalization

universe u

variable {R : Type u} [CommRing R] {σ : Type}

attribute [local instance] MvPolynomial.gradedAlgebra

theorem generator_eq_frame (j : σ) (n : ℕ) :
    AlgebraicGeometry.SheafCohomology.Projective.DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j n =
      (AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates.overFrameSectionEquiv (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n)
        (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) (AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame (R := R) j j n)) 1 := by
  apply (AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates.overFrameSectionEquiv (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n)
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) (AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame (R := R) j j n)).symm.injective
  rw [LinearEquiv.symm_apply_apply, ← NegativeTwistFrameNormalization.coefficient_eq_frame,
    AlgebraicGeometry.SheafCohomology.Projective.NegativeChartCoordinates.MvPolynomial.coordinateHyperplaneNegativeChartCoefficient_generator]

theorem mapCoefficient_eq_chart (j : σ) (a b : ℕ)
    (f : AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⟶
      AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b) :
    AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates.overFrameMapCoefficient (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
      (AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame (R := R) j j a)
      (AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame (R := R) j j b) f =
    AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomChart.MvPolynomial.coordinateNegativeTwistMapChartCoefficient j a b f := by
  change (AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates.overFrameSectionEquiv (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b)
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) (AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame (R := R) j j b)).symm
      (f.val.app (op (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j))
        ((AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates.overFrameSectionEquiv (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a)
          (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) (AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame (R := R) j j a)) 1)) = _
  rw [← generator_eq_frame, ← NegativeTwistFrameNormalization.coefficient_eq_frame]
  rfl

variable [Fintype σ] [LinearOrder σ]

theorem mapCoefficient_eq_polynomial (j : σ) (a b : ℕ) (hba : b ≤ a)
    (f : AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⟶
      AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b) :
    AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates.overFrameMapCoefficient (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
      (AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame (R := R) j j a)
      (AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame (R := R) j j b) f =
    AlgebraicGeometry.SheafCohomology.Projective.ChartPolynomialMap.Dimension.projectiveChartPolynomialMap (R := R) j
      (AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials (R := R) j a b hba f).val := by
  rw [mapCoefficient_eq_chart, ← AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomChart.MvPolynomial.coordinateNegativeTwistHomSection_chartCoefficient j a b hba f,
    AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomSections.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials_apply]
  exact (AlgebraicGeometry.SheafCohomology.Projective.ChartPolynomialMap.Dimension.projectiveChartPolynomialMap_section j (a - b)
    (AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomSections.MvPolynomial.coordinateNegativeTwistHomSection (R := R) j a b hba f)).symm

theorem map_on_subopen (j : σ) (a b : ℕ) (hba : b ≤ a)
    (f : AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⟶
      AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b)
    (V : (Proj (homogeneousSubmodule σ R)).Opens) (hV : V ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
    (x : Γ(AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a, V)) :
    (AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates.overFrameSectionEquiv (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b) V
      (AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization _ _ _
        (AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame (R := R) j j b)
        (Over.mk (homOfLE hV)))).symm (f.app V x) =
    (Proj (homogeneousSubmodule σ R)).presheaf.map (homOfLE hV).op
        (AlgebraicGeometry.SheafCohomology.Projective.ChartPolynomialMap.Dimension.projectiveChartPolynomialMap (R := R) j
          (AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials (R := R) j a b hba f).val) *
      (AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates.overFrameSectionEquiv (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a) V
        (AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization _ _ _
          (AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame (R := R) j j a)
          (Over.mk (homOfLE hV)))).symm x := by
  have h := Frame.MapRestriction.coordinate_on_subopen (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
    (AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame (R := R) j j a)
    (AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame (R := R) j j b) f hV x
  rw [mapCoefficient_eq_polynomial j a b hba f] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistChartAction
