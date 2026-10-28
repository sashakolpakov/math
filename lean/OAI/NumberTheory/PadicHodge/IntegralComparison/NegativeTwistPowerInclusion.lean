import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeChartCoordinates

/-! # Negative Twist Power Inclusion -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistPowerInclusion

noncomputable section

/-! The native powers of the hyperplane-ideal inclusion give the
normalized coefficient functional on the distinguished projective chart. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R] {σ : Type}

attribute [local instance] MvPolynomial.gradedAlgebra

local instance (X : Scheme.{u}) : MonoidalCategory X.Modules := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

def inclusion (j : σ) : (n : ℕ) →
    AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n ⟶
      AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R))
  | 0 => (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalUnitObjIso _).hom
  | n + 1 => (inclusion j n ⊗ₘ AlgebraicGeometry.SheafCohomology.Projective.IdealModule.idealModuleToUnit (AlgebraicGeometry.SheafCohomology.Projective.SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)) ≫
      (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.unitObjTensorIso _).hom

theorem baseGenerator_inclusion (j : σ) :
    (AlgebraicGeometry.SheafCohomology.Projective.IdealModule.idealModuleToUnit (AlgebraicGeometry.SheafCohomology.Projective.SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)).val.app (op (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j))
      (AlgebraicGeometry.SheafCohomology.Projective.FrameSections.overTrivializationSection (AlgebraicGeometry.SheafCohomology.Projective.IdealModule.idealModule (AlgebraicGeometry.SheafCohomology.Projective.SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
        (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) (AlgebraicGeometry.SheafCohomology.Projective.HyperplaneCoordinateSection.MvPolynomial.coordinateHyperplaneIdealOverTrivialization (R := R) j j) 1) =
      (1 : Γ(Proj (homogeneousSubmodule σ R), AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)) := by
  have h := AlgebraicGeometry.SheafCohomology.Projective.HyperplaneCoordinateSection.MvPolynomial.coordinateHyperplaneIdealOverTrivialization_inv_comp (R := R) j j
  rw [AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_self] at h
  have hv := congrArg (fun f => f.val.app (op (Over.mk (𝟙 (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j))))
    (1 : Γ(Proj (homogeneousSubmodule σ R), AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j))) h
  change (AlgebraicGeometry.SheafCohomology.Projective.IdealModule.idealModuleToUnit (AlgebraicGeometry.SheafCohomology.Projective.SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)).val.app (op (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j))
      (AlgebraicGeometry.SheafCohomology.Projective.FrameSections.overTrivializationSection (AlgebraicGeometry.SheafCohomology.Projective.IdealModule.idealModule (AlgebraicGeometry.SheafCohomology.Projective.SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
        (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) (AlgebraicGeometry.SheafCohomology.Projective.HyperplaneCoordinateSection.MvPolynomial.coordinateHyperplaneIdealOverTrivialization (R := R) j j) 1) =
    _ at hv
  change _ = (1 : Γ(Proj (homogeneousSubmodule σ R), AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)) *
    (Proj (homogeneousSubmodule σ R)).presheaf.map (𝟙 (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)).op
      (1 : Γ(Proj (homogeneousSubmodule σ R), AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)) at hv
  simpa only [map_one, mul_one] using hv

theorem inclusion_generator (j : σ) (n : ℕ) :
    (NegativeTwistPowerInclusion.inclusion (R := R) j n).val.app (op (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j))
      (AlgebraicGeometry.SheafCohomology.Projective.DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j n) =
      (1 : Γ(Proj (homogeneousSubmodule σ R), AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)) := by
  induction n with
  | zero =>
    exact AlgebraicGeometry.SheafCohomology.Projective.SectionIdentities.Scheme.Modules.iso_inv_hom_app_applyT
      (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalUnitObjIso (Proj (homogeneousSubmodule σ R))) (op (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j))
      (1 : Γ(Proj (homogeneousSubmodule σ R), AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j))
  | succ n ih =>
    change (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.unitObjTensorIso _).hom.val.app (op (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j))
      ((NegativeTwistPowerInclusion.inclusion j n ⊗ₘ AlgebraicGeometry.SheafCohomology.Projective.IdealModule.idealModuleToUnit (AlgebraicGeometry.SheafCohomology.Projective.SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)).val.app
        (op (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j))
        (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.tensorSection _ _ (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
          (AlgebraicGeometry.SheafCohomology.Projective.DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j n)
          (AlgebraicGeometry.SheafCohomology.Projective.FrameSections.overTrivializationSection (AlgebraicGeometry.SheafCohomology.Projective.IdealModule.idealModule (AlgebraicGeometry.SheafCohomology.Projective.SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
            (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) (AlgebraicGeometry.SheafCohomology.Projective.HyperplaneCoordinateSection.MvPolynomial.coordinateHyperplaneIdealOverTrivialization (R := R) j j) 1))) = _
    rw [AlgebraicGeometry.SheafCohomology.Projective.TensorFrameSections.tensorSection_map]
    rw [ih, baseGenerator_inclusion, AlgebraicGeometry.SheafCohomology.Projective.TensorFrameSections.unitObjTensorIso_hom_tensorSection, mul_one]

theorem inclusion_eq_coefficient (j : σ) (n : ℕ)
    (x : Γ(AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n, AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)) :
    (NegativeTwistPowerInclusion.inclusion (R := R) j n).val.app (op (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)) x =
      AlgebraicGeometry.SheafCohomology.Projective.NegativeChartCoordinates.MvPolynomial.coordinateHyperplaneNegativeChartCoefficient j n x := by
  conv_lhs => rw [AlgebraicGeometry.SheafCohomology.Projective.NegativeChartCoordinates.MvPolynomial.coordinateHyperplaneIdealChartPowerSection_generates j n x]
  rw [map_smul, inclusion_generator]
  change (AlgebraicGeometry.SheafCohomology.Projective.NegativeChartCoordinates.MvPolynomial.coordinateHyperplaneNegativeChartCoefficient j n x :
    Γ(Proj (homogeneousSubmodule σ R), AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)) * 1 = _
  exact mul_one _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistPowerInclusion
