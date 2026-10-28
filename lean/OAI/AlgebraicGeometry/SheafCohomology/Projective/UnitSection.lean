import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnitCoefficient
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialQuotient
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ChartScalars

/-! # Unit Section -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.UnitSection

noncomputable section

/-! Actual homogeneous polynomial sections, normalized on a closed subscheme's affine chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory _root_.MvPolynomial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Dimension

open OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnitCoefficient.Construction

universe u

local instance projectiveUnitSectionMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := Monoidal.Scheme.Modules.monoidalCategory X

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

def projectiveTwistUnitSection (j : σ) (n : ℕ) :
    𝟙_ (Proj (homogeneousSubmodule σ R)).Modules ⟶ TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n :=
  (TensorSections.monoidalUnitObjIso _).hom ≫ (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv _).symm (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower j n)

instance projectiveTwistUnitSection_chart_isIso (j : σ) (n : ℕ) :
    IsIso ((Scheme.Modules.pullback (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j).ι).map
      (projectiveTwistUnitSection (R := R) j n)) := by
  let s : Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)) ⟶
      TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n :=
    (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv _).symm (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j n)
  have hs : FrameSections.overTrivializationCoefficient (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
      (MvPolynomialClosure.MvPolynomial.coordinateOpen j) (PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSheafPowerOverFrame j j n)
      (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv _ s) = 1 := by
    rw [Equiv.apply_symm_apply]
    exact PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSectionPower_coefficient_self j n
  have : IsIso ((Scheme.Modules.pullback (MvPolynomialClosure.MvPolynomial.coordinateOpen j).ι).map s) :=
    ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnitCoefficient.Construction.sectionHom_pullback_isIso_of_overCoefficient_one s (MvPolynomialClosure.MvPolynomial.coordinateOpen j)
    (PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSheafPowerOverFrame j j n) hs
  change IsIso ((Scheme.Modules.pullback (MvPolynomialClosure.MvPolynomial.coordinateOpen j).ι).map ((TensorSections.monoidalUnitObjIso _).hom ≫ s))
  rw [Functor.map_comp]
  infer_instance

end Dimension

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.UnitSection
