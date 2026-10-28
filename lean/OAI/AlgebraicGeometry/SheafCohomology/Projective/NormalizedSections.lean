import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialSectionMap
import OAI.AlgebraicGeometry.SheafCohomology.Projective.UnitSection
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnitCoefficient
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialQuotient
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ChartScalars

/-! # Normalized Sections -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.NormalizedSections

noncomputable section

/-! Actual homogeneous polynomial sections, normalized on a closed subscheme's affine chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory _root_.MvPolynomial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Dimension

open OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnitCoefficient.Construction

universe u

local instance projectiveNormalizedSectionsMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := Monoidal.Scheme.Modules.monoidalCategory X

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem closedProjectiveAmbientPolynomialSectionsMap_coefficient {X : Scheme.{u}}
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) (j : σ) (n : ℕ)
    (p : homogeneousSubmodule σ Γ(Spec (.of R), ⊤) n) :
    ArithmeticGeometry.OrdinaryLocus.Openness.TensorSectionRestriction.Construction.tensorSectionGlobalCoefficient ((Scheme.Modules.pushforward f).obj (Invertible.Scheme.Modules.unitObj X))
      (UnitSection.Dimension.projectiveTwistUnitSection (R := R) j n) (MvPolynomialClosure.MvPolynomial.coordinateOpen j)
      (PolynomialSectionMapDefs.Dimension.closedProjectiveAmbientPolynomialSectionsMap f j n p) =
    ChartScalars.Dimension.closedProjectiveChartPolynomialAlgHom f j p.val := by
  let P := TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n
  let x : Γ(P, ⊤) := (DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j n).symm p
  let s := (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv P).symm (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j n)
  have : IsIso ((Scheme.Modules.pullback (MvPolynomialClosure.MvPolynomial.coordinateOpen j).ι).map
      ((TensorSections.monoidalUnitObjIso _).hom ≫ s)) := UnitSection.Dimension.projectiveTwistUnitSection_chart_isIso j n
  have hs : FrameSections.overTrivializationCoefficient P (MvPolynomialClosure.MvPolynomial.coordinateOpen j)
      (PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSheafPowerOverFrame j j n) (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv P s) = 1 := by
    rw [Equiv.apply_symm_apply]
    exact PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSectionPower_coefficient_self j n
  change ArithmeticGeometry.OrdinaryLocus.Openness.TensorSectionRestriction.Construction.tensorSectionGlobalCoefficient _ (UnitSection.Dimension.projectiveTwistUnitSection j n) (MvPolynomialClosure.MvPolynomial.coordinateOpen j)
    ((PolynomialSectionMapDefs.Dimension.nativeUnitToPushforward f ⊗ₘ 𝟙 P).app ⊤ ((λ_ P).inv.app ⊤ x)) = _
  rw [ArithmeticGeometry.OrdinaryLocus.Openness.TensorSectionRestriction.Construction.tensorSectionGlobalCoefficient_naturality]
  have hc := ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnitCoefficient.Construction.tensorSectionGlobalCoefficient_unit_frame s (MvPolynomialClosure.MvPolynomial.coordinateOpen j)
    (PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSheafPowerOverFrame j j n) hs x
  change f.app (MvPolynomialClosure.MvPolynomial.coordinateOpen j) ((TensorSections.monoidalUnitObjIso _).hom.app (MvPolynomialClosure.MvPolynomial.coordinateOpen j)
    (ArithmeticGeometry.OrdinaryLocus.Openness.TensorSectionRestriction.Construction.tensorSectionGlobalCoefficient (𝟙_ _) ((TensorSections.monoidalUnitObjIso _).hom ≫ s)
      (MvPolynomialClosure.MvPolynomial.coordinateOpen j) ((λ_ P).inv.app ⊤ x))) = _
  rw [hc]
  exact congrArg (f.app (MvPolynomialClosure.MvPolynomial.coordinateOpen j)) (ChartPolynomialMap.Dimension.projectiveChartPolynomialMap_section_symm j n p).symm

end Dimension

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.NormalizedSections
