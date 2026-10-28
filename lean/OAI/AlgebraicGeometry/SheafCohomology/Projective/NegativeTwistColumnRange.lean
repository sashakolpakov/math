import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistMapCoefficients
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenModuleTower
import OAI.AlgebraicGeometry.SheafCohomology.Projective.HomogeneousGeneratorImage

/-! # Negative Twist Column Range -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistColumnRange.Dimension

noncomputable section

/-! The image of each normalized projective presentation column is its filtered local-generator module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory _root_.MvPolynomial

open OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenModuleTower.Construction

universe u

local instance negativeTwistColumnRangeMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem negativeTwistPolynomialColumn_normalized_range
    (hfield : IsField Γ(Spec (.of R), ⊤))
    {N : (Proj (homogeneousSubmodule σ R)).Modules} (j : σ) (a n : ℕ) (ha : a ≤ n)
    (q : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⟶ N) :
    letI := hfield.toField
    let π := MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    let U := MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j
    letI := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra π U
    letI := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenModuleTower.Construction.baseOpenModuleOverSections π N U
    letI := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenModuleTower.Construction.baseOpenModuleScalarTower π N U
    ((ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.tensorSectionGlobalCoefficientLinear π N (UnitSection.Dimension.projectiveTwistUnitSection j n) U).comp
      (NegativeTwistMapCoefficients.Dimension.negativeTwistPolynomialColumn j a n ha q)).range =
    FilteredModuleFg.Dimension.polynomialFilteredModule
      (fun i => ChartScalars.Dimension.projectiveChartPolynomialAlgHom (R := R) j (MvPolynomial.X i))
      (Submodule.span Γ(Spec (.of R), ⊤)
        {show (ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsFunctor π U).obj N from
          q.app U (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j a)}) (n - a) := by
  let := hfield.toField
  let π := MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let U := MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j
  let := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra π U
  let := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenModuleTower.Construction.baseOpenModuleOverSections π N U
  let := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenModuleTower.Construction.baseOpenModuleScalarTower π N U
  let φ := ChartScalars.Dimension.projectiveChartPolynomialAlgHom (R := R) j
  let v := fun i => φ (MvPolynomial.X i)
  let w : (ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsFunctor π U).obj N :=
    q.app U (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j a)
  let f := (ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.tensorSectionGlobalCoefficientLinear π N (UnitSection.Dimension.projectiveTwistUnitSection j n) U).comp
    (NegativeTwistMapCoefficients.Dimension.negativeTwistPolynomialColumn j a n ha q)
  have hv : v j = 1 := ChartPolynomialMap.Dimension.projectiveChartPolynomialMap_anchor j
  apply HomogeneousGeneratorImage.Dimension.homogeneous_generator_range v j hv (n - a) w f
  intro p
  have h := NegativeTwistMapCoefficients.Dimension.negativeTwistPolynomialColumn_coefficient (R := R) j a n ha q p
  have he := AlgHom.congr_fun (MvPolynomial.aeval_unique φ) p.val
  exact h.trans (congrArg (fun r => r • w) he)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistColumnRange.Dimension
