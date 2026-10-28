import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.NegativeTwistMapCoefficients
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenModuleTower
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.HomogeneousGeneratorImage

/-! # Negative Twist Column Range -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.NegativeTwistColumnRange.Construction

noncomputable section

/-! The image of each normalized projective presentation column is its filtered local-generator module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory _root_.MvPolynomial

universe u

local instance negativeTwistColumnRangeMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem negativeTwistPolynomialColumn_normalized_range
    (hfield : IsField Γ(Spec (.of R), ⊤))
    {N : (Proj (homogeneousSubmodule σ R)).Modules} (j : σ) (a n : ℕ) (ha : a ≤ n)
    (q : AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⟶ N) :
    letI := hfield.toField
    let π := AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    let U := AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j
    letI := BaseOpenSections.Construction.baseOpenSectionsAlgebra π U
    letI := BaseOpenModuleTower.Construction.baseOpenModuleOverSections π N U
    letI := BaseOpenModuleTower.Construction.baseOpenModuleScalarTower π N U
    ((BaseOpenSections.Construction.tensorSectionGlobalCoefficientLinear π N (ProjectiveNormalizedSections.Construction.projectiveTwistUnitSection j n) U).comp
      (NegativeTwistMapCoefficients.Construction.negativeTwistPolynomialColumn j a n ha q)).range =
    FilteredModuleFg.Construction.polynomialFilteredModule
      (fun i => ProjectiveChartScalars.Construction.projectiveChartPolynomialAlgHom (R := R) j (MvPolynomial.X i))
      (Submodule.span Γ(Spec (.of R), ⊤)
        {show (BaseOpenSections.Construction.baseOpenSectionsFunctor π U).obj N from
          q.app U (AlgebraicGeometry.SheafCohomology.Projective.DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j a)}) (n - a) := by
  let := hfield.toField
  let π := AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let U := AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j
  let := BaseOpenSections.Construction.baseOpenSectionsAlgebra π U
  let := BaseOpenModuleTower.Construction.baseOpenModuleOverSections π N U
  let := BaseOpenModuleTower.Construction.baseOpenModuleScalarTower π N U
  let φ := ProjectiveChartScalars.Construction.projectiveChartPolynomialAlgHom (R := R) j
  let v := fun i => φ (MvPolynomial.X i)
  let w : (BaseOpenSections.Construction.baseOpenSectionsFunctor π U).obj N :=
    q.app U (AlgebraicGeometry.SheafCohomology.Projective.DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j a)
  let f := (BaseOpenSections.Construction.tensorSectionGlobalCoefficientLinear π N (ProjectiveNormalizedSections.Construction.projectiveTwistUnitSection j n) U).comp
    (NegativeTwistMapCoefficients.Construction.negativeTwistPolynomialColumn j a n ha q)
  have hv : v j = 1 := ProjectiveChartPolynomialMap.Construction.projectiveChartPolynomialMap_anchor j
  apply HomogeneousGeneratorImage.Construction.homogeneous_generator_range v j hv (n - a) w f
  intro p
  have h := NegativeTwistMapCoefficients.Construction.negativeTwistPolynomialColumn_coefficient (R := R) j a n ha q p
  have he := AlgHom.congr_fun (MvPolynomial.aeval_unique φ) p.val
  exact h.trans (congrArg (fun r => r • w) he)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.NegativeTwistColumnRange.Construction
