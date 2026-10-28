import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.NegativeTwistCoefficients
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections

/-! # Negative Twist Map Coefficients -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.NegativeTwistMapCoefficients.Construction

noncomputable section

/-! Each column of a negative-twist presentation acts by its actual local generator. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory _root_.MvPolynomial

universe u

local instance negativeTwistMapCoefficientsMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem negativeTwist_map_tensorSectionGlobalCoefficient
    {N : (Proj (homogeneousSubmodule σ R)).Modules} (j : σ) (a n : ℕ) (ha : a ≤ n)
    (q : AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⟶ N)
    (x : Γ(AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⊗
      AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n, ⊤)) :
    TensorSectionRestriction.Construction.tensorSectionGlobalCoefficient N (ProjectiveNormalizedSections.Construction.projectiveTwistUnitSection j n) (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
      ((q ⊗ₘ 𝟙 (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n)).app ⊤ x) =
    ProjectiveChartPolynomialMap.Construction.projectiveChartPolynomialMap j (AlgebraicGeometry.SheafCohomology.Projective.TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistPolynomialSectionEquiv j a n ha x).val •
      q.app (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j) (AlgebraicGeometry.SheafCohomology.Projective.DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j a) := by
  have hn := TensorSectionRestriction.Construction.tensorSectionGlobalCoefficient_naturality q (ProjectiveNormalizedSections.Construction.projectiveTwistUnitSection j n)
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j) x
  have hc := NegativeTwistCoefficients.Construction.negativeTwist_tensorSectionGlobalCoefficient (R := R) j a n ha x
  exact hn.trans ((congrArg (q.app (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)) hc).trans (q.app_smul _ _))

def negativeTwistPolynomialColumn {N : (Proj (homogeneousSubmodule σ R)).Modules}
    (j : σ) (a n : ℕ) (ha : a ≤ n) (q : AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⟶ N) :
    homogeneousSubmodule σ Γ(Spec (.of R), ⊤) (n - a) →ₗ[Γ(Spec (.of R), ⊤)]
      (AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
        (N ⊗ AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n) :=
  (((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ).map
    (q ⊗ₘ 𝟙 (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n))).hom).comp
      (AlgebraicGeometry.SheafCohomology.Projective.TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistPolynomialSectionEquiv j a n ha).symm.toLinearMap

theorem negativeTwistPolynomialColumn_coefficient
    {N : (Proj (homogeneousSubmodule σ R)).Modules} (j : σ) (a n : ℕ) (ha : a ≤ n)
    (q : AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⟶ N)
    (p : homogeneousSubmodule σ Γ(Spec (.of R), ⊤) (n - a)) :
    TensorSectionRestriction.Construction.tensorSectionGlobalCoefficient N (ProjectiveNormalizedSections.Construction.projectiveTwistUnitSection j n) (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
      (negativeTwistPolynomialColumn j a n ha q p) =
    ProjectiveChartPolynomialMap.Construction.projectiveChartPolynomialMap j p.val •
      q.app (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j) (AlgebraicGeometry.SheafCohomology.Projective.DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j a) := by
  obtain ⟨x, rfl⟩ := (AlgebraicGeometry.SheafCohomology.Projective.TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistPolynomialSectionEquiv (R := R) j a n ha).surjective p
  unfold negativeTwistPolynomialColumn
  erw [LinearMap.comp_apply, LinearEquiv.symm_apply_apply]
  exact negativeTwist_map_tensorSectionGlobalCoefficient j a n ha q x

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.NegativeTwistMapCoefficients.Construction
