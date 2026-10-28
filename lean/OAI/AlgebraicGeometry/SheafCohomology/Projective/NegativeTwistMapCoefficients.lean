import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistCoefficients
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections

/-! # Negative Twist Map Coefficients -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistMapCoefficients.Dimension

noncomputable section

/-! Each column of a negative-twist presentation acts by its actual local generator. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory _root_.MvPolynomial

open OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction

universe u

local instance negativeTwistMapCoefficientsMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem negativeTwist_map_tensorSectionGlobalCoefficient
    {N : (Proj (homogeneousSubmodule σ R)).Modules} (j : σ) (a n : ℕ) (ha : a ≤ n)
    (q : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⟶ N)
    (x : Γ(TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⊗
      TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n, ⊤)) :
    ArithmeticGeometry.OrdinaryLocus.Openness.TensorSectionRestriction.Construction.tensorSectionGlobalCoefficient N (UnitSection.Dimension.projectiveTwistUnitSection j n) (MvPolynomialClosure.MvPolynomial.coordinateOpen j)
      ((q ⊗ₘ 𝟙 (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n)).app ⊤ x) =
    ChartPolynomialMap.Dimension.projectiveChartPolynomialMap j (TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistPolynomialSectionEquiv j a n ha x).val •
      q.app (MvPolynomialClosure.MvPolynomial.coordinateOpen j) (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j a) := by
  have hn := ArithmeticGeometry.OrdinaryLocus.Openness.TensorSectionRestriction.Construction.tensorSectionGlobalCoefficient_naturality q (UnitSection.Dimension.projectiveTwistUnitSection j n)
    (MvPolynomialClosure.MvPolynomial.coordinateOpen j) x
  have hc := NegativeTwistCoefficients.Dimension.negativeTwist_tensorSectionGlobalCoefficient (R := R) j a n ha x
  exact hn.trans ((congrArg (q.app (MvPolynomialClosure.MvPolynomial.coordinateOpen j)) hc).trans (q.app_smul _ _))

def negativeTwistPolynomialColumn {N : (Proj (homogeneousSubmodule σ R)).Modules}
    (j : σ) (a n : ℕ) (ha : a ≤ n) (q : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⟶ N) :
    homogeneousSubmodule σ Γ(Spec (.of R), ⊤) (n - a) →ₗ[Γ(Spec (.of R), ⊤)]
      (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
        (N ⊗ TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n) :=
  (((AdditiveCoproductSections.baseGlobalSectionsFunctor MvPolynomialClosure.MvPolynomial.homogeneousProjπ).map
    (q ⊗ₘ 𝟙 (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n))).hom).comp
      (TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistPolynomialSectionEquiv j a n ha).symm.toLinearMap

theorem negativeTwistPolynomialColumn_coefficient
    {N : (Proj (homogeneousSubmodule σ R)).Modules} (j : σ) (a n : ℕ) (ha : a ≤ n)
    (q : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⟶ N)
    (p : homogeneousSubmodule σ Γ(Spec (.of R), ⊤) (n - a)) :
    ArithmeticGeometry.OrdinaryLocus.Openness.TensorSectionRestriction.Construction.tensorSectionGlobalCoefficient N (UnitSection.Dimension.projectiveTwistUnitSection j n) (MvPolynomialClosure.MvPolynomial.coordinateOpen j)
      (negativeTwistPolynomialColumn j a n ha q p) =
    ChartPolynomialMap.Dimension.projectiveChartPolynomialMap j p.val •
      q.app (MvPolynomialClosure.MvPolynomial.coordinateOpen j) (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j a) := by
  obtain ⟨x, rfl⟩ := (TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistPolynomialSectionEquiv (R := R) j a n ha).surjective p
  unfold negativeTwistPolynomialColumn
  erw [LinearMap.comp_apply, LinearEquiv.symm_apply_apply]
  exact negativeTwist_map_tensorSectionGlobalCoefficient j a n ha q x

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistMapCoefficients.Dimension
