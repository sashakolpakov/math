import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.NegativeTwistMapCoefficients
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CoproductSectionImages
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorFunctorSectionEvaluation

/-! # Negative Twist Presentation Range -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.NegativeTwistPresentationRange.Construction

noncomputable section

/-! A negative-twist presentation describes the exact image of normalized global sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry MonoidalCategory _root_.MvPolynomial
open OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorFunctorSectionEvaluation

universe u

theorem linearMap_range_comp_equiv {K M N P : Type*} [Ring K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module K P] (f : M →ₗ[K] N) (e : P ≃ₗ[K] M) :
    (f.comp e.toLinearMap).range = f.range := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨e.symm x, congrArg f (e.apply_symm_apply x)⟩

local instance negativeTwistPresentationRangeMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X
local instance negativeTwistPresentationRangeBiproducts (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem negativeTwist_presentation_normalized_range
    {N : (Proj (homogeneousSubmodule σ R)).Modules} (j : σ) {r : ℕ} (d : Fin r → ℕ)
    (q : (∐ fun i => AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d i)) ⟶ N)
    (n : ℕ) (hd : ∀ i, d i ≤ n)
    (hq : Function.Surjective
      (((AlgebraicGeometry.SheafCohomology.Projective.PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.map q).app ⊤)) :
    (BaseOpenSections.Construction.tensorSectionGlobalCoefficientLinear AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ N
      (ProjectiveNormalizedSections.Construction.projectiveTwistUnitSection j n) (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)).range =
      ⨆ i, ((BaseOpenSections.Construction.tensorSectionGlobalCoefficientLinear AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ N
        (ProjectiveNormalizedSections.Construction.projectiveTwistUnitSection j n) (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)).comp
          (NegativeTwistMapCoefficients.Construction.negativeTwistPolynomialColumn j (d i) n (hd i)
            (Sigma.ι (fun k : Fin r =>
              AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d k)) i ≫ q))).range := by
  let G := AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
  let E := AlgebraicGeometry.SheafCohomology.Projective.PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n
  let F := E.functor ⋙ G
  let M := fun i : Fin r => AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d i)
  have : E.functor.Additive := Functor.additive_of_preserves_binary_products E.functor
  have : F.Additive := inferInstanceAs (E.functor ⋙ G).Additive
  let c := BaseOpenSections.Construction.tensorSectionGlobalCoefficientLinear AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ N
    (ProjectiveNormalizedSections.Construction.projectiveTwistUnitSection j n) (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
  have hr := CoproductSectionImages.Construction.coproduct_observed_range_of_surjective F M q hq c
  refine hr.trans ?_
  apply iSup_congr
  intro i
  let e := AlgebraicGeometry.SheafCohomology.Projective.TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistPolynomialSectionEquiv (R := R) j (d i) n (hd i)
  have ht : E.functor.map (Sigma.ι M i ≫ q) =
      (Sigma.ι M i ≫ q) ⊗ₘ 𝟙 (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n) :=
    AlgebraicGeometry.SheafCohomology.Projective.TensorFunctorSectionEvaluation.invertibleRightTensorEquivalence_map_tensor _ _ _
  change (c.comp (G.map (E.functor.map (Sigma.ι M i ≫ q))).hom).range = _
  rw [ht]
  exact (linearMap_range_comp_equiv
    (c.comp (G.map ((Sigma.ι M i ≫ q) ⊗ₘ
      𝟙 (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n))).hom) e.symm).symm

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.NegativeTwistPresentationRange.Construction
