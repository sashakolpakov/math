import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedCoproductPolynomialSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.WeightedFreeComponentValues

/-! # Twisted Coproduct Components -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedCoproductComponents

noncomputable section

open _root_.MvPolynomial

/-! Polynomial components of actual sections of twisted finite coproducts. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry OAI.AlgebraicGeometry.SheafCohomology.Projective.WeightedFreeComponentValues
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] TwistedCoproductPolynomialSections.MvPolynomial.polynomialCoproductBiproducts

theorem negativeTwistCoproductPolynomialSectionsIso_component
    (j : σ) {r : ℕ} (d : Fin r → ℕ) (n : ℕ) (hd : ∀ i, d i ≤ n)
    (x : (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
      ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.obj
        (∐ fun i => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d i)))) (i : Fin r) :
    ((TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso j d n hd).hom x).val i =
      (TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistPolynomialSectionEquiv j (d i) n (hd i)
        ((AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).map
          ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.map
            (CoproductMatrixComponents.finiteCoproductProjection
              (fun k => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d k)) i)) x)).val := by
  let G := AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
  let F := (PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor
  let : F.Additive := Functor.additive_of_preserves_binary_products F
  let : (F ⋙ G).Additive := by dsimp only [G]; infer_instance
  let M := fun k : Fin r => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d k)
  let V := fun k : Fin r => ModuleCat.of Γ(Spec (CommRingCat.of R), ⊤)
    (homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) (n - d k))
  let e := fun k : Fin r => TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistPolynomialSectionEquiv (R := R) j (d k) n (hd k)
  have h := AdditiveCoproductCoordinates.additiveCoproductCoordinates_reassemble (F ⋙ G) M V e
    (H := ↥(HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading (σ := σ) Γ(Spec (CommRingCat.of R), ⊤)
      (fun k => (d k : ℤ)) (n : ℤ)))
    (WeightedFreeDegreeComponents.weightedFreeDegreeComponentsEquiv (R := Γ(Spec (CommRingCat.of R), ⊤))
      (σ := σ) d n hd) x i
  have hv := congrArg (fun z : homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤)
    (n - d i) => z.val) h
  convert hv using 1
  · rw [WeightedFreeComponentValues.weightedFreeDegreeComponentsEquiv_apply_val]
    dsimp +instances only [TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso, F, G, M, V, e,
      Functor.comp_obj, Functor.comp_map]
  · dsimp +instances only [F, G, M, e, Functor.comp_obj, Functor.comp_map]

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedCoproductComponents
