import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistSectionCoordinates
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedCoproductComponents
import OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductProjectedMap
import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistPolynomialMatrix

/-! # Twisted Coproduct Polynomial Map -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedCoproductPolynomialMap

noncomputable section

open _root_.MvPolynomial

/-! Actual twisted coproduct maps are computed by their extracted polynomial matrices. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductProjectedMap
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra TwistedCoproductPolynomialSections.MvPolynomial.polynomialCoproductBiproducts

theorem negativeTwistCoproductPolynomialSectionsIso_map_component
    (j : σ) {r s : ℕ} (d : Fin r → ℕ) (e : Fin s → ℕ)
    (hde : ∀ i k, d i ≤ e k) (n : ℕ) (hd : ∀ i, d i ≤ n) (he : ∀ k, e k ≤ n)
    (f : (∐ fun k => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (e k)) ⟶
      (∐ fun i => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d i)))
    (x : (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
      ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.obj
        (∐ fun k => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (e k)))) (i : Fin r) :
    ((TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso j d n hd).hom
      ((AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).map
        ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.map f) x)).val i =
      ∑ k, (NegativeTwistPolynomialMatrix.MvPolynomial.coordinateNegativeTwistPolynomialMatrix j d e hde f i k).val *
        ((TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso j e n he).hom x).val k := by
  let G := AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
  let F := (PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor
  let : F.Additive := Functor.additive_of_preserves_binary_products F
  let : (F ⋙ G).Additive := by dsimp only [G]; infer_instance
  let S := fun k : Fin s => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (e k)
  let T := fun l : Fin r => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d l)
  let w : (F ⋙ G).obj (T i) →ₗ[Γ(Spec (CommRingCat.of R), ⊤)]
      MvPolynomial σ Γ(Spec (CommRingCat.of R), ⊤) :=
    (homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) (n - d i)).subtype.comp
      (TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistPolynomialSectionEquiv (R := R) j (d i) n (hd i)).toLinearMap
  have h := AdditiveCoproductProjectedMap.additiveCoproductMatrix_projected (F ⋙ G) S T f x i w
  dsimp +instances only [w, F, G, S, T, Functor.comp_obj, Functor.comp_map,
    LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe] at h
  rw [TwistedCoproductComponents.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso_component]
  rw [h]
  apply Finset.sum_congr rfl
  intro k _
  have hk := NegativeTwistSectionCoordinates.MvPolynomial.negativeTwistPolynomialSectionEquiv_map (R := R) j (e k) (d i) n
    (hde i k) (he k) (hd i)
    (Sigma.ι S k ≫ f ≫ CoproductMatrixComponents.finiteCoproductProjection T i)
    ((F ⋙ G).map (CoproductMatrixComponents.finiteCoproductProjection S k) x)
  rw [TwistedCoproductComponents.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso_component]
  dsimp +instances only [F, G, S, T, Functor.comp_obj, Functor.comp_map] at hk
  convert hk using 1
  dsimp +instances only [NegativeTwistPolynomialMatrix.MvPolynomial.coordinateNegativeTwistPolynomialMatrix, CoproductMatrixComponents.finiteCoproductEncodedMatrix]

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedCoproductPolynomialMap
