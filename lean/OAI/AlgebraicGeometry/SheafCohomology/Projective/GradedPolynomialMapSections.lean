import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedPolynomialMap
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedCoproductComponents
import OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductProjectedMap
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialMatrixComponents

/-! # Graded Polynomial Map Sections -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedPolynomialMapSections

noncomputable section

open _root_.MvPolynomial

/-! The realized sheaf map acts on actual twisted sections by the original graded map. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra TwistedCoproductPolynomialSections.MvPolynomial.polynomialCoproductBiproducts

theorem coordinateGradedPolynomialSheafMap_sections (j : σ) {r s : ℕ}
    (d : Fin r → ℕ) (e : Fin s → ℕ)
    (f : (Fin s →₀ MvPolynomial σ Γ(Spec (CommRingCat.of R), ⊤)) →ₗ[
      MvPolynomial σ Γ(Spec (CommRingCat.of R), ⊤)]
        (Fin r →₀ MvPolynomial σ Γ(Spec (CommRingCat.of R), ⊤)))
    (hf : ∀ q x, x ∈ HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading Γ(Spec (CommRingCat.of R), ⊤) (fun k => (e k : ℤ)) q →
      f x ∈ HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading Γ(Spec (CommRingCat.of R), ⊤) (fun i => (d i : ℤ)) q)
    (n : ℕ) (hd : ∀ i, d i ≤ n) (he : ∀ k, e k ≤ n)
    (x : (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
      ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.obj
        (∐ fun k => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (e k)))) :
    ((TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso j d n hd).hom
      ((AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).map
        ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.map
          (GradedPolynomialMap.MvPolynomial.coordinateGradedPolynomialSheafMap j d e f hf)) x)).val =
      f ((TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso j e n he).hom x).val := by
  apply Finsupp.ext
  intro i
  have hrow := PolynomialMatrixComponents.homogeneousPolynomialMatrixMap_apply d e (WeightedFreeMapMatrix.weightedFreeMapPolynomial d e f hf)
    ((TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso j e n he).hom x).val i
  rw [WeightedFreeMapMatrix.homogeneousPolynomialMatrixMap_weightedFreeMapPolynomial] at hrow
  simp only [WeightedFreeMapMatrix.weightedFreeMapPolynomial_val] at hrow
  rw [hrow]
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
  have h := AdditiveCoproductProjectedMap.additiveCoproductMatrix_projected (F ⋙ G) S T
    (GradedPolynomialMap.MvPolynomial.coordinateGradedPolynomialSheafMap j d e f hf) x i w
  dsimp +instances only [w, F, G, S, T, Functor.comp_obj, Functor.comp_map,
    LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe] at h
  simp_rw [GradedPolynomialMap.MvPolynomial.coordinateGradedPolynomialSheafMap_component] at h
  rw [TwistedCoproductComponents.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso_component, h]
  apply Finset.sum_congr rfl
  intro k _
  have hk := GradedPolynomialMap.MvPolynomial.coordinateGradedPolynomialEntry_sections j d e f hf i k n (hd i) (he k)
    ((F ⋙ G).map (CoproductMatrixComponents.finiteCoproductProjection S k) x)
  rw [TwistedCoproductComponents.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso_component]
  dsimp +instances only [F, G, S, Functor.comp_obj, Functor.comp_map] at hk
  convert hk using 1

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedPolynomialMapSections
