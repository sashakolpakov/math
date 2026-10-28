import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedPolynomialComplex
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ExactLinearCoordinates
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedSectionsDetectExact

/-! # Graded Polynomial Exact -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedPolynomialExact

noncomputable section

open _root_.MvPolynomial

/-! Exact homogeneous polynomial sequences give exact sequences of actual twist sheaves. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry OAI.AlgebraicGeometry.SheafCohomology.Projective.ExactLinearCoordinates
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra TwistedCoproductPolynomialSections.MvPolynomial.polynomialCoproductBiproducts
variable (j : σ) {r s t : ℕ} (d : Fin r → ℕ) (e : Fin s → ℕ) (w : Fin t → ℕ)
variable (f : (Fin s →₀ MvPolynomial σ Γ(Spec (CommRingCat.of R), ⊤)) →ₗ[
  MvPolynomial σ Γ(Spec (CommRingCat.of R), ⊤)] (Fin r →₀ MvPolynomial σ Γ(Spec (CommRingCat.of R), ⊤)))
variable (g : (Fin t →₀ MvPolynomial σ Γ(Spec (CommRingCat.of R), ⊤)) →ₗ[
  MvPolynomial σ Γ(Spec (CommRingCat.of R), ⊤)] (Fin s →₀ MvPolynomial σ Γ(Spec (CommRingCat.of R), ⊤)))
variable (hf : ∀ q x, x ∈ HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading Γ(Spec (CommRingCat.of R), ⊤) (fun k => (e k : ℤ)) q →
  f x ∈ HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading Γ(Spec (CommRingCat.of R), ⊤) (fun i => (d i : ℤ)) q)
variable (hg : ∀ q x, x ∈ HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading Γ(Spec (CommRingCat.of R), ⊤) (fun k => (w k : ℤ)) q →
  g x ∈ HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading Γ(Spec (CommRingCat.of R), ⊤) (fun i => (e i : ℤ)) q)

theorem coordinateGradedPolynomialSheafMap_sections_exact (hex : Function.Exact g f)
    (n : ℕ) (hd : ∀ i, d i ≤ n) (he : ∀ k, e k ≤ n) (hw : ∀ k, w k ≤ n) :
    Function.Exact
      ((AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).map
        ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.map
          (GradedPolynomialMap.MvPolynomial.coordinateGradedPolynomialSheafMap j e w g hg))).hom
      ((AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).map
        ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.map
          (GradedPolynomialMap.MvPolynomial.coordinateGradedPolynomialSheafMap j d e f hf))).hom := by
  apply ExactLinearCoordinates.exact_of_linearEquiv_coordinates
    (TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso (R := R) j w n hw).toLinearEquiv
    (TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso (R := R) j e n he).toLinearEquiv
    (TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso (R := R) j d n hd).toLinearEquiv
    _ _
    (HilbertScheme.Presentations.Graded.Exactness.GradedModules.degreeMap _ _ (g.restrictScalars Γ(Spec (CommRingCat.of R), ⊤)) hg (n : ℤ))
    (HilbertScheme.Presentations.Graded.Exactness.GradedModules.degreeMap _ _ (f.restrictScalars Γ(Spec (CommRingCat.of R), ⊤)) hf (n : ℤ))
  · intro x
    apply Subtype.ext
    rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply]
    convert GradedPolynomialMapSections.MvPolynomial.coordinateGradedPolynomialSheafMap_sections (R := R) j e w g hg n he hw x using 1
    rfl
  · intro x
    apply Subtype.ext
    rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply]
    convert GradedPolynomialMapSections.MvPolynomial.coordinateGradedPolynomialSheafMap_sections (R := R) j d e f hf n hd he x using 1
    rfl
  · exact HilbertScheme.Presentations.Graded.Exactness.GradedModules.degreeMap_exact _ _ _
      (g.restrictScalars Γ(Spec (CommRingCat.of R), ⊤))
      (f.restrictScalars Γ(Spec (CommRingCat.of R), ⊤)) hg hf hex (n : ℤ)

def coordinateGradedPolynomialShortComplex [IsNoetherianRing R] (hfg : f.comp g = 0) :
    ShortComplex (Proj (homogeneousSubmodule σ R)).Modules :=
  ShortComplex.mk (GradedPolynomialMap.MvPolynomial.coordinateGradedPolynomialSheafMap j e w g hg)
    (GradedPolynomialMap.MvPolynomial.coordinateGradedPolynomialSheafMap j d e f hf)
    (GradedPolynomialComplex.MvPolynomial.coordinateGradedPolynomialSheafMap_comp_zero j d e w f g hf hg hfg)

theorem coordinateGradedPolynomialShortComplex_exact [IsNoetherianRing R]
    (hfg : f.comp g = 0) (hex : Function.Exact g f) :
    (coordinateGradedPolynomialShortComplex j d e w f g hf hg hfg).Exact := by
  have := TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_quasicoherent (R := R) j w
  have := TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_quasicoherent (R := R) j e
  have := TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_finiteType (R := R) j e
  have := TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_quasicoherent (R := R) j d
  let b := Finset.univ.sup d + Finset.univ.sup e + Finset.univ.sup w
  apply TwistedSectionsDetectExact.MvPolynomial.finiteType_exact_of_eventually_twistedSections_exact _ _ _ j b
  intro n hn
  have hd (i : Fin r) : d i ≤ n := by
    have := Finset.le_sup (f := d) (Finset.mem_univ i)
    dsimp only [b] at hn
    omega
  have he (i : Fin s) : e i ≤ n := by
    have := Finset.le_sup (f := e) (Finset.mem_univ i)
    dsimp only [b] at hn
    omega
  have hw (i : Fin t) : w i ≤ n := by
    have := Finset.le_sup (f := w) (Finset.mem_univ i)
    dsimp only [b] at hn
    omega
  exact coordinateGradedPolynomialSheafMap_sections_exact j d e w f g hf hg hex n hd he hw

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedPolynomialExact
