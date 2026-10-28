import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedPolynomialMapSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedSectionsDetectMorphism
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwoStagePresentation

/-! # Graded Polynomial Complex -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedPolynomialComplex

noncomputable section

open _root_.MvPolynomial

/-! Compositions vanishing in a homogeneous polynomial sequence vanish in its actual sheaf realization. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
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

theorem coordinateGradedPolynomialSheafMap_comp_sections_zero (hfg : f.comp g = 0)
    (n : ℕ) (hd : ∀ i, d i ≤ n) (he : ∀ k, e k ≤ n) (hw : ∀ k, w k ≤ n)
    (x : (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
      ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.obj
        (∐ fun k => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (w k)))) :
    (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).map
      ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.map
        (GradedPolynomialMap.MvPolynomial.coordinateGradedPolynomialSheafMap j e w g hg ≫ GradedPolynomialMap.MvPolynomial.coordinateGradedPolynomialSheafMap j d e f hf)) x = 0 := by
  apply (TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso j d n hd).toLinearEquiv.injective
  rw [map_zero]
  apply Subtype.ext
  rw [Iso.toLinearEquiv_apply]
  rw [Functor.map_comp, Functor.map_comp, ModuleCat.comp_apply,
    GradedPolynomialMapSections.MvPolynomial.coordinateGradedPolynomialSheafMap_sections j d e f hf n hd he,
    GradedPolynomialMapSections.MvPolynomial.coordinateGradedPolynomialSheafMap_sections j e w g hg n he hw]
  exact LinearMap.congr_fun hfg ((TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso j w n hw).hom x).val

theorem coordinateGradedPolynomialSheafMap_comp_zero [IsNoetherianRing R] (hfg : f.comp g = 0) :
    GradedPolynomialMap.MvPolynomial.coordinateGradedPolynomialSheafMap j e w g hg ≫ GradedPolynomialMap.MvPolynomial.coordinateGradedPolynomialSheafMap j d e f hf = 0 := by
  have := TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_quasicoherent (R := R) j w
  have := TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_finiteType (R := R) j w
  have := TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_quasicoherent (R := R) j d
  let b := Finset.univ.sup d + Finset.univ.sup e + Finset.univ.sup w
  apply TwistedSectionsDetectMorphism.MvPolynomial.finiteType_hom_eq_zero_of_eventually_twistedSections_eq_zero _ j b
  intro n hn x
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
  exact coordinateGradedPolynomialSheafMap_comp_sections_zero j d e w f g hf hg hfg n hd he hw x

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedPolynomialComplex
