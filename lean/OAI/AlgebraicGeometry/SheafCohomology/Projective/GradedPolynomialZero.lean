import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedPolynomialMapSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedSectionsDetectMorphism
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwoStagePresentation

/-! # Graded Polynomial Zero -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedPolynomialZero

noncomputable section

open _root_.MvPolynomial

/-! Zero homogeneous polynomial maps realize as zero morphisms of actual twist sheaves. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra TwistedCoproductPolynomialSections.MvPolynomial.polynomialCoproductBiproducts
variable (j : σ) {r s : ℕ} (d : Fin r → ℕ) (e : Fin s → ℕ)
variable (f : (Fin s →₀ MvPolynomial σ Γ(Spec (CommRingCat.of R), ⊤)) →ₗ[
  MvPolynomial σ Γ(Spec (CommRingCat.of R), ⊤)]
    (Fin r →₀ MvPolynomial σ Γ(Spec (CommRingCat.of R), ⊤)))
variable (hf : ∀ n x, x ∈ HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading
    Γ(Spec (CommRingCat.of R), ⊤) (fun k => (e k : ℤ)) n →
  f x ∈ HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading
    Γ(Spec (CommRingCat.of R), ⊤) (fun i => (d i : ℤ)) n)

theorem coordinateGradedPolynomialSheafMap_sections_zero (hzero : f = 0)
    (n : ℕ) (hd : ∀ i, d i ≤ n) (he : ∀ k, e k ≤ n)
    (x : (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
      ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.obj
        (∐ fun k => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (e k)))) :
    (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).map
      ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.map
        (GradedPolynomialMap.MvPolynomial.coordinateGradedPolynomialSheafMap j d e f hf)) x = 0 := by
  apply (TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso (R := R) j d n hd).toLinearEquiv.injective
  rw [map_zero]
  apply Subtype.ext
  rw [Iso.toLinearEquiv_apply, GradedPolynomialMapSections.MvPolynomial.coordinateGradedPolynomialSheafMap_sections j d e f hf n hd he x,
    hzero, LinearMap.zero_apply]
  rfl

theorem coordinateGradedPolynomialSheafMap_zero [IsNoetherianRing R] (hzero : f = 0) :
    GradedPolynomialMap.MvPolynomial.coordinateGradedPolynomialSheafMap j d e f hf = 0 := by
  have := TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_quasicoherent (R := R) j e
  have := TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_finiteType (R := R) j e
  have := TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_quasicoherent (R := R) j d
  let b := Finset.univ.sup d + Finset.univ.sup e
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
  exact coordinateGradedPolynomialSheafMap_sections_zero j d e f hf hzero n hd he x

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedPolynomialZero
