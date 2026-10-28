import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedPolynomialMapSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedSectionsDetectMono
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwoStagePresentation
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleHomAppEvaluation

/-! # Graded Polynomial Mono -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedPolynomialMono

noncomputable section

open _root_.MvPolynomial

/-! Injective homogeneous polynomial maps give actual monomorphisms of twist sheaves. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleHomAppEvaluation
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

theorem coordinateGradedPolynomialSheafMap_sections_injective
    (hinj : Function.Injective f) (n : ℕ) (hd : ∀ i, d i ≤ n) (he : ∀ k, e k ≤ n) :
    Function.Injective
      ((AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).map
        ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.map
          (GradedPolynomialMap.MvPolynomial.coordinateGradedPolynomialSheafMap j d e f hf))).hom := by
  intro x y hxy
  apply (TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso (R := R) j e n he).toLinearEquiv.injective
  apply Subtype.ext
  rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply]
  apply hinj
  have hx := GradedPolynomialMapSections.MvPolynomial.coordinateGradedPolynomialSheafMap_sections j d e f hf n hd he x
  have hy := GradedPolynomialMapSections.MvPolynomial.coordinateGradedPolynomialSheafMap_sections j d e f hf n hd he y
  rw [← hx, ← hy, hxy]

theorem coordinateGradedPolynomialSheafMap_mono [IsNoetherianRing R]
    (hinj : Function.Injective f) : Mono (GradedPolynomialMap.MvPolynomial.coordinateGradedPolynomialSheafMap j d e f hf) := by
  have := TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_quasicoherent (R := R) j e
  have := TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_finiteType (R := R) j e
  have := TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_quasicoherent (R := R) j d
  let b := Finset.univ.sup d + Finset.univ.sup e
  apply TwistedSectionsDetectMono.MvPolynomial.finiteType_mono_of_eventually_twistedSections_injective _ j b
  intro n hn
  have hd (i : Fin r) : d i ≤ n := by
    have := Finset.le_sup (f := d) (Finset.mem_univ i)
    dsimp only [b] at hn
    omega
  have he (i : Fin s) : e i ≤ n := by
    have := Finset.le_sup (f := e) (Finset.mem_univ i)
    dsimp only [b] at hn
    omega
  exact coordinateGradedPolynomialSheafMap_sections_injective j d e f hf hinj n hd he

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedPolynomialMono
