import OAI.AlgebraicGeometry.SheafCohomology.Projective.WeightedFreeMapMatrix
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoproductMatrixConstruction
import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistSectionCoordinates

/-! # Graded Polynomial Map -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedPolynomialMap

noncomputable section

open _root_.MvPolynomial

/-! Realizing homogeneous polynomial maps as actual maps between negative-twist sheaves. -/

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

def coordinateGradedPolynomialEntry (i : Fin r) (k : Fin s) :
    TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (e k) ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d i) :=
  if h : d i ≤ e k then
    (NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials (R := R) j (e k) (d i) h).symm
      (WeightedFreeMapMatrix.weightedFreeMapPolynomial d e f hf i k)
  else 0

def coordinateGradedPolynomialSheafMap :
    (∐ fun k => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (e k)) ⟶
      (∐ fun i => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d i)) :=
  CoproductMatrixConstruction.finiteCoproductMatrixHom
    (fun k => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (e k))
    (fun i => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d i))
    (coordinateGradedPolynomialEntry j d e f hf)

theorem coordinateGradedPolynomialSheafMap_component (i : Fin r) (k : Fin s) :
    Sigma.ι (fun k => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (e k)) k ≫
      coordinateGradedPolynomialSheafMap j d e f hf ≫
        CoproductMatrixComponents.finiteCoproductProjection (fun i => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d i)) i =
          coordinateGradedPolynomialEntry j d e f hf i k :=
  CoproductMatrixConstruction.finiteCoproductMatrixHom_component _ _ _ i k

theorem coordinateGradedPolynomialEntry_sections (i : Fin r) (k : Fin s) (n : ℕ)
    (hd : d i ≤ n) (he : e k ≤ n)
    (x : (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
      ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.obj
        (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (e k)))) :
    (TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistPolynomialSectionEquiv j (d i) n hd
      ((AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).map
        ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.map
          (coordinateGradedPolynomialEntry j d e f hf i k)) x)).val =
      f (Finsupp.single k 1) i * (TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistPolynomialSectionEquiv j (e k) n he x).val := by
  by_cases h : d i ≤ e k
  · rw [coordinateGradedPolynomialEntry, dite_eq_left h]
    rw [NegativeTwistSectionCoordinates.MvPolynomial.negativeTwistPolynomialSectionEquiv_map j (e k) (d i) n h he hd,
      Equiv.apply_symm_apply, WeightedFreeMapMatrix.weightedFreeMapPolynomial_val]
  · rw [coordinateGradedPolynomialEntry, dite_eq_right h,
      WeightedFreeMapMatrix.weightedFreeMapCoefficient_zero d e f hf i k (lt_of_not_ge h)]
    simp

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedPolynomialMap
