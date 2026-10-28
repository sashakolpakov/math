import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedCoproductPolynomialMap
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ProjectiveSectionDegreeCokernel
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PresentationDegreeMap
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PresentationCoordinateMapEquality

/-! # Section Polynomial Map -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective

noncomputable section

open _root_.MvPolynomial

/-! Identification of the actual section presentation with its polynomial degree map. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry OAI.AlgebraicGeometry.SheafCohomology.Projective.PresentationCoordinateMapEquality
universe u
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra TwistedCoproductPolynomialSections.MvPolynomial.polynomialCoproductBiproducts
open OAI.AlgebraicGeometry.SheafCohomology.Projective.TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation
variable {j : σ} {M : (Proj (homogeneousSubmodule σ R)).Modules}
    (D : TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation j M)

theorem TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.sectionDegreeMap_eq_polynomialDegreeMap (n : ℕ)
    (hr : ∀ i, D.rowDegree i ≤ n) (hc : ∀ k, D.columnDegree k ≤ n) :
    D.sectionDegreeMap n hr hc = D.polynomialDegreeMap n := by
  dsimp only [TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.sectionDegreeMap]
  apply PresentationCoordinateMapEquality.presentationCoordinateMap_eq_of
  intro x
  apply Subtype.ext
  apply Finsupp.ext
  intro i
  rw [CategoryTheory.Iso.toLinearEquiv_apply, CategoryTheory.Iso.toLinearEquiv_apply,
    TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.polynomialDegreeMap_apply]
  have h := TwistedCoproductPolynomialMap.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso_map_component (R := R)
    j D.rowDegree D.columnDegree D.degree_order n hr hc D.relations x i
  convert h using 1
  dsimp only [TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.polynomialMatrix]

def TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.sectionDegreeCokernelEquivDegreeCokernel (n : ℕ)
    (hr : ∀ i, D.rowDegree i ≤ n) (hc : ∀ k, D.columnDegree k ≤ n) :
    D.SectionDegreeCokernel n hr hc ≃ₗ[Γ(Spec (CommRingCat.of R), ⊤)]
      D.DegreeCokernel (n : ℤ) :=
  (Submodule.quotEquivOfEq _ _ (congrArg LinearMap.range
    (D.sectionDegreeMap_eq_polynomialDegreeMap n hr hc))).trans
      (D.polynomialDegreeCokernelEquiv n)

theorem TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.eventually_degreeCokernel_sections [IsNoetherianRing R] [M.IsQuasicoherent] :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      Nonempty (D.DegreeCokernel (n : ℤ) ≃ₗ[Γ(Spec (CommRingCat.of R), ⊤)]
        (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
          ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.obj M)) := by
  obtain ⟨b, hb⟩ := D.eventually_sectionDegreeCokernel
  refine ⟨b, fun n hn => ?_⟩
  obtain ⟨hr, hc, ⟨e⟩⟩ := hb n hn
  exact ⟨(D.sectionDegreeCokernelEquivDegreeCokernel n hr hc).symm.trans e⟩

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective
