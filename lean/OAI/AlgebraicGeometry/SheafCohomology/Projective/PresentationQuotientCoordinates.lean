import OAI.AlgebraicGeometry.SheafCohomology.Projective.PresentationGradedModule
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedQuotientDegreeMap
import OAI.AlgebraicGeometry.SheafCohomology.Projective.SurjectiveLinearCoordinates

/-! # Presentation Quotient Coordinates -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective

noncomputable section

open _root_.MvPolynomial

/-! Natural quotient coordinates for the large twisted sections of an actual presentation. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry OAI.AlgebraicGeometry.SheafCohomology.Projective.SurjectiveLinearCoordinates
universe u
open OAI.AlgebraicGeometry.SheafCohomology.Projective.TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra
variable {j : σ} {M : (Proj (homogeneousSubmodule σ R)).Modules}
    (D : TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation j M)

def TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.gradedCokernelProjectionDegree (n : ℕ) :
    D.RowDegreeSpace n →ₗ[Γ(Spec (CommRingCat.of R), ⊤)] D.gradedCokernel.grading (n : ℤ) :=
  GradedModuleMk.GradedModuleQuotient.degreeMap D.generatorModule.grading D.polynomialMap.range (n : ℤ)

theorem TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.exists_gradedCokernel_sections_compatible (n : ℕ)
    (hr : ∀ i, D.rowDegree i ≤ n) (hc : ∀ k, D.columnDegree k ≤ n)
    (hex : Function.Exact
      ((AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).map
        ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.map
          D.relations)).hom
      ((AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).map
        ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.map
          D.projection)).hom)
    (hs : Function.Surjective
      ((AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).map
        ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.map
          D.projection)).hom) :
    ∃ e : D.gradedCokernel.grading (n : ℤ) ≃ₗ[Γ(Spec (CommRingCat.of R), ⊤)]
        (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
          ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.obj M),
      ∀ x, e (D.gradedCokernelProjectionDegree n
        ((TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso (R := R) j D.rowDegree n hr).hom x)) =
        (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).map
          ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.map
            D.projection) x := by
  let G := AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
  let F := (PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor
  let er := (TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso (R := R) j D.rowDegree n hr).toLinearEquiv
  let ec := (TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso (R := R) j D.columnDegree n hc).toLinearEquiv
  let q := D.gradedCokernelProjectionDegree n
  let p := (G.map (F.map D.projection)).hom.comp er.symm.toLinearMap
  have hq : Function.Surjective q :=
    GradedQuotientDegreeMap.GradedModuleQuotient.degreeMap_surjective D.generatorModule.grading D.polynomialMap.range (n : ℤ)
  have hp : Function.Surjective p := hs.comp er.symm.surjective
  have he' := PresentedTargetCoordinates.presentationCoordinateMap_exact (G.map (F.map D.relations)).hom
      (G.map (F.map D.projection)).hom hex ec er
  have he : Function.Exact (D.sectionDegreeMap n hr hc) p := by
    convert he' using 1
    funext x
    dsimp only [TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.sectionDegreeMap, PresentedTargetCoordinates.presentationCoordinateMap, LinearMap.comp_apply,
      LinearEquiv.coe_coe, er, ec, F, G]
  have hk : q.ker = p.ker := by
    rw [LinearMap.exact_iff.mp he, D.sectionDegreeMap_eq_polynomialDegreeMap n hr hc]
    exact (GradedQuotientDegreeMap.GradedModuleQuotient.degreeMap_kernel D.generatorModule.grading
      D.polynomialMap.range (n : ℤ)).trans
      (GradedCokernelDegree.homogeneousDegreeMap_range _ _ D.polynomialMap D.polynomialMap_homogeneous (n : ℤ)).symm
  refine ⟨SurjectiveLinearCoordinates.surjectiveLinearCoordinates q p hq hp hk, fun x => ?_⟩
  change SurjectiveLinearCoordinates.surjectiveLinearCoordinates q p hq hp hk (q (er x)) = _
  rw [SurjectiveLinearCoordinates.surjectiveLinearCoordinates_apply]
  change (G.map (F.map D.projection)).hom (er.symm (er x)) = _
  rw [er.symm_apply_apply]

theorem TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.eventually_gradedCokernel_sections_compatible [IsNoetherianRing R] [M.IsQuasicoherent] :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      ∃ (hr : ∀ i, D.rowDegree i ≤ n)
        (e : D.gradedCokernel.grading (n : ℤ) ≃ₗ[Γ(Spec (CommRingCat.of R), ⊤)]
          (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
            ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.obj M)),
        ∀ x, e (D.gradedCokernelProjectionDegree n
          ((TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso (R := R) j D.rowDegree n hr).hom x)) =
          (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).map
            ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.map
              D.projection) x := by
  let T := ShortComplex.mk D.relations D.projection D.zero
  have : Epi T.g := D.epi
  have : T.X₁.IsQuasicoherent := TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_quasicoherent j D.columnDegree
  have : T.X₁.IsFiniteType := TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_finiteType j D.columnDegree
  have : T.X₂.IsQuasicoherent := TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_quasicoherent j D.rowDegree
  have : T.X₂.IsFiniteType := TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_finiteType j D.rowDegree
  have : T.X₃.IsQuasicoherent := inferInstanceAs M.IsQuasicoherent
  obtain ⟨b, hb⟩ := PresentationSections.MvPolynomial.finiteType_exact_eventually_projectiveTwist_sections T D.exact j
  let B := max b (max (Finset.univ.sup D.rowDegree) (Finset.univ.sup D.columnDegree))
  refine ⟨B, fun n hn => ?_⟩
  have hr : ∀ i, D.rowDegree i ≤ n := fun i =>
    (Finset.le_sup (f := D.rowDegree) (Finset.mem_univ i)).trans
      ((le_trans (le_max_left _ _) (le_max_right _ _)).trans hn)
  have hc : ∀ k, D.columnDegree k ≤ n := fun k =>
    (Finset.le_sup (f := D.columnDegree) (Finset.mem_univ k)).trans
      ((le_trans (le_max_right _ _) (le_max_right _ _)).trans hn)
  obtain ⟨hex, hs⟩ := hb n ((le_max_left _ _).trans hn)
  obtain ⟨e, he⟩ := D.exists_gradedCokernel_sections_compatible n hr hc hex hs
  exact ⟨hr, e, he⟩

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective
