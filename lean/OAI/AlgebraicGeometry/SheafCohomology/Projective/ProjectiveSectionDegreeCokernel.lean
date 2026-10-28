import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedCoproductPolynomialSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PresentedTargetCoordinates
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PresentationSections

/-! # Projective Section Degree Cokernel -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective

noncomputable section

open _root_.MvPolynomial

/-! An actual coherent sheaf's large twists are presented by maps on polynomial degree spaces. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry OAI.AlgebraicGeometry.SheafCohomology.Projective.PresentedTargetCoordinates
universe u
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

variable {j : σ} {M : (Proj (homogeneousSubmodule σ R)).Modules}
    (D : TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation j M)

abbrev TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.RowDegreeSpace (n : ℕ) : Type u :=
  ↥(HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading (σ := σ) Γ(Spec (CommRingCat.of R), ⊤)
    (fun i => (D.rowDegree i : ℤ)) (n : ℤ))

abbrev TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.ColumnDegreeSpace (n : ℕ) : Type u :=
  ↥(HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading (σ := σ) Γ(Spec (CommRingCat.of R), ⊤)
    (fun k => (D.columnDegree k : ℤ)) (n : ℤ))

def TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.sectionDegreeMap (n : ℕ) (hr : ∀ i, D.rowDegree i ≤ n)
    (hc : ∀ k, D.columnDegree k ≤ n) :
    D.ColumnDegreeSpace n →ₗ[Γ(Spec (CommRingCat.of R), ⊤)] D.RowDegreeSpace n :=
  let G := AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
  let F := (PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor
  PresentedTargetCoordinates.presentationCoordinateMap (G.map (F.map D.relations)).hom
    (TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso j D.columnDegree n hc).toLinearEquiv
    (TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso j D.rowDegree n hr).toLinearEquiv

def TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.sectionDegreeRange (n : ℕ) (hr : ∀ i, D.rowDegree i ≤ n)
    (hc : ∀ k, D.columnDegree k ≤ n) :
    Submodule Γ(Spec (CommRingCat.of R), ⊤) (D.RowDegreeSpace n) :=
  (D.sectionDegreeMap n hr hc).range

abbrev TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.SectionDegreeCokernel (n : ℕ) (hr : ∀ i, D.rowDegree i ≤ n)
    (hc : ∀ k, D.columnDegree k ≤ n) :=
  PresentedTargetCoordinates.LinearCokernel (R := Γ(Spec (CommRingCat.of R), ⊤))
    (M := D.ColumnDegreeSpace n) (N := D.RowDegreeSpace n) (D.sectionDegreeMap n hr hc)

theorem TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.eventually_sectionDegreeCokernel [IsNoetherianRing R] [M.IsQuasicoherent] :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      ∃ (hr : ∀ i, D.rowDegree i ≤ n) (hc : ∀ k, D.columnDegree k ≤ n),
        Nonempty ((D.SectionDegreeCokernel n hr hc) ≃ₗ[
          Γ(Spec (CommRingCat.of R), ⊤)]
          (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
            ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.obj M)) := by
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
  let G := AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
  let F := (PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor
  exact ⟨hr, hc, ⟨PresentedTargetCoordinates.presentedTargetCoordinatesEquiv
    (G.map (F.map D.relations)).hom (G.map (F.map D.projection)).hom hex hs
    (TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso j D.columnDegree n hc).toLinearEquiv
    (TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso j D.rowDegree n hr).toLinearEquiv⟩⟩

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective
