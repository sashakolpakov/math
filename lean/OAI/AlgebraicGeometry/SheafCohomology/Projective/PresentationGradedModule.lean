import OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteGradedQuotient
import OAI.AlgebraicGeometry.SheafCohomology.Projective.SectionPolynomialMap

/-! # Presentation Graded Module -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective

noncomputable section

open _root_.MvPolynomial

/-! The nonnegatively graded module attached to an actual projective sheaf presentation. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteGradedQuotient
universe u
open OAI.AlgebraicGeometry.SheafCohomology.Projective.TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra
variable {j : σ} {M : (Proj (homogeneousSubmodule σ R)).Modules}
    (D : TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation j M)

def TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.gradedCokernel : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ Γ(Spec (CommRingCat.of R), ⊤) :=
  FiniteGradedQuotient.finiteGradedQuotient D.generatorModule D.polynomialMap.range D.polynomialRelations_homogeneous

theorem TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.gradedCokernel_nonnegative : GradedNonnegativeSyzygy.HasNonnegativeGrading D.gradedCokernel := by
  apply FiniteGradedQuotient.finiteGradedQuotient_nonnegative
  intro d hd
  exact GradedModuleLowerBound.weightedFreeGrading_eq_bot_of_lt (fun i => (D.rowDegree i : ℤ)) d
    (fun i => hd.trans_le (Int.natCast_nonneg (D.rowDegree i)))

def TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.gradedCokernelDegreeEquiv (d : ℤ) :
    D.DegreeCokernel d ≃ₗ[Γ(Spec (CommRingCat.of R), ⊤)] D.gradedCokernel.grading d :=
  FiniteGradedQuotient.finiteGradedQuotientDegreeEquiv D.generatorModule D.polynomialMap.range
    D.polynomialRelations_homogeneous d

theorem TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation.eventually_gradedCokernel_sections [IsNoetherianRing R] [M.IsQuasicoherent] :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      Nonempty (D.gradedCokernel.grading (n : ℤ) ≃ₗ[Γ(Spec (CommRingCat.of R), ⊤)]
        (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
          ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.obj M)) := by
  obtain ⟨b, hb⟩ := D.eventually_degreeCokernel_sections
  refine ⟨b, fun n hn => ?_⟩
  obtain ⟨e⟩ := hb n hn
  exact ⟨(D.gradedCokernelDegreeEquiv (n : ℤ)).symm.trans e⟩

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective
