import OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteGradedQuotient
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedMinimalFiniteCover

/-! # Graded Quotient Lift -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedQuotientLift

noncomputable section

/-! Homogeneous lifts of the minimal free cover through an actual graded quotient. -/

set_option backward.isDefEq.respectTransparency false
universe u
namespace GradedQuotientMinimalLift
variable {K : Type u} [Field K] {σ : Type} [Fintype σ]
variable (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ K)
variable (P : Submodule (MvPolynomial σ K) D.Carrier) (hP : P.IsHomogeneous D.grading)
variable (hQ : GradedNonnegativeSyzygy.HasNonnegativeGrading (FiniteGradedQuotient.finiteGradedQuotient D P hP))

include hQ in
theorem exists_liftVector (i : Fin (GradedMinimalFiniteCover.augmentationRank (FiniteGradedQuotient.finiteGradedQuotient D P hP))) :
    ∃ y : D.Carrier,
      y ∈ D.grading (GradedMinimalFiniteCover.augmentationFinWeight (FiniteGradedQuotient.finiteGradedQuotient D P hP) i : ℤ) ∧
        P.mkQ y = GradedMinimalFiniteCover.augmentationFinProjection (FiniteGradedQuotient.finiteGradedQuotient D P hP) (Finsupp.single i 1) := by
  let Q := FiniteGradedQuotient.finiteGradedQuotient D P hP
  have hy := GradedMinimalFiniteCover.augmentationFinProjection_homogeneous Q hQ (GradedMinimalFiniteCover.augmentationFinWeight Q i : ℤ)
    (Finsupp.single i 1) (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFree_single_homogeneous K (fun k => (GradedMinimalFiniteCover.augmentationFinWeight Q k : ℤ)) i)
  exact hy

def liftVector (i : Fin (GradedMinimalFiniteCover.augmentationRank (FiniteGradedQuotient.finiteGradedQuotient D P hP))) : D.Carrier :=
  Classical.choose (exists_liftVector D P hP hQ i)

theorem liftVector_homogeneous (i : Fin (GradedMinimalFiniteCover.augmentationRank (FiniteGradedQuotient.finiteGradedQuotient D P hP))) :
    liftVector D P hP hQ i ∈ D.grading (GradedMinimalFiniteCover.augmentationFinWeight (FiniteGradedQuotient.finiteGradedQuotient D P hP) i : ℤ) :=
  (Classical.choose_spec (exists_liftVector D P hP hQ i)).1

theorem projection_liftVector (i : Fin (GradedMinimalFiniteCover.augmentationRank (FiniteGradedQuotient.finiteGradedQuotient D P hP))) :
    P.mkQ (liftVector D P hP hQ i) =
      GradedMinimalFiniteCover.augmentationFinProjection (FiniteGradedQuotient.finiteGradedQuotient D P hP) (Finsupp.single i 1) :=
  (Classical.choose_spec (exists_liftVector D P hP hQ i)).2

def lift : (GradedMinimalFiniteCover.augmentationFinFreeModule (FiniteGradedQuotient.finiteGradedQuotient D P hP)).Carrier →ₗ[MvPolynomial σ K] D.Carrier :=
  Finsupp.linearCombination (MvPolynomial σ K) (liftVector D P hP hQ)

theorem lift_homogeneous (n : ℤ)
    (x : (GradedMinimalFiniteCover.augmentationFinFreeModule (FiniteGradedQuotient.finiteGradedQuotient D P hP)).Carrier)
    (hx : x ∈ (GradedMinimalFiniteCover.augmentationFinFreeModule (FiniteGradedQuotient.finiteGradedQuotient D P hP)).grading n) :
    lift D P hP hQ x ∈ D.grading n :=
  HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFree_linearCombination_homogeneous K D.grading
    (fun k => (GradedMinimalFiniteCover.augmentationFinWeight (FiniteGradedQuotient.finiteGradedQuotient D P hP) k : ℤ))
    (liftVector D P hP hQ) (liftVector_homogeneous D P hP hQ) n x hx

theorem projection_comp_lift : P.mkQ.comp (lift D P hP hQ) =
    GradedMinimalFiniteCover.augmentationFinProjection (FiniteGradedQuotient.finiteGradedQuotient D P hP) := by
  apply Finsupp.lhom_ext
  intro i a
  change P.mkQ (lift D P hP hQ (Finsupp.single i a)) =
    GradedMinimalFiniteCover.augmentationFinProjection (FiniteGradedQuotient.finiteGradedQuotient D P hP) (Finsupp.single i a)
  erw [lift, Finsupp.linearCombination_single, map_smul, projection_liftVector, ← map_smul]
  congr 1
  change (a • Finsupp.single i (1 : MvPolynomial σ K) :
    Fin (GradedMinimalFiniteCover.augmentationRank (FiniteGradedQuotient.finiteGradedQuotient D P hP)) →₀ MvPolynomial σ K) = Finsupp.single i a
  simp

end GradedQuotientMinimalLift

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedQuotientLift
