import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.NegativeTwistCoverCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.RelationCechSequence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CechHomologyBound
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.HomologyExactSequences

/-! # Coherent Cech Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoherentCechFiniteness

noncomputable section

/-! Every finite-type quasicoherent sheaf on a projective coordinate quotient has finite Čech cohomology over a Noetherian base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
  (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem projectiveCech_finite_descending_step (q : ℕ)
    (h : ∀ K : (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient I).Modules, K.IsQuasicoherent → K.IsFiniteType →
      Module.Finite R (((CoefficientCechFunctor.projectiveCoefficientCechFunctor I).obj K).homology (q + 1)))
    (M : (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient I).Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    Module.Finite R (((CoefficientCechFunctor.projectiveCoefficientCechFunctor I).obj M).homology q) := by
  rename_i hMq hMt
  change (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules at M
  dsimp only [HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient] at *
  let : M.IsQuasicoherent := hMq
  let : M.IsFiniteType := hMt
  let D := @NegativeTwistCover.ProjectiveNegativeTwistCover.ofFiniteType R _ n I M hMq hMt
  have : Module.Finite R ((D.relationSequence.map
      (CoefficientCechFunctor.projectiveCoefficientCechFunctor I)).X₁.homology (q + 1)) :=
    h D.relations
      (@NegativeTwistCover.ProjectiveNegativeTwistCover.relations_quasicoherent R _ n I M D hMq)
      (@NegativeTwistCover.ProjectiveNegativeTwistCover.relations_finiteType R _ n I M _ D hMq)
  have : Module.Finite R ((D.relationSequence.map
      (CoefficientCechFunctor.projectiveCoefficientCechFunctor I)).X₂.homology q) := D.source_cech_homology_finite q
  exact HilbertConstruction.Finite.HomologyExactSequences.FiniteHomology.finite_homology_X3
    (S := D.relationSequence.map (CoefficientCechFunctor.projectiveCoefficientCechFunctor I))
    (@NegativeTwistCover.ProjectiveNegativeTwistCover.relationCechSequence_shortExact R _ n I M D hMq)
    q (q + 1)
    (by simp only [ComplexShape.up_Rel])

theorem projectiveCoherentCech_homology_finite
    (M : (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient I).Modules) [M.IsQuasicoherent] [M.IsFiniteType] (q : ℕ) :
    Module.Finite R (((CoefficientCechFunctor.projectiveCoefficientCechFunctor I).obj M).homology q) := by
  rename_i hMq hMt
  change (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules at M
  dsimp only [HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient] at *
  let : M.IsQuasicoherent := hMq
  let : M.IsFiniteType := hMt
  by_cases hq : q ≤ n + 1
  · have h : ∀ K : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules, K.IsQuasicoherent → K.IsFiniteType →
        Module.Finite R (((CoefficientCechFunctor.projectiveCoefficientCechFunctor I).obj K).homology q) := by
      apply Nat.decreasingInduction (n := n + 1)
        (motive := fun j _ ↦ ∀ K : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules,
          K.IsQuasicoherent → K.IsFiniteType →
            Module.Finite R (((CoefficientCechFunctor.projectiveCoefficientCechFunctor I).obj K).homology j))
        (of_succ := ?_) (self := ?_) hq
      · intro j _ hj K hKq hKt
        exact @projectiveCech_finite_descending_step R _ _ n I j hj K hKq hKt
      · intro K _ _
        exact CechHomologyBound.projectiveCech_homology_finite_of_bound I K (n + 1) le_rfl
    exact h M inferInstance inferInstance
  · exact CechHomologyBound.projectiveCech_homology_finite_of_bound I M q (le_of_not_ge hq)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoherentCechFiniteness
