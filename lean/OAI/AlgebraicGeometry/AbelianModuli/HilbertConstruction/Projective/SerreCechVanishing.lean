import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.CoverTensorVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.TwistedRelationCech
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CechHomologyBound
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.VanishingHomologyExactSequences

/-! # Serre Cech Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SerreCechVanishing

noncomputable section

/-! Uniform Serre vanishing for actual coordinate Čech cohomology of every coherent projective sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem projectiveSerreCech_descending_step (q : ℕ)
    (h : ∀ K : (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient I).Modules, K.IsQuasicoherent → K.IsFiniteType →
      ∃ B : ℕ, ∀ d : ℕ, B ≤ d → ∀ j : ℕ, q + 1 ≤ j →
        IsZero ((TwistedCech.projectiveTwistedCech I K d).homology (j + 1)))
    (M : (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient I).Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d → ∀ j : ℕ, q ≤ j →
      IsZero ((TwistedCech.projectiveTwistedCech I M d).homology (j + 1)) := by
  rename_i hMq hMt
  change (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules at M
  dsimp only [HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient] at *
  let : M.IsQuasicoherent := hMq
  let : M.IsFiniteType := hMt
  let D := @NegativeTwistCover.ProjectiveNegativeTwistCover.ofFiniteType R _ n I M
    ‹M.IsQuasicoherent› ‹M.IsFiniteType›
  obtain ⟨BK, hK⟩ := h D.relations
    (@NegativeTwistCover.ProjectiveNegativeTwistCover.relations_quasicoherent R _ n I M D ‹M.IsQuasicoherent›)
    (@NegativeTwistCover.ProjectiveNegativeTwistCover.relations_finiteType R _ n I M _ D ‹M.IsQuasicoherent›)
  obtain ⟨BP, hP⟩ := D.source_tensorCech_eventually_vanish
  refine ⟨max BK BP, fun d hd j hj ↦ ?_⟩
  let L := ProjectiveTwisting.Bundle.projectiveTwistingBundle I d
  let S := (D.relationSequence.map (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence L).functor).map
    (CoefficientCechFunctor.projectiveCoefficientCechFunctor I)
  have hS : S.ShortExact := D.twistedRelationCech_shortExact L
  have h₁ : IsZero (S.X₁.homology (j + 2)) :=
    hK d ((le_max_left BK BP).trans hd) (j + 1) (Nat.succ_le_succ hj)
  have h₂ : IsZero (S.X₂.homology (j + 1)) := hP d ((le_max_right BK BP).trans hd) j
  exact VanishingHomologyExactSequences.shortExact_homology_X3_isZero hS (j + 1) (j + 2)
    (by change j + 1 + 1 = j + 2; omega) h₂ h₁

theorem projectiveCoherentCech_eventually_vanish
    (M : (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient I).Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d → ∀ q : ℕ,
      IsZero ((TwistedCech.projectiveTwistedCech I M d).homology (q + 1)) := by
  rename_i hMq hMt
  change (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules at M
  dsimp only [HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient] at *
  let : M.IsQuasicoherent := hMq
  let : M.IsFiniteType := hMt
  have h : ∀ K : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules, K.IsQuasicoherent → K.IsFiniteType →
      ∃ B : ℕ, ∀ d : ℕ, B ≤ d → ∀ j : ℕ, 0 ≤ j →
        IsZero ((TwistedCech.projectiveTwistedCech I K d).homology (j + 1)) := by
    apply Nat.decreasingInduction (n := n)
      (motive := fun q _ ↦ ∀ K : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules,
        K.IsQuasicoherent → K.IsFiniteType → ∃ B : ℕ, ∀ d : ℕ, B ≤ d →
          ∀ j : ℕ, q ≤ j → IsZero ((TwistedCech.projectiveTwistedCech I K d).homology (j + 1)))
      (of_succ := ?_) (self := ?_) (Nat.zero_le n)
    · intro q _ hq K hKq hKt
      exact @projectiveSerreCech_descending_step R _ _ n I q hq K hKq hKt
    · intro K _ _
      refine ⟨0, fun d _ j hj ↦ ?_⟩
      exact CechHomologyBound.projectiveCech_homology_isZero I
        ((LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d)).functor.obj K)
        (j + 1) (Nat.succ_le_succ hj)
  obtain ⟨B, hB⟩ := h M inferInstance inferInstance
  exact ⟨B, fun d hd q ↦ hB d hd q (Nat.zero_le q)⟩

theorem projectiveCoherentTensorCech_eventually_vanish
    (M : (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient I).Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d → ∀ q : ℕ,
      IsZero (((CoefficientCechFunctor.projectiveCoefficientCechFunctor I).obj
        (Tensor.ProductSheaf.tensorModule M (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf)).homology (q + 1)) := by
  rename_i hMq hMt
  change (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules at M
  dsimp only [HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient] at *
  let : M.IsQuasicoherent := hMq
  let : M.IsFiniteType := hMt
  obtain ⟨B, hB⟩ :=
    @projectiveCoherentCech_eventually_vanish R _ _ n I M hMq hMt
  refine ⟨B, fun d hd q ↦ ?_⟩
  exact (hB d hd q).of_iso
    (((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) (q + 1)).mapIso
      (TwistedCech.projectiveTwistedCechActualIso I M d)).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SerreCechVanishing
