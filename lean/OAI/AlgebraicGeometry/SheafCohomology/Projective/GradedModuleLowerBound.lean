import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedPieceFiniteness
import Mathlib.Data.Fintype.Order

/-! # Graded Module Lower Bound -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedModuleLowerBound

noncomputable section

/-! Finite graded polynomial modules vanish in all sufficiently negative degrees. -/

open DirectSum
universe u v
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ]

theorem weightedFreeGrading_eq_bot_of_lt {ι : Type v} (w : ι → ℤ)
    (d : ℤ) (hd : ∀ i, d < w i) : HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading (σ := σ) R w d = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  change x = 0
  apply Finsupp.ext
  intro i
  have hi := (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.mem_weightedFreeGrading R w d x).mp hx i
  rw [GradedPieceFiniteness.polynomialIntegerGrading_eq_bot_of_neg R (d - w i) (by have := hd i; omega)] at hi
  exact hi

theorem finiteGradedPolynomialModule_boundedBelow
    (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ R) :
    ∃ b : ℤ, ∀ d : ℤ, d < b → D.grading d = ⊥ := by
  obtain ⟨b, hb⟩ := Finite.bddBelow_range D.cover.degree
  refine ⟨b, fun d hd => ?_⟩
  have hfree : D.freeModule.grading d = ⊥ :=
    weightedFreeGrading_eq_bot_of_lt D.cover.degree d
      (fun i => hd.trans_le (hb (Set.mem_range_self i)))
  apply eq_bot_iff.mpr
  intro x hx
  change x = 0
  obtain ⟨y, hy⟩ := D.projection_surjective x
  have hpre := HilbertScheme.Presentations.Graded.Exactness.GradedModules.homogeneous_preimage D.freeModule.grading D.grading
    (D.projection.restrictScalars R) D.projection_homogeneous d x hx y hy
  have hzero : (decompose D.freeModule.grading y d).val = 0 := by
    exact hfree.le (decompose D.freeModule.grading y d).property
  rw [hzero, map_zero] at hpre
  exact hpre.symm

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedModuleLowerBound
