import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.PointApproximation
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.Integral

/-! # Divisor Point Moving -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.DivisorPointMoving

noncomputable section

/-! On an integral smooth projective scheme of any dimension, any divisor cycle can be
moved away from finitely many selected points by actual rational equivalence. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
  [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]

include m

theorem move_single (S : Finset X.carrier) (A : X.DimensionCycleSupport 1) :
    ∃ b : X.RationalDimensionCycle 1, CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 1 (Finsupp.single A 1) b ∧
      ∀ B ∈ b.support, ∀ C ∈ S, C ∉ (B.val : Set X.carrier) := by
  obtain ⟨g, hg, he⟩ := Divisor.PointApproximation.exists_equation X m S A
  let d := Principal.Integral.Cycle.cycle X g
  refine ⟨Finsupp.single A 1 - d, ?_, ?_⟩
  · change Finsupp.single A 1 - (Finsupp.single A 1 - d) ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 1
    rw [sub_sub_cancel]
    exact Submodule.subset_span (Principal.Integral.Cycle.isPrincipal X m g hg)
  · intro B hB C hC hCB
    apply (Finsupp.mem_support_iff.mp hB)
    change (Finsupp.single A 1 : X.RationalDimensionCycle 1) B - d B = 0
    rw [Principal.Integral.Cycle.cycle_apply, he C hC B hCB]
    by_cases hBA : B = A
    · subst B
      simp
    · simp [hBA]

theorem move (S : Finset X.carrier) (a : X.RationalDimensionCycle 1) :
    ∃ b : X.RationalDimensionCycle 1, CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 1 a b ∧
      ∀ B ∈ b.support, ∀ C ∈ S, C ∉ (B.val : Set X.carrier) := by
  induction a using Finsupp.induction_linear with
  | zero =>
    refine ⟨0, CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X 1 0, ?_⟩
    intro B hB
    simp at hB
  | add a b ha hb =>
    obtain ⟨a', ha', hsa⟩ := ha
    obtain ⟨b', hb', hsb⟩ := hb
    refine ⟨a' + b', ?_, ?_⟩
    · change (a + b) - (a' + b') ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 1
      have he : (a + b) - (a' + b') = (a - a') + (b - b') := by abel
      rw [he]
      exact Submodule.add_mem _ ha' hb'
    · intro B hB C hC
      rcases Finset.mem_union.mp (Finsupp.support_add hB) with hB | hB
      · exact hsa B hB C hC
      · exact hsb B hB C hC
  | single A r =>
    obtain ⟨b, hb, hs⟩ := move_single X m S A
    refine ⟨r • b, ?_, fun B hB C hC => hs B (Finsupp.support_smul hB) C hC⟩
    change Finsupp.single A r - r • b ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 1
    have hr : Finsupp.single A r = r • Finsupp.single A (1 : ℚ) := by simp
    rw [hr, ← smul_sub]
    exact Submodule.smul_mem _ r hb

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.DivisorPointMoving
