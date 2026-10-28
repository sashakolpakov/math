import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Sets.Compacts

/-! # Compact Ball Exhaustion -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CompactBallExhaustion

noncomputable section

/-!
# A cofinal exhaustion by closed balls

The closed balls of radii `n + 1` form an actual compact exhaustion of a
finite-dimensional real normed space. The associated functor from the ordered
natural numbers to its compact subsets is final, so it may index the usual
compact-support colimit without changing that colimit.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The `n`th actual compact support is the closed ball of radius `n + 1`. -/
def compactBallSupport (n : ℕ) : Compacts E :=
  ⟨Metric.closedBall 0 ((n : ℝ) + 1), isCompact_closedBall _ _⟩

@[simp]
theorem coe_compactBallSupport (n : ℕ) :
    (compactBallSupport E n : Set E) = Metric.closedBall 0 ((n : ℝ) + 1) := rfl

/-- Increasing the natural-number index enlarges the compact support. -/
theorem compactBallSupport_mono : Monotone (compactBallSupport E) := by
  intro m n hmn
  exact Metric.closedBall_subset_closedBall
    (add_le_add (Nat.cast_le.mpr hmn) (le_refl (1 : ℝ)))

/-- Each support lies in the interior of the next one. -/
theorem compactBallSupport_subset_interior_succ (n : ℕ) :
    (compactBallSupport E n : Set E) ⊆ interior (compactBallSupport E (n + 1) : Set E) := by
  apply Set.Subset.trans (Metric.closedBall_subset_ball ?_)
    Metric.ball_subset_interior_closedBall
  simp only [Nat.cast_add, Nat.cast_one]
  exact lt_add_one _

/-- The closed balls of increasing integer radius cover the whole space. -/
theorem iUnion_compactBallSupport :
    (⋃ n, (compactBallSupport E n : Set E)) = Set.univ := by
  apply Set.iUnion_eq_univ_iff.mpr
  intro x
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  refine ⟨n, ?_⟩
  change dist x 0 ≤ (n : ℝ) + 1
  rw [dist_zero_right]
  exact hn.le.trans (le_add_of_nonneg_right zero_le_one)

/-- The explicit closed-ball sequence as mathlib's genuine compact exhaustion. -/
def compactBallExhaustion : CompactExhaustion E where
  toFun n := compactBallSupport E n
  isCompact' n := (compactBallSupport E n).isCompact
  subset_interior_succ' := compactBallSupport_subset_interior_succ E
  iUnion_eq' := iUnion_compactBallSupport E

@[simp]
theorem compactBallExhaustion_apply (n : ℕ) :
    compactBallExhaustion E n = Metric.closedBall 0 ((n : ℝ) + 1) := rfl

/-- Every compact set is contained in a member of the explicit ball sequence. -/
theorem exists_le_compactBallSupport (K : Compacts E) :
    ∃ n, K ≤ compactBallSupport E n :=
  (compactBallExhaustion E).exists_superset_of_isCompact K.isCompact

/-- The functor of actual closed-ball inclusions into the ordered compact subsets. -/
def compactBallExhaustionFunctor : ℕ ⥤ Compacts E :=
  (compactBallSupport_mono E).functor

@[simp]
theorem compactBallExhaustionFunctor_obj (n : ℕ) :
    (compactBallExhaustionFunctor E).obj n = compactBallSupport E n := rfl

@[simp]
theorem compactBallExhaustionFunctor_map {m n : ℕ} (hmn : m ≤ n) :
    (compactBallExhaustionFunctor E).map (homOfLE hmn) =
      homOfLE (compactBallSupport_mono E hmn) := rfl

/-- Closed integer-radius balls are categorically cofinal among all compact supports. -/
instance compactBallExhaustionFunctor_final : (compactBallExhaustionFunctor E).Final :=
  (Monotone.final_functor_iff (compactBallSupport_mono E)).mpr
    (exists_le_compactBallSupport E)

end

end OAI.AlgebraicTopology.Duality.Poincare.CompactBallExhaustion
