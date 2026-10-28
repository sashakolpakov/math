import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.Bundle
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! # Metric Weight -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.MetricWeight

noncomputable section

section

/-! A finite smooth partition subordinate to the actual holomorphic line-bundle frames. -/

open _root_.CategoryTheory _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [CompactSpace M]
  (u : Holomorphic.Connecting.holomorphicUnitCohomology E M)

theorem exists_holomorphicLineFiniteCover : ∃ s : Finset M,
    ∀ x : M, ∃ i : s, x ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i.val := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun i => (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i : Set M))
    (fun i => (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i).isOpen) (by
      intro x _
      exact mem_iUnion.mpr ⟨x, (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x⟩)
  refine ⟨s, ?_⟩
  intro x
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  exact ⟨⟨i, hi⟩, hxi⟩

def holomorphicLineFiniteCover : Finset M := (exists_holomorphicLineFiniteCover u).choose

theorem holomorphicLineFiniteCover_covers (x : M) :
    ∃ i : holomorphicLineFiniteCover u, x ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i.val :=
  (exists_holomorphicLineFiniteCover u).choose_spec x

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

theorem exists_holomorphicLineSmoothPartition :
    ∃ p : SmoothPartitionOfUnity (holomorphicLineFiniteCover u) 𝓘(ℝ, E) M,
      p.IsSubordinate (fun i => (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i.val : Set M)) := by
  apply SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E) isClosed_univ
    (fun i : holomorphicLineFiniteCover u => (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i.val : Set M))
    (fun i => (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i.val).isOpen)
  intro x _
  exact mem_iUnion.mpr (holomorphicLineFiniteCover_covers u x)

def holomorphicLineSmoothPartition :
    SmoothPartitionOfUnity (holomorphicLineFiniteCover u) 𝓘(ℝ, E) M :=
  (exists_holomorphicLineSmoothPartition u).choose

theorem holomorphicLineSmoothPartition_support (i : holomorphicLineFiniteCover u) :
    tsupport (holomorphicLineSmoothPartition u i) ⊆ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i.val :=
  (exists_holomorphicLineSmoothPartition u).choose_spec i

theorem holomorphicLineSmoothPartition_nonneg (i : holomorphicLineFiniteCover u) (x : M) :
    0 ≤ holomorphicLineSmoothPartition u i x :=
  (holomorphicLineSmoothPartition u).nonneg i x

theorem holomorphicLineSmoothPartition_sum (x : M) :
    ∑ i, holomorphicLineSmoothPartition u i x = 1 := by
  simpa only [finsum_eq_sum_of_fintype] using (holomorphicLineSmoothPartition u).sum_eq_one (mem_univ x)

end

/-! Positive Hermitian metric coefficients from the actual frame cocycle and smooth partition. -/

open _root_.CategoryTheory _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] (u : Holomorphic.Connecting.holomorphicUnitCohomology E M)

def holomorphicLineMetricSummand (i : M) (j : holomorphicLineFiniteCover u)
    (x : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) : ℝ := by
  classical
  exact if hj : x.val ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j.val then
    holomorphicLineSmoothPartition u j x.val *
      Complex.normSq ((Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j.val).val ⟨x.val, x.property, hj⟩)
  else 0

def holomorphicLineMetricWeight (i : M) (x : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) : ℝ :=
  ∑ j, holomorphicLineMetricSummand u i j x

theorem holomorphicLineMetricSummand_nonneg (i : M) (j : holomorphicLineFiniteCover u)
    (x : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) : 0 ≤ holomorphicLineMetricSummand u i j x := by
  unfold holomorphicLineMetricSummand
  split_ifs
  · exact mul_nonneg (holomorphicLineSmoothPartition_nonneg u j x.val) (Complex.normSq_nonneg _)
  · exact le_rfl

theorem holomorphicLineMetricWeight_pos (i : M) (x : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) :
    0 < holomorphicLineMetricWeight u i x := by
  obtain ⟨j, hj⟩ := (holomorphicLineSmoothPartition u).exists_pos_of_mem (mem_univ x.val)
  have hxj : x.val ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j.val :=
    holomorphicLineSmoothPartition_support u j (subset_tsupport _ (ne_of_gt hj))
  have hterm : 0 < holomorphicLineMetricSummand u i j x := by
    erw [holomorphicLineMetricSummand, dite_eq_left hxj]
    exact mul_pos hj (Complex.normSq_pos.mpr
      (Holomorphic.SlitLog.holomorphicUnit_value_ne_zero (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j.val) ⟨x.val, x.property, hxj⟩))
  exact hterm.trans_le (Finset.single_le_sum (fun k _ => holomorphicLineMetricSummand_nonneg u i k x)
    (Finset.mem_univ j))

theorem holomorphicLineMetricWeight_transition (i j x : M)
    (hi : x ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) (hj : x ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j) :
    holomorphicLineMetricWeight u i ⟨x, hi⟩ =
      Complex.normSq ((Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val ⟨x, hi, hj⟩) *
        holomorphicLineMetricWeight u j ⟨x, hj⟩ := by
  classical
  unfold holomorphicLineMetricWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : x ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u k.val
  · simp only [holomorphicLineMetricSummand, dite_eq_left hk]
    rw [← Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition_cocycle E M u i j k.val x hi hj hk, Complex.normSq_mul]
    ring
  · simp only [holomorphicLineMetricSummand, dite_eq_right hk, mul_zero]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.MetricWeight
