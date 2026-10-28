import OAI.AlgebraicTopology.Cohomology.Singular.ChartBalls
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Compactness.Compact

/-! # Compact Chart Cover -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.CompactChartCover.Cycles

noncomputable section

/-!
# Finite compact refinements by genuine coordinate balls

Closed model balls lying in actual chart targets pull back to compact
neighborhoods. Every compact subset therefore has a finite compact refinement
by such neighborhoods, with a larger closed coordinate ball still contained
in each chart target. No homology or fundamental-class input is assumed.
-/

open Set Filter
open scoped _root_.Topology

variable (E : Type) [NormedAddCommGroup E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]

/-- The portion of a chart source with coordinates in the stated closed ball. -/
def chartClosedBallDomain (x : M) (r : ℝ) : Set M :=
  (chartAt E x).source ∩ (chartAt E x) ⁻¹' Metric.closedBall (chartAt E x x) r

@[simp]
theorem mem_chartClosedBallDomain (x y : M) (r : ℝ) :
    y ∈ chartClosedBallDomain E x r ↔
      y ∈ (chartAt E x).source ∧
        chartAt E x y ∈ Metric.closedBall (chartAt E x x) r := Iff.rfl

theorem chartClosedBallDomain_subset_source (x : M) (r : ℝ) :
    chartClosedBallDomain E x r ⊆ (chartAt E x).source := inter_subset_left

theorem chart_image_chartClosedBallDomain_subset (x : M) (r : ℝ) :
    chartAt E x '' chartClosedBallDomain E x r ⊆
      Metric.closedBall (chartAt E x x) r := by
  rintro y ⟨z, hz, rfl⟩
  exact hz.2

/-- When the closed ball lies in the chart target, its inverse-chart image
is precisely this coordinate neighborhood. -/
theorem chartClosedBallDomain_eq_image (x : M) (r : ℝ)
    (htarget : Metric.closedBall (chartAt E x x) r ⊆ (chartAt E x).target) :
    chartClosedBallDomain E x r =
      (chartAt E x).symm '' Metric.closedBall (chartAt E x x) r :=
  ((chartAt E x).symm_image_eq_source_inter_preimage htarget).symm

theorem chart_image_chartClosedBallDomain (x : M) (r : ℝ)
    (htarget : Metric.closedBall (chartAt E x x) r ⊆ (chartAt E x).target) :
    chartAt E x '' chartClosedBallDomain E x r =
      Metric.closedBall (chartAt E x x) r := by
  rw [chartClosedBallDomain_eq_image E x r htarget]
  exact (chartAt E x).image_symm_image_of_subset_target htarget

/-- Restriction of the actual chart identifies this compact coordinate
neighborhood with its model closed ball. -/
def chartClosedBallHomeomorph (x : M) (r : ℝ)
    (htarget : Metric.closedBall (chartAt E x x) r ⊆ (chartAt E x).target) :
    chartClosedBallDomain E x r ≃ₜ Metric.closedBall (chartAt E x x) r :=
  (chartAt E x).homeomorphOfImageSubsetSource
    (chartClosedBallDomain_subset_source E x r)
    (chart_image_chartClosedBallDomain E x r htarget)

@[simp]
theorem chartClosedBallHomeomorph_apply (x : M) (r : ℝ)
    (htarget : Metric.closedBall (chartAt E x x) r ⊆ (chartAt E x).target)
    (y : chartClosedBallDomain E x r) :
    (chartClosedBallHomeomorph E x r htarget y : E) = chartAt E x y := rfl

/-- The open coordinate ball lies inside the corresponding closed one. -/
theorem chartBallDomain_subset_closed (x : M) (r : ℝ) :
    AlgebraicTopology.Cohomology.Singular.ChartBalls.chartBallDomain E x r ⊆ chartClosedBallDomain E x r := by
  intro y hy
  exact ⟨hy.1, Metric.ball_subset_closedBall hy.2⟩

theorem chartClosedBallDomain_mem_nhds (x : M) {r : ℝ} (hr : 0 < r) :
    chartClosedBallDomain E x r ∈ 𝓝 x :=
  mem_of_superset (AlgebraicTopology.Cohomology.Singular.ChartBalls.chartBallDomain_mem_nhds E x hr)
    (chartBallDomain_subset_closed E x r)

/-- Every chart center has a positive radius with a larger closed ball
still entirely in the actual chart target. -/
theorem exists_chart_closedBall_radius (x : M) :
    ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (chartAt E x x) (2 * r) ⊆ (chartAt E x).target := by
  obtain ⟨R, hR, htarget⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.mp (chart_target_mem_nhds E x)
  refine ⟨R / 2, by positivity, ?_⟩
  have hradius : 2 * (R / 2) = R := by ring
  simpa only [hradius] using htarget

/-- A compact set is covered by finitely many positive-radius open chart
balls, centered in that compact set, with a larger closed-ball buffer. -/
theorem exists_finite_buffered_chartBall_cover {K : Set M} (hK : IsCompact K) :
    ∃ (centers : Finset M) (radius : M → ℝ),
      (∀ x ∈ centers, x ∈ K) ∧
      (∀ x ∈ centers, 0 < radius x ∧
        Metric.closedBall (chartAt E x x) (2 * radius x) ⊆ (chartAt E x).target) ∧
      K ⊆ ⋃ x ∈ centers, AlgebraicTopology.Cohomology.Singular.ChartBalls.chartBallDomain E x (radius x) := by
  classical
  choose radius hpos htarget using exists_chart_closedBall_radius E (M := M)
  obtain ⟨centers, hcenters, hcover⟩ := hK.elim_nhds_subcover_nhdsSet
    (U := fun x => AlgebraicTopology.Cohomology.Singular.ChartBalls.chartBallDomain E x (radius x))
    (fun x _ => AlgebraicTopology.Cohomology.Singular.ChartBalls.chartBallDomain_mem_nhds E x (hpos x))
  exact ⟨centers, radius, hcenters, fun x _ => ⟨hpos x, htarget x⟩,
    subset_of_mem_nhdsSet hcover⟩

section ProperModel

variable [ProperSpace E]

/-- Closed coordinate balls lying in chart targets are genuinely compact,
by continuity of the inverse chart on the compact model closed ball. -/
theorem isCompact_chartClosedBallDomain (x : M) (r : ℝ)
    (htarget : Metric.closedBall (chartAt E x x) r ⊆ (chartAt E x).target) :
    IsCompact (chartClosedBallDomain E x r) := by
  rw [chartClosedBallDomain_eq_image E x r htarget]
  exact (isCompact_closedBall (chartAt E x x) r).image_of_continuousOn
    ((chartAt E x).continuousOn_symm.mono htarget)

/-- The closure of the smaller open coordinate ball stays in the compact
closed coordinate ball and hence in the chart source. -/
theorem closure_chartBallDomain_subset [T2Space M] (x : M) (r : ℝ)
    (htarget : Metric.closedBall (chartAt E x x) r ⊆ (chartAt E x).target) :
    closure (AlgebraicTopology.Cohomology.Singular.ChartBalls.chartBallDomain E x r) ⊆ chartClosedBallDomain E x r :=
  closure_minimal (chartBallDomain_subset_closed E x r)
    (isCompact_chartClosedBallDomain E x r htarget).isClosed

end ProperModel

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E] [T2Space M]

/-- Every compact set has a finite compact refinement subordinate to actual
coordinate closed balls with positive radius and a larger chart-contained
closed-ball buffer. The pieces are constructed as intersections with `K`. -/
theorem exists_compact_chart_decomposition {K : Set M} (hK : IsCompact K) :
    ∃ (centers : Finset M) (radius : M → ℝ) (pieces : M → Set M),
      K = ⋃ x ∈ centers, pieces x ∧
      (∀ x ∈ centers,
        x ∈ pieces x ∧ IsCompact (pieces x) ∧ pieces x ⊆ K ∧
        pieces x ⊆ chartClosedBallDomain E x (radius x) ∧
        0 < radius x ∧
        Metric.closedBall (chartAt E x x) (2 * radius x) ⊆ (chartAt E x).target) := by
  obtain ⟨centers, radius, hcenters, hradius, hcover⟩ :=
    exists_finite_buffered_chartBall_cover E hK
  refine ⟨centers, radius, fun x => K ∩ chartClosedBallDomain E x (radius x), ?_, ?_⟩
  · apply Subset.antisymm
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := mem_iUnion₂.mp (hcover hy)
      exact mem_iUnion₂.mpr ⟨x, hx, hy, chartBallDomain_subset_closed E x (radius x) hxy⟩
    · intro y hy
      obtain ⟨x, _, hxy⟩ := mem_iUnion₂.mp hy
      exact hxy.1
  · intro x hx
    have hinner : Metric.closedBall (chartAt E x x) (radius x) ⊆ (chartAt E x).target :=
      (Metric.closedBall_subset_closedBall (by linarith [(hradius x hx).1])).trans
        (hradius x hx).2
    refine ⟨⟨hcenters x hx, ?_⟩,
      hK.inter (isCompact_chartClosedBallDomain E x (radius x) hinner),
      inter_subset_left, inter_subset_right, (hradius x hx).1, (hradius x hx).2⟩
    exact chartBallDomain_subset_closed E x (radius x)
      (AlgebraicTopology.Cohomology.Singular.ChartBalls.mem_chartBallDomain_self E x (hradius x hx).1)

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.CompactChartCover.Cycles
