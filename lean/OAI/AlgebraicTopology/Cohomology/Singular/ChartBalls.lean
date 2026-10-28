import OAI.AlgebraicTopology.Cohomology.Singular.Contractible
import Mathlib.Geometry.Manifold.ChartedSpace

/-! # Chart Balls -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ChartBalls

noncomputable section

/-!
# Chart balls and local singular cohomology

For a space charted on a real normed vector space, balls contained in a
chart target pull back to a neighborhood basis. Each such domain is
explicitly homeomorphic to the model ball. Positive-radius chart balls are
therefore contractible and have vanishing positive-degree singular
cohomology. Only the actual charted-space topology is used here; these
results in particular apply to smooth manifolds without boundary.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Filter
open scoped _root_.Topology

variable (E : Type) [NormedAddCommGroup E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]

/-- The part of a chart source whose chart coordinates lie in a ball
centered at the coordinates of the chosen point. -/
def chartBallDomain (x : X) (r : ℝ) : Set X :=
  (chartAt E x).source ∩ (chartAt E x) ⁻¹' Metric.ball (chartAt E x x) r

@[simp]
theorem mem_chartBallDomain (x y : X) (r : ℝ) :
    y ∈ chartBallDomain E x r ↔
      y ∈ (chartAt E x).source ∧ chartAt E x y ∈ Metric.ball (chartAt E x x) r :=
  Iff.rfl

theorem isOpen_chartBallDomain (x : X) (r : ℝ) :
    IsOpen (chartBallDomain E x r) :=
  (chartAt E x).isOpen_inter_preimage Metric.isOpen_ball

/-- A chart ball as an actual open subspace of the original topological
space. This carries the canonical open-submanifold chart structure. -/
def chartBallOpen (x : X) (r : ℝ) : TopologicalSpace.Opens X :=
  ⟨chartBallDomain E x r, isOpen_chartBallDomain E x r⟩

@[simp]
theorem coe_chartBallOpen (x : X) (r : ℝ) :
    (chartBallOpen E x r : Set X) = chartBallDomain E x r :=
  rfl

@[simp]
theorem mem_chartBallOpen (x y : X) (r : ℝ) :
    y ∈ chartBallOpen E x r ↔
      y ∈ (chartAt E x).source ∧ chartAt E x y ∈ Metric.ball (chartAt E x x) r :=
  Iff.rfl

theorem mem_chartBallDomain_self (x : X) {r : ℝ} (hr : 0 < r) :
    x ∈ chartBallDomain E x r :=
  ⟨mem_chart_source E x, Metric.mem_ball_self hr⟩

theorem chartBallDomain_mem_nhds (x : X) {r : ℝ} (hr : 0 < r) :
    chartBallDomain E x r ∈ 𝓝 x :=
  (isOpen_chartBallDomain E x r).mem_nhds (mem_chartBallDomain_self E x hr)

theorem chartBallDomain_mono (x : X) {r s : ℝ} (hrs : r ≤ s) :
    chartBallDomain E x r ⊆ chartBallDomain E x s := by
  intro y hy
  exact ⟨hy.1, Metric.ball_subset_ball hrs hy.2⟩

/-- The chart maps an admissible chart-ball domain onto the entire model
ball, not merely into it. -/
theorem chart_image_chartBallDomain (x : X) (r : ℝ)
    (htarget : Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target) :
    chartAt E x '' chartBallDomain E x r = Metric.ball (chartAt E x x) r := by
  change chartAt E x '' ((chartAt E x).source ∩
    (chartAt E x) ⁻¹' Metric.ball (chartAt E x x) r) = _
  rw [← (chartAt E x).symm_image_eq_source_inter_preimage htarget]
  exact (chartAt E x).image_symm_image_of_subset_target htarget

/-- Restricting the actual chart gives a homeomorphism from an admissible
open chart-ball domain to the corresponding ball in the model space. -/
def chartBallHomeomorph (x : X) (r : ℝ)
    (htarget : Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target) :
    chartBallOpen E x r ≃ₜ Metric.ball (chartAt E x x) r :=
  (chartAt E x).homeomorphOfImageSubsetSource Set.inter_subset_left
    (chart_image_chartBallDomain E x r htarget)

@[simp]
theorem chartBallHomeomorph_coe_apply (x : X) (r : ℝ)
    (htarget : Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target)
    (y : chartBallOpen E x r) :
    (chartBallHomeomorph E x r htarget y : E) = chartAt E x y :=
  rfl

@[simp]
theorem chartBallHomeomorph_symm_coe_apply (x : X) (r : ℝ)
    (htarget : Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target)
    (y : Metric.ball (chartAt E x x) r) :
    ((chartBallHomeomorph E x r htarget).symm y : X) = (chartAt E x).symm y :=
  rfl

/-- Admissible positive-radius chart balls form a basis of the actual
neighborhood filter at the chart center. -/
theorem nhds_basis_chartBall (x : X) :
    (𝓝 x).HasBasis
      (fun r : ℝ => 0 < r ∧ Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target)
      (fun r => chartBallDomain E x r) := by
  rw [← (chartAt E x).symm_map_nhds_eq (mem_chart_source E x)]
  have hb := (Metric.nhds_basis_ball (x := chartAt E x x)).restrict_subset
    (chart_target_mem_nhds E x)
  refine (hb.map (chartAt E x).symm).congr (fun _ => Iff.rfl) ?_
  intro r hr
  exact (chartAt E x).symm_image_eq_source_inter_preimage hr.2

/-- Every neighborhood contains an admissible positive-radius chart ball. -/
theorem exists_chartBall_subset_of_mem_nhds (x : X) {s : Set X} (hs : s ∈ 𝓝 x) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target ∧
      chartBallDomain E x r ⊆ s := by
  obtain ⟨r, ⟨hr, ht⟩, hsub⟩ := (nhds_basis_chartBall E x).mem_iff.mp hs
  exact ⟨r, hr, ht, hsub⟩

variable [NormedSpace ℝ E]

/-- Each admissible positive-radius chart ball is contractible by transport
of the straight-line contraction of its convex model ball. -/
theorem contractibleSpace_chartBall (x : X) (r : ℝ) (hr : 0 < r)
    (htarget : Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target) :
    ContractibleSpace (chartBallOpen E x r) := by
  let : ContractibleSpace (Metric.ball (chartAt E x x) r) :=
    (convex_ball (chartAt E x x) r).contractibleSpace
      ⟨chartAt E x x, Metric.mem_ball_self hr⟩
  exact (chartBallHomeomorph E x r htarget).contractibleSpace

include E in
/-- The chart-ball basis supplies a contractible open neighborhood inside
every prescribed neighborhood. -/
theorem exists_contractible_open_subset_of_mem_nhds (x : X)
    {s : Set X} (hs : s ∈ 𝓝 x) :
    ∃ U : TopologicalSpace.Opens X,
      x ∈ U ∧ (U : Set X) ⊆ s ∧ ContractibleSpace U := by
  obtain ⟨r, hr, ht, hsub⟩ := exists_chartBall_subset_of_mem_nhds E x hs
  exact ⟨chartBallOpen E x r, mem_chartBallDomain_self E x hr, hsub,
    contractibleSpace_chartBall E x r hr ht⟩

variable {R : Type} [Ring R]

/-- Positive-degree singular cohomology vanishes on admissible chart balls. -/
theorem isZero_singularCohomology_chartBall (M : ModuleCat.{0} R)
    (x : X) (r : ℝ) (hr : 0 < r)
    (htarget : Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target)
    (n : ℕ) (hn : n ≠ 0) :
    IsZero (Basic.singularCohomology M (TopCat.of (chartBallOpen E x r)) n) := by
  let := contractibleSpace_chartBall E x r hr htarget
  exact Contractible.isZero_singularCohomology_of_contractible M (TopCat.of (chartBallOpen E x r)) n hn

end

end OAI.AlgebraicTopology.Cohomology.Singular.ChartBalls
