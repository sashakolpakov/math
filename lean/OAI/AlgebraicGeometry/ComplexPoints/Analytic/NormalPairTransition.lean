import OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! # Normal Pair Transition -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic

noncomputable section

/-!
# Transitions on verified normal-pair neighborhoods

The ambient chart of a normal pair may extend beyond the neighborhood on
which it describes the full image. We first restrict both charts to those
proved neighborhoods. Their transition then preserves the normal zero
locus on its entire actual source, as does its inverse.
-/

open Set
open scoped _root_.Topology _root_.Manifold

variable {M N : Type*} [TopologicalSpace N] {f : M → N} {x : M}
  {E F E' F' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup E'] [NormedAddCommGroup F']
  (P : NormalPairRecenter.ImmersionNormalPair E F f x)

/-- Restrict to precisely the neighborhood where the full-image statement
has been proved. -/
def NormalPairRecenter.ImmersionNormalPair.restrictedChart : OpenPartialHomeomorph N (E × F) :=
  P.ambientChart.restrOpen P.neighborhood P.isOpen_neighborhood

@[simp]
theorem NormalPairRecenter.ImmersionNormalPair.restrictedChart_source : P.restrictedChart.source = P.neighborhood := by
  change P.ambientChart.source ∩ P.neighborhood = P.neighborhood
  exact inter_eq_right.mpr P.neighborhood_subset_source

@[simp]
theorem NormalPairRecenter.ImmersionNormalPair.restrictedChart_target : P.restrictedChart.target =
    Metric.ball (0 : E) P.radius ×ˢ Metric.ball (0 : F) P.radius := by
  rw [← P.restrictedChart.image_source_eq_target, NormalPairRecenter.ImmersionNormalPair.restrictedChart_source]
  exact P.ambientChart.image_symm_image_of_subset_target P.product_subset_target

@[simp]
theorem NormalPairRecenter.ImmersionNormalPair.restrictedChart_apply (y : N) : P.restrictedChart y = P.ambientChart y := rfl

@[simp]
theorem NormalPairRecenter.ImmersionNormalPair.restrictedChart_symm_apply (z : E × F) :
    P.restrictedChart.symm z = P.ambientChart.symm z := rfl

theorem NormalPairRecenter.ImmersionNormalPair.point_mem_restrictedChart_source : f x ∈ P.restrictedChart.source := by
  rw [NormalPairRecenter.ImmersionNormalPair.restrictedChart_source]
  exact P.point_mem_neighborhood

@[simp]
theorem NormalPairRecenter.ImmersionNormalPair.restrictedChart_point : P.restrictedChart (f x) = (0, 0) :=
  P.point_coordinates

@[simp]
theorem NormalPairRecenter.ImmersionNormalPair.ambientChart_symm_zero : P.ambientChart.symm (0, 0) = f x := by
  rw [← P.point_coordinates, P.ambientChart.left_inv P.point_mem_source]

theorem NormalPairRecenter.ImmersionNormalPair.zero_mem_restrictedChart_target : (0, 0) ∈ P.restrictedChart.target := by
  rw [NormalPairRecenter.ImmersionNormalPair.restrictedChart_target]
  exact ⟨Metric.mem_ball_self P.radius_pos, Metric.mem_ball_self P.radius_pos⟩

variable (Q : NormalPairRecenter.ImmersionNormalPair E' F' f x)

/-- The actual coordinate transition on the overlap of the proved normal
neighborhoods. -/
def NormalPairRecenter.ImmersionNormalPair.transition : OpenPartialHomeomorph (E × F) (E' × F') :=
  P.restrictedChart.symm.trans Q.restrictedChart

@[simp]
theorem NormalPairRecenter.ImmersionNormalPair.transition_apply (z : E × F) :
    P.transition Q z = Q.ambientChart (P.ambientChart.symm z) := rfl

@[simp]
theorem NormalPairRecenter.ImmersionNormalPair.transition_symm_apply (z : E' × F') :
    (P.transition Q).symm z = P.ambientChart (Q.ambientChart.symm z) := rfl

/-- Membership in the transition source requires both verified neighborhoods. -/
theorem NormalPairRecenter.ImmersionNormalPair.transition_source : (P.transition Q).source =
    (Metric.ball (0 : E) P.radius ×ˢ Metric.ball (0 : F) P.radius) ∩
      P.ambientChart.symm ⁻¹' Q.neighborhood := by
  rw [NormalPairRecenter.ImmersionNormalPair.transition, OpenPartialHomeomorph.trans_source]
  change P.restrictedChart.target ∩ P.ambientChart.symm ⁻¹' Q.restrictedChart.source = _
  rw [NormalPairRecenter.ImmersionNormalPair.restrictedChart_target, NormalPairRecenter.ImmersionNormalPair.restrictedChart_source]

/-- The source is exactly the first chart's image of the actual overlap. -/
theorem NormalPairRecenter.ImmersionNormalPair.transition_source_image : (P.transition Q).source =
    P.ambientChart '' (P.neighborhood ∩ Q.neighborhood) := by
  rw [NormalPairRecenter.ImmersionNormalPair.transition, OpenPartialHomeomorph.trans_source'']
  change P.restrictedChart '' (P.restrictedChart.source ∩ Q.restrictedChart.source) = _
  rw [NormalPairRecenter.ImmersionNormalPair.restrictedChart_source, NormalPairRecenter.ImmersionNormalPair.restrictedChart_source]
  rfl

/-- The target is exactly the second chart's image of the same overlap. -/
theorem NormalPairRecenter.ImmersionNormalPair.transition_target_image : (P.transition Q).target =
    Q.ambientChart '' (P.neighborhood ∩ Q.neighborhood) := by
  rw [NormalPairRecenter.ImmersionNormalPair.transition, OpenPartialHomeomorph.trans_target'']
  change Q.restrictedChart '' (Q.restrictedChart.source ∩ P.restrictedChart.source) = _
  rw [NormalPairRecenter.ImmersionNormalPair.restrictedChart_source, NormalPairRecenter.ImmersionNormalPair.restrictedChart_source, inter_comm]
  rfl

theorem NormalPairRecenter.ImmersionNormalPair.isOpen_transition_source : IsOpen (P.transition Q).source :=
  (P.transition Q).open_source

theorem NormalPairRecenter.ImmersionNormalPair.isOpen_transition_target : IsOpen (P.transition Q).target :=
  (P.transition Q).open_target

@[simp]
theorem NormalPairRecenter.ImmersionNormalPair.transition_symm : (P.transition Q).symm = Q.transition P := by
  rw [NormalPairRecenter.ImmersionNormalPair.transition, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
  rfl

theorem NormalPairRecenter.ImmersionNormalPair.zero_mem_transition_source : (0, 0) ∈ (P.transition Q).source := by
  rw [NormalPairRecenter.ImmersionNormalPair.transition_source]
  refine ⟨⟨Metric.mem_ball_self P.radius_pos, Metric.mem_ball_self P.radius_pos⟩, ?_⟩
  change P.ambientChart.symm (0, 0) ∈ Q.neighborhood
  rw [NormalPairRecenter.ImmersionNormalPair.ambientChart_symm_zero]
  exact Q.point_mem_neighborhood

@[simp]
theorem NormalPairRecenter.ImmersionNormalPair.transition_zero : P.transition Q (0, 0) = (0, 0) := by
  rw [NormalPairRecenter.ImmersionNormalPair.transition_apply, NormalPairRecenter.ImmersionNormalPair.ambientChart_symm_zero, Q.point_coordinates]

theorem NormalPairRecenter.ImmersionNormalPair.zero_mem_transition_target : (0, 0) ∈ (P.transition Q).target := by
  rw [← P.transition_zero Q]
  exact (P.transition Q).map_source (P.zero_mem_transition_source Q)

/-- The transition preserves the zero normal locus everywhere on its
verified source, because both charts describe the same full image. -/
theorem NormalPairRecenter.ImmersionNormalPair.transition_preserves_zero (z : E × F) (hz : z ∈ (P.transition Q).source) :
    (P.transition Q z).2 = 0 ↔ z.2 = 0 := by
  rw [NormalPairRecenter.ImmersionNormalPair.transition_source] at hz
  have hp : P.ambientChart.symm z ∈ P.neighborhood := ⟨z, hz.1, rfl⟩
  have hP := P.range_iff (P.ambientChart.symm z) hp
  have hQ := Q.range_iff (P.ambientChart.symm z) hz.2
  rw [P.ambientChart.right_inv (P.product_subset_target hz.1)] at hP
  exact hQ.symm.trans hP

theorem NormalPairRecenter.ImmersionNormalPair.transition_preserves_complement (z : E × F) (hz : z ∈ (P.transition Q).source) :
    (P.transition Q z).2 ≠ 0 ↔ z.2 ≠ 0 :=
  not_congr (P.transition_preserves_zero Q z hz)

/-- The inverse transition has the same full zero-locus preservation. -/
theorem NormalPairRecenter.ImmersionNormalPair.transition_symm_preserves_zero (z : E' × F')
    (hz : z ∈ (P.transition Q).target) :
    ((P.transition Q).symm z).2 = 0 ↔ z.2 = 0 := by
  have h := P.transition_preserves_zero Q ((P.transition Q).symm z)
    ((P.transition Q).map_target hz)
  rw [(P.transition Q).right_inv hz] at h
  exact h.symm

theorem NormalPairRecenter.ImmersionNormalPair.transition_symm_preserves_complement (z : E' × F')
    (hz : z ∈ (P.transition Q).target) :
    ((P.transition Q).symm z).2 ≠ 0 ↔ z.2 ≠ 0 :=
  not_congr (P.transition_symm_preserves_zero Q z hz)

/-- The actual zero slices in the overlap are homeomorphic. -/
def NormalPairRecenter.ImmersionNormalPair.transitionSupportHomeomorph :
    {z : (P.transition Q).source // z.val.2 = 0} ≃ₜ
      {z : (P.transition Q).target // z.val.2 = 0} :=
  (P.transition Q).toHomeomorphSourceTarget.subtype
    (fun z => (P.transition_preserves_zero Q z.val z.property).symm)

/-- The actual complements of the zero slices in the overlap are homeomorphic. -/
def NormalPairRecenter.ImmersionNormalPair.transitionComplementHomeomorph :
    {z : (P.transition Q).source // z.val.2 ≠ 0} ≃ₜ
      {z : (P.transition Q).target // z.val.2 ≠ 0} :=
  (P.transition Q).toHomeomorphSourceTarget.subtype
    (fun z => (P.transition_preserves_complement Q z.val z.property).symm)

variable {𝕜 G : Type*} [NontriviallyNormedField 𝕜]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 E'] [NormedSpace 𝕜 F']
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [ChartedSpace G N]

/-- Restricting a differentiable ambient chart to the verified neighborhood
preserves differentiability of both chart directions. -/
theorem NormalPairRecenter.ImmersionNormalPair.restrictedChart_mdifferentiable
    (hP : P.ambientChart.MDifferentiable 𝓘(𝕜, G) 𝓘(𝕜, E × F)) :
    P.restrictedChart.MDifferentiable 𝓘(𝕜, G) 𝓘(𝕜, E × F) := by
  constructor
  · change MDifferentiableOn 𝓘(𝕜, G) 𝓘(𝕜, E × F) P.ambientChart
      (P.ambientChart.source ∩ P.neighborhood)
    exact hP.1.mono inter_subset_left
  · change MDifferentiableOn 𝓘(𝕜, E × F) 𝓘(𝕜, G) P.ambientChart.symm
      (P.ambientChart.target ∩ P.ambientChart.symm ⁻¹' P.neighborhood)
    exact hP.2.mono inter_subset_left

/-- Actual differentiable charts give an actual differentiable transition
on the verified overlap, including a differentiable inverse. -/
theorem NormalPairRecenter.ImmersionNormalPair.transition_mdifferentiable
    (hP : P.ambientChart.MDifferentiable 𝓘(𝕜, G) 𝓘(𝕜, E × F))
    (hQ : Q.ambientChart.MDifferentiable 𝓘(𝕜, G) 𝓘(𝕜, E' × F')) :
    (P.transition Q).MDifferentiable 𝓘(𝕜, E × F) 𝓘(𝕜, E' × F') :=
  (P.restrictedChart_mdifferentiable hP).symm.trans (Q.restrictedChart_mdifferentiable hQ)

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic
