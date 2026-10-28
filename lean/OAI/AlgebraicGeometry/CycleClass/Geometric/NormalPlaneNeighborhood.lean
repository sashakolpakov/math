import Mathlib.Topology.OpenPartialHomeomorph.Continuity

/-! # Normal Plane Neighborhood -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.NormalPlaneNeighborhood.Cycles

/-!
# Normal-plane preservation near the origin of an open chart

The horizontal inclusion `x ↦ (x, 0)` is continuous. Hence an open chart
containing the origin contains this inclusion near the origin, and actual
preservation of the zero normal coordinate gives the corresponding eventual
equality. The same argument applies to the inverse chart. No differentiability
or linear structure is needed for this topological step.
-/

open Filter _root_.Topology

universe uE uF

variable {E : Type uE} [TopologicalSpace E] [Zero E]
variable {F : Type uF} [TopologicalSpace F] [Zero F]

/-- A neighborhood of the product origin contains horizontal points near the
origin of the first factor. -/
theorem normalPlane_eventually_mem {U : Set (E × F)} (hU : IsOpen U)
    (h0 : ((0 : E), (0 : F)) ∈ U) :
    ∀ᶠ x : E in 𝓝 0, (x, (0 : F)) ∈ U := by
  have h : Continuous (fun x : E => (x, (0 : F))) :=
    continuous_id.prodMk continuous_const
  exact h.continuousAt.eventually (hU.eventually_mem h0)

theorem normalPlane_eventually_mem_source (e : OpenPartialHomeomorph (E × F) (E × F))
    (h0 : ((0 : E), (0 : F)) ∈ e.source) :
    ∀ᶠ x : E in 𝓝 0, (x, (0 : F)) ∈ e.source :=
  normalPlane_eventually_mem e.open_source h0

/-- Actual preservation on the chart source implies preservation on the
horizontal slice near the origin. -/
theorem normalPlane_eventually_map_snd_eq_zero
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (h0 : ((0 : E), (0 : F)) ∈ e.source)
    (hpres : ∀ z ∈ e.source, z.2 = 0 → (e z).2 = 0) :
    ∀ᶠ x : E in 𝓝 0, (e (x, (0 : F))).2 = 0 :=
  (normalPlane_eventually_mem_source e h0).mono fun x hx => hpres (x, 0) hx rfl

/-- A chart carrying the origin to the origin has the origin in its target. -/
theorem normalPlane_zero_mem_target (e : OpenPartialHomeomorph (E × F) (E × F))
    (h0 : ((0 : E), (0 : F)) ∈ e.source)
    (he0 : e (0, 0) = (0, 0)) :
    ((0 : E), (0 : F)) ∈ e.target :=
  he0 ▸ e.map_source h0

/-- The actual partial inverse of an origin-fixing chart fixes the origin. -/
theorem normalPlane_symm_apply_zero (e : OpenPartialHomeomorph (E × F) (E × F))
    (h0 : ((0 : E), (0 : F)) ∈ e.source)
    (he0 : e (0, 0) = (0, 0)) :
    e.symm (0, 0) = (0, 0) := by
  simpa only [he0] using e.left_inv h0

/-- Actual preservation by the inverse on the chart target implies the
eventual zero-normal equality for the inverse horizontal slice. -/
theorem normalPlane_eventually_symm_snd_eq_zero
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (h0 : ((0 : E), (0 : F)) ∈ e.source)
    (he0 : e (0, 0) = (0, 0))
    (hpresInv : ∀ z ∈ e.target, z.2 = 0 → (e.symm z).2 = 0) :
    ∀ᶠ x : E in 𝓝 0, (e.symm (x, (0 : F))).2 = 0 :=
  normalPlane_eventually_map_snd_eq_zero e.symm
    (normalPlane_zero_mem_target e h0 he0) hpresInv

/-- Exact preservation of the normal-zero set on the source also proves
preservation by the actual inverse, so no independent inverse assumption is
needed in this formulation. -/
theorem normalPlane_eventually_symm_snd_eq_zero_of_iff
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (h0 : ((0 : E), (0 : F)) ∈ e.source)
    (he0 : e (0, 0) = (0, 0))
    (hpres : ∀ z ∈ e.source, (e z).2 = 0 ↔ z.2 = 0) :
    ∀ᶠ x : E in 𝓝 0, (e.symm (x, (0 : F))).2 = 0 := by
  apply normalPlane_eventually_symm_snd_eq_zero e h0 he0
  intro z hz hz0
  apply (hpres (e.symm z) (e.map_target hz)).mp
  rw [e.right_inv hz]
  exact hz0

end OAI.AlgebraicGeometry.CycleClass.Geometric.NormalPlaneNeighborhood.Cycles
