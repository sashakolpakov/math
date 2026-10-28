import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Compactness.Compact

/-! # Compact Convex Neighborhood -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.CompactConvexNeighborhood.Cycles

noncomputable section

/-!
# Finite compact convex neighborhoods inside an open set

A compact subset of an open set in a finite-dimensional real normed space
has a neighborhood which is a finite union of genuine closed balls, all
contained in the open set. Compactness is used on neighborhoods, so the
conclusion places the compact set in the interior of the union.
-/

open Set Filter
open scoped _root_.Topology

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A compact set inside an open set has a neighborhood which is a finite
union of compact convex closed balls contained in that open set. The ball
centers lie in the original compact set and all radii are positive. -/
theorem exists_finite_closedBall_neighborhood {K W : Set E}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ (centers : Finset E) (radius : E → ℝ),
      (∀ x ∈ centers,
        x ∈ K ∧ 0 < radius x ∧
        IsCompact (Metric.closedBall x (radius x)) ∧
        Convex ℝ (Metric.closedBall x (radius x)) ∧
        Metric.closedBall x (radius x) ⊆ W) ∧
      K ⊆ interior (⋃ x ∈ centers, Metric.closedBall x (radius x)) ∧
      (⋃ x ∈ centers, Metric.closedBall x (radius x)) ⊆ W ∧
      IsCompact (⋃ x ∈ centers, Metric.closedBall x (radius x)) := by
  classical
  choose! radius hpos hsub using fun x (hx : x ∈ K) =>
    Metric.nhds_basis_closedBall.mem_iff.mp (hW.mem_nhds (hKW hx))
  obtain ⟨centers, hcenters, hcover⟩ := hK.elim_nhds_subcover_nhdsSet
    (U := fun x => Metric.closedBall x (radius x))
    (fun x hx => Metric.closedBall_mem_nhds x (hpos x hx))
  refine ⟨centers, radius, ?_, subset_interior_iff_mem_nhdsSet.mpr hcover, ?_, ?_⟩
  · intro x hx
    exact ⟨hcenters x hx, hpos x (hcenters x hx), isCompact_closedBall x (radius x),
      convex_closedBall x (radius x), hsub x (hcenters x hx)⟩
  · exact iUnion₂_subset fun x hx => hsub x (hcenters x hx)
  · exact centers.isCompact_biUnion fun x _ => isCompact_closedBall x (radius x)

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.CompactConvexNeighborhood.Cycles
