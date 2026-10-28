module

public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.Algebra.Monoid.FunOnFinite
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Instances.Real.Lemmas

/-! The finite real standard simplex carries the metric on its barycentric weights. -/

public noncomputable section

namespace Convexity.StdSimplex

/-- The sup metric on barycentric coordinates, preserving the standard simplex topology. -/
instance metricSpace (ι : Type*) [Fintype ι] : MetricSpace (StdSimplex ℝ ι) :=
  (isEmbedding_toFun_comp_weights ℝ ι).comapMetricSpace (fun x => (x.weights : ι → ℝ))

/-- Barycentric coordinates of a real simplex point. -/
scoped instance coeFn (ι : Type*) : CoeFun (StdSimplex ℝ ι) (fun _ => ι → ℝ) :=
  ⟨fun x => x.weights⟩

/-- Construct a finite simplex from nonnegative coordinates summing to one. -/
def ofCoordinates {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (hn : ∀ i, 0 ≤ x i) (ht : ∑ i, x i = 1) : StdSimplex ℝ ι where
  weights := Finsupp.equivFunOnFinite.symm x
  nonneg i := by simpa using hn i
  total := by simpa [Finsupp.sum_fintype] using ht

@[simp]
theorem ofCoordinates_weights {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (hn : ∀ i, 0 ≤ x i) (ht : ∑ i, x i = 1) (i : ι) :
    (ofCoordinates x hn ht).weights i = x i := by simp [ofCoordinates]

/-- Coordinates of a finite simplex after identifying vertices. -/
theorem weights_map_sum {X Y : Type*} [Fintype X] [DecidableEq Y]
    (f : X → Y) (w : StdSimplex ℝ X) (y : Y) :
    (map f w).weights y = ∑ x with f x = y, w.weights x := by
  classical
  simp [map, Finsupp.mapDomain_apply, Finsupp.sum_fintype,
    Finsupp.single_apply, Finset.sum_filter]

/-- Finite barycentric coordinate vectors form a convex set. -/
theorem convex_range_weights (ι : Type*) [Fintype ι] :
    Convex ℝ (Set.range (fun x : StdSimplex ℝ ι => (x.weights : ι → ℝ))) := by
  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩ c d hc hd hcd
  refine ⟨ofCoordinates (c • (u.weights : ι → ℝ) + d • (v.weights : ι → ℝ)) ?_ ?_, ?_⟩
  · intro i
    exact add_nonneg (mul_nonneg hc (u.weights_nonneg i))
      (mul_nonneg hd (v.weights_nonneg i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, total_of_fintype, mul_one, hcd]
  · funext i
    simp

/-- A nonempty finite standard simplex is contractible through its coordinates. -/
instance contractibleSpace (ι : Type*) [Fintype ι] [Nonempty ι] :
    ContractibleSpace (StdSimplex ℝ ι) := by
  classical
  let coord : StdSimplex ℝ ι → ι → ℝ := fun x => x.weights
  let a : StdSimplex ℝ ι := single (Classical.choice ‹Nonempty ι›)
  let : ContractibleSpace (Set.range coord) :=
    (convex_range_weights ι).contractibleSpace ⟨coord a, ⟨a, rfl⟩⟩
  exact (isEmbedding_toFun_comp_weights ℝ ι).toHomeomorph.contractibleSpace

/-- The finite-coordinate linear map agrees with mapping barycentric weights. -/
theorem map_coordinates {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (w : StdSimplex ℝ X) :
    ((map f w).weights : Y → ℝ) = FunOnFinite.linearMap ℝ ℝ f (w.weights : X → ℝ) := by
  simp [map, FunOnFinite.linearMap]
  rfl

/-- Distance is the sup distance between the barycentric coordinate vectors. -/
theorem dist_eq_weights {ι : Type*} [Fintype ι] (x y : StdSimplex ℝ ι) :
    dist x y = dist (x.weights : ι → ℝ) (y.weights : ι → ℝ) := rfl

/-- Recover a simplex from a vector known to be its barycentric coordinates. -/
def ofMemRange {ι : Type*} (x : ι → ℝ)
    (hx : x ∈ Set.range (fun y : StdSimplex ℝ ι => (y.weights : ι → ℝ))) :
    StdSimplex ℝ ι := Classical.choose hx

@[simp]
theorem ofMemRange_weights {ι : Type*} (x : ι → ℝ)
    (hx : x ∈ Set.range (fun y : StdSimplex ℝ ι => (y.weights : ι → ℝ))) :
    ((ofMemRange x hx).weights : ι → ℝ) = x := Classical.choose_spec hx

/-- Finite real simplices inherit local path connectedness from their coordinate range. -/
instance locallyPathConnectedSpace (ι : Type*) [Fintype ι] :
    LocallyPathConnectedSpace (StdSimplex ℝ ι) := by
  let : LocallyPathConnectedSpace
      (Set.range (fun x : StdSimplex ℝ ι => (x.weights : ι → ℝ))) :=
    (convex_range_weights ι).locallyPathConnectedSpace
  exact (isEmbedding_toFun_comp_weights ℝ ι).toHomeomorph.symm.locallyPathConnectedSpace

/-- Barycentric coordinates realize the chosen metric isometrically. -/
theorem isometry_weights (ι : Type*) [Fintype ι] :
    Isometry (fun x : StdSimplex ℝ ι => (x.weights : ι → ℝ)) :=
  Isometry.of_dist_eq fun x y => (dist_eq_weights x y).symm

end Convexity.StdSimplex
