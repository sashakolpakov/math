import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicTopology.Cohomology.Singular.ContinuousFormulas
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.Topology.Compactness.Compact

/-! # Increasing Cover -/

namespace OAI.Topology.Euclidean.IncreasingCover

noncomputable section

/-!
# Compact containment and singular-simplex lifts for increasing open covers

Every compact subset of a space covered by an increasing sequence of open
sets lies in a single member. In particular, finitely many genuine singular
simplices, even in different dimensions, factor through one cover member.
The factors below are actual simplices of that open subspace; their images
under the native singular-set inclusion are the original simplices.
-/

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

open _root_.CategoryTheory Opposite _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.ContinuousFormulas
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Globalization

universe u v w

/-- A compact subset of an increasing open cover lies in a single member. -/
theorem exists_compact_subset_increasing_cover
    {X : Type u} [TopologicalSpace X] (U : ℕ → Set X)
    (hmono : Monotone U) (hopen : ∀ n, IsOpen (U n))
    (hcover : (⋃ n, U n) = Set.univ) {K : Set X} (hK : IsCompact K) :
    ∃ n, K ⊆ U n := by
  apply hK.elim_directed_cover U hopen
  · rw [hcover]
    exact Set.subset_univ K
  · intro i j
    exact ⟨max i j, hmono (le_max_left i j), hmono (le_max_right i j)⟩

/-- Finitely many continuous images of compact spaces fit in one member of
an increasing open cover. The source spaces may depend on the index. -/
theorem exists_finite_ranges_subset_increasing_cover
    {X : Type u} [TopologicalSpace X] (U : ℕ → Set X)
    (hmono : Monotone U) (hopen : ∀ n, IsOpen (U n))
    (hcover : (⋃ n, U n) = Set.univ)
    {ι : Type v} [Finite ι] {Y : ι → Type w}
    [∀ i, TopologicalSpace (Y i)] [∀ i, CompactSpace (Y i)]
    (f : ∀ i, C(Y i, X)) :
    ∃ n, ∀ i, Set.range (f i) ⊆ U n := by
  obtain ⟨n, hn⟩ := exists_compact_subset_increasing_cover U hmono hopen hcover
    (isCompact_iUnion (fun i => isCompact_range (f i).continuous))
  exact ⟨n, fun i => (Set.subset_iUnion (fun j => Set.range (f j)) i).trans hn⟩

/-- The compact-containment result in the lattice of actual open subsets. -/
theorem exists_compact_subset_increasing_openCover
    {X : Type u} [TopologicalSpace X] (U : ℕ → Opens X)
    (hmono : Monotone U) (hcover : (⨆ n, U n) = ⊤)
    {K : Set X} (hK : IsCompact K) :
    ∃ n, K ⊆ U n := by
  apply exists_compact_subset_increasing_cover (fun n => (U n : Set X))
    (fun _ _ h => hmono h) (fun n => (U n).isOpen) _ hK
  have h := congrArg (fun V : Opens X => (V : Set X)) hcover
  simpa only [Opens.coe_iSup, Opens.coe_top] using h

/-- The image of a genuine singular simplex is compact. -/
theorem isCompact_singularSimplex_range {X : TopCat.{0}} {n : ℕ}
    (σ : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices X n) :
    IsCompact (Set.range (AlgebraicTopology.Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n σ)) :=
  isCompact_range (AlgebraicTopology.Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n σ).continuous

/-- A finite family of genuine singular simplices, allowing different
dimensions, has all its images inside one member of an increasing open cover. -/
theorem exists_finite_singularSimplex_ranges_subset {X : TopCat.{0}}
    (U : ℕ → Opens X) (hmono : Monotone U) (hcover : (⨆ n, U n) = ⊤)
    {ι : Type v} [Finite ι] (d : ι → ℕ) (σ : ∀ i, AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices X (d i)) :
    ∃ n, ∀ i, Set.range (AlgebraicTopology.Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X (d i) (σ i)) ⊆ U n := by
  obtain ⟨n, hn⟩ := exists_compact_subset_increasing_openCover U hmono hcover
    (isCompact_iUnion (fun i => isCompact_singularSimplex_range (σ i)))
  exact ⟨n, fun i => (Set.subset_iUnion
    (fun j => Set.range (AlgebraicTopology.Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X (d j) (σ j))) i).trans hn⟩

/-- Finite supports in one singular-chain degree fit in one cover member. -/
theorem exists_finset_singularSimplex_ranges_subset {X : TopCat.{0}}
    (U : ℕ → Opens X) (hmono : Monotone U) (hcover : (⨆ n, U n) = ⊤)
    {d : ℕ} (s : Finset (AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices X d)) :
    ∃ n, ∀ σ ∈ s, Set.range (AlgebraicTopology.Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X d σ) ⊆ U n := by
  obtain ⟨n, hn⟩ := exists_compact_subset_increasing_openCover U hmono hcover
    (s.isCompact_biUnion (fun σ _ => isCompact_singularSimplex_range σ))
  refine ⟨n, fun σ hσ x hx => hn ?_⟩
  exact Set.mem_iUnion.mpr ⟨σ, Set.mem_iUnion.mpr ⟨hσ, hx⟩⟩

/-- Restrict the codomain of an actual singular simplex whose image lies in
an open subset. This is a simplex of that subset with its subspace topology. -/
def singularSimplexLift {X : TopCat.{0}} (U : Opens X) {n : ℕ}
    (σ : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices X n)
    (hσ : Set.range (AlgebraicTopology.Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n σ) ⊆ U) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices (TopCat.of U) n :=
  (AlgebraicTopology.Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap (TopCat.of U) n).symm
    ⟨fun z => ⟨AlgebraicTopology.Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n σ z, hσ (Set.mem_range_self z)⟩,
      (AlgebraicTopology.Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n σ).continuous.subtype_mk _⟩

/-- The lift preserves the pointwise value of the original singular simplex. -/
@[simp]
theorem singularSimplexLift_apply {X : TopCat.{0}} (U : Opens X) {n : ℕ}
    (σ : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices X n)
    (hσ : Set.range (AlgebraicTopology.Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n σ) ⊆ U)
    (z : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    (AlgebraicTopology.Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap (TopCat.of U) n
      (singularSimplexLift U σ hσ) z).val =
        AlgebraicTopology.Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n σ z := by
  simp only [singularSimplexLift, Equiv.apply_symm_apply]
  rfl

/-- The native singular-set inclusion carries the lifted simplex back to
the original simplex, as an equality in the genuine simplicial set. -/
@[simp]
theorem map_singularSimplexLift {X : TopCat.{0}} (U : Opens X) {n : ℕ}
    (σ : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices X n)
    (hσ : Set.range (AlgebraicTopology.Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n σ) ⊆ U) :
    (TopCat.toSSet.map U.inclusion').app (op ⦋n⦌) (singularSimplexLift U σ hσ) = σ := by
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n).injective
  rw [AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.singularSimplicesEquivContinuousMap_map]
  ext z
  exact singularSimplexLift_apply U σ hσ z

/-- A lift through an actual open-subspace inclusion is unique. -/
theorem singularSimplexLift_unique {X : TopCat.{0}} (U : Opens X) {n : ℕ}
    (σ : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices X n)
    (hσ : Set.range (AlgebraicTopology.Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n σ) ⊆ U)
    (τ : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices (TopCat.of U) n)
    (hτ : (TopCat.toSSet.map U.inclusion').app (op ⦋n⦌) τ = σ) :
    τ = singularSimplexLift U σ hσ := by
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap (TopCat.of U) n).injective
  ext z
  have hz := congrArg (fun t : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices X n =>
    AlgebraicTopology.Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n t z) hτ
  rw [AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.singularSimplicesEquivContinuousMap_map] at hz
  exact hz.trans (singularSimplexLift_apply U σ hσ z).symm

/-- Every genuine singular simplex factors through one member of an
increasing open cover. -/
theorem exists_singularSimplex_lift {X : TopCat.{0}}
    (U : ℕ → Opens X) (hmono : Monotone U) (hcover : (⨆ n, U n) = ⊤)
    {d : ℕ} (σ : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices X d) :
    ∃ n, ∃ τ : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices (TopCat.of (U n)) d,
      (TopCat.toSSet.map (U n).inclusion').app (op ⦋d⦌) τ = σ := by
  obtain ⟨n, hn⟩ := exists_compact_subset_increasing_openCover U hmono hcover
    (isCompact_singularSimplex_range σ)
  exact ⟨n, singularSimplexLift (U n) σ hn, map_singularSimplexLift (U n) σ hn⟩

/-- A finite family of genuine simplices admits simultaneous native lifts
through one member of the increasing open cover. -/
theorem exists_finite_singularSimplex_lifts {X : TopCat.{0}}
    (U : ℕ → Opens X) (hmono : Monotone U) (hcover : (⨆ n, U n) = ⊤)
    {ι : Type v} [Finite ι] (d : ι → ℕ) (σ : ∀ i, AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices X (d i)) :
    ∃ n, ∃ τ : ∀ i, AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices (TopCat.of (U n)) (d i),
      ∀ i, (TopCat.toSSet.map (U n).inclusion').app (op ⦋d i⦌) (τ i) = σ i := by
  obtain ⟨n, hn⟩ := exists_finite_singularSimplex_ranges_subset U hmono hcover d σ
  exact ⟨n, fun i => singularSimplexLift (U n) (σ i) (hn i),
    fun i => map_singularSimplexLift (U n) (σ i) (hn i)⟩

end Globalization

end

end OAI.Topology.Euclidean.IncreasingCover
