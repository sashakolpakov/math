import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.PartialHomeomorph.Basic

/-! # Finite Chart Cover -/

namespace OAI.Topology.Euclidean.FiniteChartCover.Globalization

noncomputable section

/-!
# Finite chart covers and their intersections

A compact charted space has a finite cover by its actual preferred chart
domains. A finite intersection contained in one of those domains is carried
by that chart to an open subset of the model space. For a smooth manifold,
the restriction is a diffeomorphism with the inherited open-subset structures.
No convexity or contractibility of intersections is asserted.
-/

open Set _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

universe u v

variable (H : Type u) [TopologicalSpace H]
variable {M : Type v} [TopologicalSpace M] [ChartedSpace H M]

/-- The actual intersection of the preferred chart domains indexed by a finite set. -/
def chartIntersection (s : Finset M) : Set M :=
  ⋂ x ∈ s, (chartAt H x).source

@[simp]
theorem mem_chartIntersection (s : Finset M) (y : M) :
    y ∈ chartIntersection H s ↔ ∀ x ∈ s, y ∈ (chartAt H x).source := by
  simp only [chartIntersection, Set.mem_iInter]

theorem isOpen_chartIntersection (s : Finset M) : IsOpen (chartIntersection H s) :=
  isOpen_biInter_finset fun x _ => (chartAt H x).open_source

theorem chartIntersection_subset_source (s : Finset M) {x : M} (hx : x ∈ s) :
    chartIntersection H s ⊆ (chartAt H x).source := by
  intro y hy
  exact (mem_chartIntersection H s y).mp hy x hx

/-- The finite intersection, bundled with its proved openness. -/
def chartIntersectionOpen (s : Finset M) : Opens M :=
  ⟨chartIntersection H s, isOpen_chartIntersection H s⟩

theorem chartIntersection_image_subset_target (s : Finset M) {x : M} (hx : x ∈ s) :
    (chartAt H x) '' chartIntersection H s ⊆ (chartAt H x).target := by
  rintro y ⟨z, hz, rfl⟩
  exact (chartAt H x).map_source (chartIntersection_subset_source H s hx hz)

theorem isOpen_chartIntersection_image (s : Finset M) {x : M} (hx : x ∈ s) :
    IsOpen ((chartAt H x) '' chartIntersection H s) :=
  (chartAt H x).isOpen_image_of_subset_source (isOpen_chartIntersection H s)
    (chartIntersection_subset_source H s hx)

/-- The actual image of a finite chart intersection inside one member's model chart. -/
def chartIntersectionImageOpen (s : Finset M) (x : M) (hx : x ∈ s) : Opens H :=
  ⟨(chartAt H x) '' chartIntersection H s, isOpen_chartIntersection_image H s hx⟩

/-- Restriction of any member chart identifies the intersection with an open model subset. -/
def chartIntersectionHomeomorph (s : Finset M) (x : M) (hx : x ∈ s) :
    chartIntersectionOpen H s ≃ₜ chartIntersectionImageOpen H s x hx :=
  (chartAt H x).toPartialHomeomorph.homeomorphOfImageSubsetSource
    (chartIntersection_subset_source H s hx) rfl

@[simp]
theorem chartIntersectionHomeomorph_apply (s : Finset M) (x : M) (hx : x ∈ s)
    (y : chartIntersectionOpen H s) :
    (chartIntersectionHomeomorph H s x hx y : H) = chartAt H x y.1 := rfl

@[simp]
theorem chartIntersectionHomeomorph_symm_apply (s : Finset M) (x : M) (hx : x ∈ s)
    (y : chartIntersectionImageOpen H s x hx) :
    ((chartIntersectionHomeomorph H s x hx).symm y : M) = (chartAt H x).symm y.1 := rfl

/-- Compactness supplies an actual finite subcover of the preferred chart domains. -/
theorem exists_finite_chart_cover [CompactSpace M] :
    ∃ s : Finset M, (⋃ x ∈ s, (chartAt H x).source) = Set.univ := by
  have hcover : (Set.univ : Set M) ⊆ ⋃ x : M, (chartAt H x).source := by
    rw [iUnion_source_chartAt H M]
  obtain ⟨s, hs⟩ := (isCompact_univ : IsCompact (Set.univ : Set M)).elim_finite_subcover
    (fun x : M => (chartAt H x).source) (fun x => (chartAt H x).open_source) hcover
  exact ⟨s, Set.Subset.antisymm (Set.subset_univ _) hs⟩

/-- A finite set of chart centers selected from the proved finite-subcover theorem. -/
def compactChartCenters [CompactSpace M] : Finset M :=
  Classical.choose (exists_finite_chart_cover H (M := M))

theorem compactChartCenters_cover [CompactSpace M] :
    (⋃ x ∈ compactChartCenters H (M := M), (chartAt H x).source) = Set.univ :=
  Classical.choose_spec (exists_finite_chart_cover H (M := M))

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable (I : ModelWithCorners 𝕜 E H) [IsManifold I ∞ M]

/-- The same chart restriction is a genuine smooth diffeomorphism with the
canonical manifold structures on both open subsets. -/
def chartIntersectionDiffeomorph (s : Finset M) (x : M) (hx : x ∈ s) :
    chartIntersectionOpen H s ≃ₘ⟮I, I⟯ chartIntersectionImageOpen H s x hx where
  toEquiv := (chartIntersectionHomeomorph H s x hx).toEquiv
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (chartIntersectionImageOpen H s x hx) _).mp
    change ContMDiff I I ∞ (fun y : chartIntersectionOpen H s => chartAt H x y.1)
    exact (contMDiffOn_chart (I := I) (x := x)).comp_contMDiff
      (contMDiff_subtype_val (I := I) (U := chartIntersectionOpen H s))
      (fun y => chartIntersection_subset_source H s hx y.property)
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (chartIntersectionOpen H s) _).mp
    change ContMDiff I I ∞
      (fun y : chartIntersectionImageOpen H s x hx => (chartAt H x).symm y.1)
    exact (contMDiffOn_chart_symm (I := I) (x := x)).comp_contMDiff
      (contMDiff_subtype_val (I := I) (U := chartIntersectionImageOpen H s x hx))
      (fun y => chartIntersection_image_subset_target H s hx y.property)

/-- A compact smooth manifold has a finite chart cover whose every nonempty
finite family of domains intersects in a set diffeomorphic to an open model subset. -/
theorem exists_finite_smooth_chart_cover [CompactSpace M] :
    ∃ s : Finset M,
      (⋃ x ∈ s, (chartAt H x).source) = Set.univ ∧
      ∀ t : Finset M, t ⊆ s → t.Nonempty →
        ∃ V : Opens H, Nonempty (chartIntersectionOpen H t ≃ₘ⟮I, I⟯ V) := by
  obtain ⟨s, hs⟩ := exists_finite_chart_cover H (M := M)
  refine ⟨s, hs, ?_⟩
  intro t _ ht
  obtain ⟨x, hx⟩ := ht
  exact ⟨chartIntersectionImageOpen H t x hx, ⟨chartIntersectionDiffeomorph H I t x hx⟩⟩

end

end OAI.Topology.Euclidean.FiniteChartCover.Globalization
