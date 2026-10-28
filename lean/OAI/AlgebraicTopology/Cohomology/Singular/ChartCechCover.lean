import OAI.AlgebraicTopology.Cohomology.Singular.ChartOpenDiffeomorph
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech

/-! # Chart Cech Cover -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ChartCechCover

noncomputable section

/-!
# Preferred chart covers and their ordered Čech intersections

The sources of the preferred charts form an actual open cover. Every ordered
finite Čech intersection lies in its first chart source, hence is diffeomorphic
to its actual open image in the model space. The construction applies equally
to empty intersections and requires no convexity of the intersection or image.
-/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

section Topology

variable (H : Type*) [TopologicalSpace H]
variable (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- The open cover indexed by all preferred chart centers. -/
def preferredChartCover (x : M) : Opens M :=
  ⟨(chartAt H x).source, (chartAt H x).open_source⟩

@[simp]
theorem mem_preferredChartCover (x y : M) :
    y ∈ preferredChartCover H M x ↔ y ∈ (chartAt H x).source := Iff.rfl

/-- Every preferred chart contains its own center. -/
theorem mem_preferredChartCover_self (x : M) : x ∈ preferredChartCover H M x :=
  mem_chart_source H x

/-- The actual preferred chart sources cover every manifold point. -/
theorem preferredChartCover_covers (y : M) : ∃ x, y ∈ preferredChartCover H M x :=
  ⟨y, mem_preferredChartCover_self H M y⟩

/-- The same cover property in the lattice of open subsets. -/
theorem preferredChartCover_iSup_eq_top : (⨆ x, preferredChartCover H M x) = ⊤ := by
  apply top_unique
  intro y _
  exact (le_iSup (preferredChartCover H M) y) (mem_preferredChartCover_self H M y)

/-- An ordered Čech intersection lies in each chart named by its tuple. -/
theorem preferredChartCechIntersection_subset_source {p : ℕ}
    (a : Fin (p + 1) → M) (k : Fin (p + 1)) :
    (DeRham.Comparison.SmoothCech.cechIntersection (preferredChartCover H M) a : Set M) ⊆
      (chartAt H (a k)).source :=
  DeRham.Comparison.SmoothCech.cechIntersection_le (preferredChartCover H M) a k

/-- The actual open image of a Čech intersection in the tuple's first chart. -/
def preferredChartCechImage {p : ℕ} (a : Fin (p + 1) → M) : Opens H :=
  ChartOpenDiffeomorph.chartOpenImage H (a 0) (DeRham.Comparison.SmoothCech.cechIntersection (preferredChartCover H M) a)
    (preferredChartCechIntersection_subset_source H M a 0)

@[simp]
theorem coe_preferredChartCechImage {p : ℕ} (a : Fin (p + 1) → M) :
    (preferredChartCechImage H M a : Set H) =
      chartAt H (a 0) ''
        (DeRham.Comparison.SmoothCech.cechIntersection (preferredChartCover H M) a : Set M) := rfl

/-- The model image lies in the actual target of the chosen chart. -/
theorem preferredChartCechImage_subset_target {p : ℕ} (a : Fin (p + 1) → M) :
    (preferredChartCechImage H M a : Set H) ⊆ (chartAt H (a 0)).target :=
  ChartOpenDiffeomorph.chartOpenImage_subset_target H (a 0)
    (DeRham.Comparison.SmoothCech.cechIntersection (preferredChartCover H M) a)
    (preferredChartCechIntersection_subset_source H M a 0)

end Topology

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (M : Type*) [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Every ordered finite Čech intersection of preferred chart sources is
diffeomorphic to its actual open model image, including empty intersections. -/
def preferredChartCechDiffeomorph {p : ℕ} (a : Fin (p + 1) → M) :
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E)
      (DeRham.Comparison.SmoothCech.cechIntersection (preferredChartCover E M) a)
      (preferredChartCechImage E M a) ∞ :=
  ChartOpenDiffeomorph.chartOpenDiffeomorph E (a 0) (DeRham.Comparison.SmoothCech.cechIntersection (preferredChartCover E M) a)
    (preferredChartCechIntersection_subset_source E M a 0)

@[simp]
theorem preferredChartCechDiffeomorph_apply {p : ℕ} (a : Fin (p + 1) → M)
    (y : DeRham.Comparison.SmoothCech.cechIntersection (preferredChartCover E M) a) :
    (preferredChartCechDiffeomorph E M a y : E) = chartAt E (a 0) (y : M) := rfl

@[simp]
theorem preferredChartCechDiffeomorph_symm_apply {p : ℕ} (a : Fin (p + 1) → M)
    (y : preferredChartCechImage E M a) :
    ((preferredChartCechDiffeomorph E M a).symm y : M) =
      (chartAt E (a 0)).symm (y : E) := rfl

/-- A ready-to-use existence statement for the model-open Čech factors. -/
theorem preferredChartCechIntersection_diffeomorphic_open {p : ℕ}
    (a : Fin (p + 1) → M) :
    ∃ W : Opens E, Nonempty (Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E)
      (DeRham.Comparison.SmoothCech.cechIntersection (preferredChartCover E M) a) W ∞) :=
  ⟨preferredChartCechImage E M a, ⟨preferredChartCechDiffeomorph E M a⟩⟩

end

end OAI.AlgebraicTopology.Cohomology.Singular.ChartCechCover
