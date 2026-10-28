import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-! # Chart Open Diffeomorph -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ChartOpenDiffeomorph

noncomputable section

/-!
# Smooth coordinates on arbitrary open chart subdomains

An open subset contained in a chart source is diffeomorphic to its actual
open image under that chart. Neither the subset nor its image is required
to be nonempty, and the chart anchor need not belong to the subset.

Nested open submanifolds also flatten to their actual ambient open image,
through the pointwise identity on the underlying ambient points.
-/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

section ChartTopology

variable (H : Type*) [TopologicalSpace H]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The actual chart image of an arbitrary open subset of the chart source. -/
def chartOpenImage (x : M) (W : Opens M) (hW : (W : Set M) ⊆ (chartAt H x).source) :
    Opens H :=
  ⟨chartAt H x '' (W : Set M), (chartAt H x).isOpen_image_of_subset_source W.isOpen hW⟩

/-- Every point of the open chart image lies in the actual chart target. -/
theorem chartOpenImage_subset_target (x : M) (W : Opens M)
    (hW : (W : Set M) ⊆ (chartAt H x).source) :
    (chartOpenImage H x W hW : Set H) ⊆ (chartAt H x).target := by
  rintro y ⟨z, hz, rfl⟩
  exact (chartAt H x).map_source (hW hz)

/-- Restriction of the given chart is a homeomorphism onto its open image. -/
def chartOpenHomeomorph (x : M) (W : Opens M)
    (hW : (W : Set M) ⊆ (chartAt H x).source) :
    W ≃ₜ chartOpenImage H x W hW :=
  (chartAt H x).homeomorphOfImageSubsetSource hW rfl

@[simp]
theorem chartOpenHomeomorph_apply (x : M) (W : Opens M)
    (hW : (W : Set M) ⊆ (chartAt H x).source) (y : W) :
    (chartOpenHomeomorph H x W hW y : H) = chartAt H x (y : M) := rfl

@[simp]
theorem chartOpenHomeomorph_symm_apply (x : M) (W : Opens M)
    (hW : (W : Set M) ⊆ (chartAt H x).source) (y : chartOpenImage H x W hW) :
    ((chartOpenHomeomorph H x W hW).symm y : M) = (chartAt H x).symm (y : H) := rfl

end ChartTopology

section NestedTopology

variable {M : Type*} [TopologicalSpace M]

/-- The ambient open subset obtained by forgetting one layer of an open subtype. -/
def nestedOpenImage (U : Opens M) (W : Opens U) : Opens M :=
  ⟨Subtype.val '' (W : Set U), U.isOpenEmbedding'.isOpenMap _ W.isOpen⟩

/-- The flattened open subset is contained in the original ambient open subset. -/
theorem nestedOpenImage_subset (U : Opens M) (W : Opens U) :
    (nestedOpenImage U W : Set M) ⊆ (U : Set M) := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

private theorem nestedOpenImage_inner_mem (U : Opens M) (W : Opens U)
    (y : nestedOpenImage U W) :
    (⟨(y : M), nestedOpenImage_subset U W y.property⟩ : U) ∈ W := by
  rcases y.property with ⟨z, hz, heq⟩
  have h : (⟨(y : M), nestedOpenImage_subset U W y.property⟩ : U) = z :=
    Subtype.ext heq.symm
  exact h.symm ▸ hz

/-- Flattening two open-subtype layers preserves precisely the ambient point. -/
def nestedOpenEquiv (U : Opens M) (W : Opens U) : W ≃ nestedOpenImage U W where
  toFun y := ⟨((y : U) : M), ⟨(y : U), y.property, rfl⟩⟩
  invFun y := ⟨⟨(y : M), nestedOpenImage_subset U W y.property⟩,
    nestedOpenImage_inner_mem U W y⟩
  left_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv y := by
    apply Subtype.ext
    rfl

@[simp]
theorem nestedOpenEquiv_apply (U : Opens M) (W : Opens U) (y : W) :
    (nestedOpenEquiv U W y : M) = ((y : U) : M) := rfl

@[simp]
theorem nestedOpenEquiv_symm_apply (U : Opens M) (W : Opens U)
    (y : nestedOpenImage U W) :
    (((nestedOpenEquiv U W).symm y : U) : M) = (y : M) := rfl

end NestedTopology

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- Nested open submanifolds flatten smoothly while preserving the given model.
No nonemptiness or manifold-compatibility premise is needed for these inclusions. -/
def nestedOpenDiffeomorph (U : Opens M) (W : Opens U) :
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) W (nestedOpenImage U W) ∞ where
  toEquiv := nestedOpenEquiv U W
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (nestedOpenImage U W) _).mp
    change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun y : W => ((y : U) : M))
    exact (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := U)).comp
      (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := W))
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff W _).mp
    apply (ContMDiff.subtypeVal_comp_iff U _).mp
    change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (Subtype.val : nestedOpenImage U W → M)
    exact contMDiff_subtype_val

@[simp]
theorem nestedOpenDiffeomorph_apply (U : Opens M) (W : Opens U) (y : W) :
    (nestedOpenDiffeomorph E U W y : M) = ((y : U) : M) := rfl

@[simp]
theorem nestedOpenDiffeomorph_symm_apply (U : Opens M) (W : Opens U)
    (y : nestedOpenImage U W) :
    (((nestedOpenDiffeomorph E U W).symm y : U) : M) = (y : M) := rfl

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual chart identifies each open subset of its source smoothly with
its open model image. This includes empty subsets and subsets missing the anchor. -/
def chartOpenDiffeomorph (x : M) (W : Opens M)
    (hW : (W : Set M) ⊆ (chartAt E x).source) :
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) W (chartOpenImage E x W hW) ∞ where
  toEquiv := (chartOpenHomeomorph E x W hW).toEquiv
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (chartOpenImage E x W hW) _).mp
    change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun y : W => chartAt E x (y : M))
    exact (contMDiffOn_chart (I := 𝓘(ℝ, E)) (x := x)).comp_contMDiff
      (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := W)) (fun y => hW y.property)
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff W _).mp
    change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (fun y : chartOpenImage E x W hW => (chartAt E x).symm (y : E))
    exact (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (x := x)).comp_contMDiff
      (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := chartOpenImage E x W hW))
      (fun y => chartOpenImage_subset_target E x W hW y.property)

@[simp]
theorem chartOpenDiffeomorph_apply (x : M) (W : Opens M)
    (hW : (W : Set M) ⊆ (chartAt E x).source) (y : W) :
    (chartOpenDiffeomorph E x W hW y : E) = chartAt E x (y : M) := rfl

@[simp]
theorem chartOpenDiffeomorph_symm_apply (x : M) (W : Opens M)
    (hW : (W : Set M) ⊆ (chartAt E x).source) (y : chartOpenImage E x W hW) :
    ((chartOpenDiffeomorph E x W hW).symm y : M) = (chartAt E x).symm (y : E) := rfl

end

end OAI.AlgebraicTopology.Cohomology.Singular.ChartOpenDiffeomorph
