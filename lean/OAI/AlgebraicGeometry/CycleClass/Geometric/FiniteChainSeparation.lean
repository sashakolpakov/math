import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeChainSupport
import Mathlib.Topology.Sets.Opens

/-! # Finite Chain Separation -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteChainSeparation

noncomputable section

/-!
# Separating a point from a finite singular chain

Each actual singular simplex has compact image. Thus the finite union of
images with nonzero coefficients is compact, and is closed in a Hausdorff
space. If it avoids a point, its open complement is a neighborhood avoided
by every nonzero simplex in the chain.
-/

open _root_.CategoryTheory
open scoped Simplicial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Cycles

/-- The geometric image of an actual singular simplex is compact. -/
theorem singularSimplexImage_isCompact (X : TopCat.{0}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌)) :
    IsCompact (LocallyFiniteChains.Cycles.singularSimplexImage X n σ) :=
  isCompact_range (X.toSSetObjEquiv (.op ⦋n⦌) σ).continuous

/-- The geometric support of a finite integral chain, as the union of the
images of exactly its nonzero simplex coefficients. -/
def finiteChainImage (X : TopCat.{0}) (n : ℕ) (c : (LocalHomology.Cycles.integralSingularChains X).X n) :
    Set X :=
  ⋃ σ ∈ (LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients ℤ X n c).support,
    LocallyFiniteChains.Cycles.singularSimplexImage X n σ

/-- Membership in the geometric chain image is witnessed by a nonzero simplex. -/
theorem mem_finiteChainImage_iff (X : TopCat.{0}) (n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) (x : X) :
    x ∈ finiteChainImage X n c ↔
      ∃ σ, LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients ℤ X n c σ ≠ 0 ∧
        x ∈ LocallyFiniteChains.Cycles.singularSimplexImage X n σ := by
  simp [finiteChainImage, Finsupp.mem_support_iff]

/-- A finite chain has compact geometric image in every topological space. -/
theorem finiteChainImage_isCompact (X : TopCat.{0}) (n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) : IsCompact (finiteChainImage X n c) :=
  (LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients ℤ X n c).support.isCompact_biUnion
    (fun σ _ => singularSimplexImage_isCompact X n σ)

/-- A finite chain has closed geometric image in a Hausdorff space. -/
theorem finiteChainImage_isClosed (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) : IsClosed (finiteChainImage X n c) :=
  (finiteChainImage_isCompact X n c).isClosed

/-- If every nonzero simplex of a finite chain avoids a point, all these
simplices avoid a single open neighborhood of that point. -/
theorem exists_open_avoided_by_chain (X : TopCat.{0}) [T2Space X] (x : X) (n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X n)
    (hc : ∀ σ, LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients ℤ X n c σ ≠ 0 →
      x ∉ LocallyFiniteChains.Cycles.singularSimplexImage X n σ) :
    ∃ U : TopologicalSpace.Opens X, x ∈ U ∧
      ∀ σ, LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients ℤ X n c σ ≠ 0 →
        LocallyFiniteChains.Cycles.singularSimplexImage X n σ ⊆ (U : Set X)ᶜ := by
  refine ⟨⟨(finiteChainImage X n c)ᶜ, (finiteChainImage_isClosed X n c).isOpen_compl⟩,
    ?_, ?_⟩
  · change x ∉ finiteChainImage X n c
    intro hx
    obtain ⟨σ, hσ, hxσ⟩ := (mem_finiteChainImage_iff X n c x).mp hx
    exact hc σ hσ hxσ
  · intro σ hσ y hy
    change y ∈ (finiteChainImage X n c)ᶜᶜ
    rw [compl_compl]
    exact (mem_finiteChainImage_iff X n c y).mpr ⟨σ, hσ, hy⟩

/-- The avoiding neighborhood can be chosen inside any specified open
neighborhood of the point. -/
theorem exists_open_avoided_by_chain_within (X : TopCat.{0}) [T2Space X]
    (x : X) (n : ℕ) (c : (LocalHomology.Cycles.integralSingularChains X).X n)
    (hc : ∀ σ, LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients ℤ X n c σ ≠ 0 →
      x ∉ LocallyFiniteChains.Cycles.singularSimplexImage X n σ)
    (V : TopologicalSpace.Opens X) (hxV : x ∈ V) :
    ∃ U : TopologicalSpace.Opens X, x ∈ U ∧ U ≤ V ∧
      ∀ σ, LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients ℤ X n c σ ≠ 0 →
        LocallyFiniteChains.Cycles.singularSimplexImage X n σ ⊆ (U : Set X)ᶜ := by
  obtain ⟨W, hxW, hW⟩ := exists_open_avoided_by_chain X x n c hc
  refine ⟨V ⊓ W, ⟨hxV, hxW⟩, inf_le_left, ?_⟩
  intro σ hσ y hy hyU
  exact hW σ hσ hy hyU.2

/-- Point-relative vanishing means precisely that every nonzero simplex
avoids the point. This equivalence needs no separation assumption. -/
theorem relativeChainProjection_eq_zero_iff_avoids_point
    (X : TopCat.{0}) (x : X) (n : ℕ) (c : (LocalHomology.Cycles.integralSingularChains X).X n) :
    (LocalHomology.Cycles.relativeChainProjection X ({x}ᶜ : Set X)).f n c = 0 ↔
      ∀ σ, LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients ℤ X n c σ ≠ 0 →
        x ∉ LocallyFiniteChains.Cycles.singularSimplexImage X n σ := by
  simpa only [Set.subset_compl_singleton_iff] using
    (RelativeChainSupport.Cycles.relativeChainProjection_eq_zero_iff_supported X ({x}ᶜ : Set X) n c)

/-- A finite chain vanishing relative to a point already vanishes relative
to the complement of some open neighborhood. -/
theorem exists_open_relative_projection_eq_zero (X : TopCat.{0}) [T2Space X]
    (x : X) (n : ℕ) (c : (LocalHomology.Cycles.integralSingularChains X).X n)
    (hc : (LocalHomology.Cycles.relativeChainProjection X ({x}ᶜ : Set X)).f n c = 0) :
    ∃ U : TopologicalSpace.Opens X, x ∈ U ∧
      (LocalHomology.Cycles.relativeChainProjection X (U : Set X)ᶜ).f n c = 0 := by
  obtain ⟨U, hxU, hU⟩ := exists_open_avoided_by_chain X x n c
    ((relativeChainProjection_eq_zero_iff_avoids_point X x n c).mp hc)
  exact ⟨U, hxU, RelativeChainSupport.Cycles.relativeChainProjection_eq_zero_of_supported X (U : Set X)ᶜ n c hU⟩

/-- The finite-chain vanishing neighborhood may be shrunk inside any
previously chosen neighborhood, as needed for local-homology germs. -/
theorem exists_open_relative_projection_eq_zero_within (X : TopCat.{0}) [T2Space X]
    (x : X) (n : ℕ) (c : (LocalHomology.Cycles.integralSingularChains X).X n)
    (hc : (LocalHomology.Cycles.relativeChainProjection X ({x}ᶜ : Set X)).f n c = 0)
    (V : TopologicalSpace.Opens X) (hxV : x ∈ V) :
    ∃ U : TopologicalSpace.Opens X, x ∈ U ∧ U ≤ V ∧
      (LocalHomology.Cycles.relativeChainProjection X (U : Set X)ᶜ).f n c = 0 := by
  obtain ⟨U, hxU, hUV, hU⟩ := exists_open_avoided_by_chain_within X x n c
    ((relativeChainProjection_eq_zero_iff_avoids_point X x n c).mp hc) V hxV
  exact ⟨U, hxU, hUV, RelativeChainSupport.Cycles.relativeChainProjection_eq_zero_of_supported X (U : Set X)ᶜ n c hU⟩

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteChainSeparation
