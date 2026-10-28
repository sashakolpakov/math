import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Topology.LocallyFinite
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.LinearAlgebra.Pi

/-! # Locally Finite Chains -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles

noncomputable section

/-!
# Locally finite singular coefficients measured in the underlying space

Local finiteness is imposed on the images of the nonzero singular simplices
inside the underlying space X. It is not local finiteness in a topology on
the space of maps. Face coefficients are finite sums because every target
simplex has a point belonging to all its contributing source simplex images.

This file constructs the coefficient modules and individual face maps. It
does not postulate a Borel--Moore class, fundamental class, or cycle-class map.
-/

open Set Filter Function
open scoped _root_.Topology BigOperators Simplicial

namespace SpatialSupport

variable {X ι κ : Type*} [TopologicalSpace X]
variable {R : Type*} [Semiring R]

/-- The images indexed by nonzero coefficients form a locally finite family
of sets in X. -/
def IsLocallyFinite (image : ι → Set X) (c : ι → R) : Prop :=
  LocallyFinite (fun i => {x | c i ≠ 0 ∧ x ∈ image i})

theorem zero (image : ι → Set X) : IsLocallyFinite image (0 : ι → R) := by
  intro x
  refine ⟨univ, univ_mem, ?_⟩
  simp

theorem add {image : ι → Set X} {c d : ι → R}
    (hc : IsLocallyFinite image c) (hd : IsLocallyFinite image d) :
    IsLocallyFinite image (c + d) := by
  intro x
  obtain ⟨U, hU, hfinU⟩ := hc x
  obtain ⟨V, hV, hfinV⟩ := hd x
  refine ⟨U ∩ V, inter_mem hU hV, (hfinU.union hfinV).subset ?_⟩
  rintro i ⟨y, ⟨hne, hy⟩, hyU, hyV⟩
  by_cases hci : c i = 0
  · right
    refine ⟨y, ⟨?_, hy⟩, hyV⟩
    simpa only [Pi.add_apply, hci, zero_add] using hne
  · exact Or.inl ⟨y, ⟨hci, hy⟩, hyU⟩

theorem smul {image : ι → Set X} {c : ι → R}
    (r : R) (hc : IsLocallyFinite image c) : IsLocallyFinite image (r • c) := by
  exact hc.subset fun i x hx => ⟨fun hci => hx.1 (by simp [hci]), hx.2⟩

/-- Coefficients whose nonzero indexed images are locally finite form an
actual submodule of the function module. -/
def module (R : Type*) [Semiring R] (image : ι → Set X) : Submodule R (ι → R) where
  carrier := IsLocallyFinite image
  zero_mem' := zero image
  add_mem' := add
  smul_mem' r _ hc := smul r hc

instance (image : ι → Set X) : CoeFun (module R image) (fun _ => ι → R) :=
  ⟨Subtype.val⟩

/-- The contributing source coefficients over a fixed nonempty target image
form a finite set, proved from spatial local finiteness. -/
theorem finite_fiber {imageA : ι → Set X} {imageB : κ → Set X}
    (f : ι → κ) (himage : ∀ i, imageB (f i) ⊆ imageA i)
    (hne : ∀ j, (imageB j).Nonempty) (c : module R imageA) (j : κ) :
    ({i | f i = j} ∩ support (c : ι → R)).Finite := by
  obtain ⟨x, hx⟩ := hne j
  have hc : LocallyFinite (fun i => {x | c i ≠ 0 ∧ x ∈ imageA i}) := c.property
  apply (hc.point_finite x).subset
  rintro i ⟨hfi, hci⟩
  exact ⟨hci, himage i ((show f i = j from hfi).symm ▸ hx)⟩

/-- Summation of coefficients over an index-map fiber. Local finiteness
will ensure that every relevant sum below has finite support. -/
def fiberSum (f : ι → κ) (c : ι → R) (j : κ) : R :=
  ∑ᶠ i ∈ {i | f i = j}, c i

theorem fiberSum_locallyFinite {imageA : ι → Set X} {imageB : κ → Set X}
    (f : ι → κ) (himage : ∀ i, imageB (f i) ⊆ imageA i)
    (c : module R imageA) : IsLocallyFinite imageB (fiberSum f c) := by
  intro x
  obtain ⟨U, hU, hfin⟩ := (show IsLocallyFinite imageA (c : ι → R) from c.property) x
  refine ⟨U, hU, (hfin.image f).subset ?_⟩
  rintro j ⟨y, ⟨hcoef, hy⟩, hyU⟩
  obtain ⟨i, hfi, hci⟩ := exists_ne_zero_of_finsum_mem_ne_zero hcoef
  refine ⟨i, ⟨y, ⟨hci, ?_⟩, hyU⟩, hfi⟩
  exact himage i ((show f i = j from hfi).symm ▸ hy)

/-- A proved finite-fiber linear pushforward preserving spatial local
finiteness whenever target images are contained in their source images. -/
def pushforward {imageA : ι → Set X} {imageB : κ → Set X}
    (f : ι → κ) (himage : ∀ i, imageB (f i) ⊆ imageA i)
    (hne : ∀ j, (imageB j).Nonempty) :
    module R imageA →ₗ[R] module R imageB where
  toFun c := ⟨fiberSum f c, fiberSum_locallyFinite f himage c⟩
  map_add' c d := by
    apply Subtype.ext
    funext j
    exact finsum_mem_add_distrib' (finite_fiber f himage hne c j)
      (finite_fiber f himage hne d j)
  map_smul' r c := by
    apply Subtype.ext
    funext j
    exact ((DistribSMul.toAddMonoidHom R r).map_finsum_mem'
      (finite_fiber f himage hne c j)).symm

@[simp] theorem pushforward_apply {imageA : ι → Set X} {imageB : κ → Set X}
    (f : ι → κ) (himage : ∀ i, imageB (f i) ⊆ imageA i)
    (hne : ∀ j, (imageB j).Nonempty) (c : module R imageA) (j : κ) :
    pushforward f himage hne c j = ∑ᶠ i ∈ {i | f i = j}, c i := rfl

end SpatialSupport

/-- The spatial image of an actual continuous singular simplex. -/
def singularSimplexImage (X : TopCat.{0}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌)) : Set X :=
  Set.range (X.toSSetObjEquiv (.op ⦋n⦌) σ)

theorem singularSimplexImage_nonempty (X : TopCat.{0}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌)) :
    (singularSimplexImage X n σ).Nonempty := Set.range_nonempty _

/-- Each face image is contained in the image of its source simplex. -/
theorem singularSimplexImage_face_subset (X : TopCat.{0}) (n : ℕ) (i : Fin (n + 2))
    (σ : (TopCat.toSSet.obj X).obj (.op ⦋n + 1⦌)) :
    singularSimplexImage X n ((TopCat.toSSet.obj X).δ i σ) ⊆
      singularSimplexImage X (n + 1) σ := by
  rintro x ⟨y, rfl⟩
  exact ⟨Convexity.StdSimplex.map i.succAbove y, (TopCat.toSSetObjEquiv_δ_apply σ i y).symm⟩

/-- Singular coefficients whose nonzero simplex images are locally finite
in X. All additive and module operations are inherited from this submodule. -/
abbrev LocallyFiniteSingularChains (R : Type*) [Semiring R] (X : TopCat.{0}) (n : ℕ) :=
  SpatialSupport.module R (singularSimplexImage X n)

/-- Each face map has finite contributing fibers on spatially locally finite
singular chains. -/
theorem locallyFiniteFace_finite {R : Type*} [Semiring R] (X : TopCat.{0}) (n : ℕ)
    (i : Fin (n + 2)) (c : LocallyFiniteSingularChains R X (n + 1))
    (τ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌)) :
    ({σ | (TopCat.toSSet.obj X).δ i σ = τ} ∩ support (c : _ → R)).Finite :=
  SpatialSupport.finite_fiber ((TopCat.toSSet.obj X).δ i)
    (singularSimplexImage_face_subset X n i) (singularSimplexImage_nonempty X n) c τ

/-- The actual individual face pushforward on locally finite singular
coefficients, with all sums proved finite. -/
def locallyFiniteFace (R : Type*) [Semiring R] (X : TopCat.{0}) (n : ℕ)
    (i : Fin (n + 2)) :
    LocallyFiniteSingularChains R X (n + 1) →ₗ[R] LocallyFiniteSingularChains R X n :=
  SpatialSupport.pushforward ((TopCat.toSSet.obj X).δ i)
    (singularSimplexImage_face_subset X n i) (singularSimplexImage_nonempty X n)

@[simp] theorem locallyFiniteFace_apply {R : Type*} [Semiring R]
    (X : TopCat.{0}) (n : ℕ) (i : Fin (n + 2))
    (c : LocallyFiniteSingularChains R X (n + 1))
    (τ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌)) :
    locallyFiniteFace R X n i c τ =
      ∑ᶠ σ ∈ {σ | (TopCat.toSSet.obj X).δ i σ = τ}, c σ := rfl

/-- The alternating boundary as an actual degreewise linear map. The
boundary-square identity is a further obligation, not asserted here. -/
def locallyFiniteBoundary (R : Type*) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    LocallyFiniteSingularChains R X (n + 1) →ₗ[R] LocallyFiniteSingularChains R X n :=
  ∑ i : Fin (n + 2), (-1 : R) ^ i.val • locallyFiniteFace R X n i

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles
