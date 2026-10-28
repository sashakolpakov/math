import OAI.AlgebraicGeometry.CycleClass.Geometric.SpatialPushforward
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Topology.Maps.Proper.Basic

/-! # Locally Finite Proper Map -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteProperMap.Cycles

noncomputable section

/-!
# Proper pushforward of spatially locally finite singular chains

Properness is the genuine topological property `IsProperMap`. Compact fibers
and closedness carry spatially locally finite families to locally finite image
families. This makes every coefficient sum in proper singular-chain pushforward
finite; no compactness of the whole source is imposed.
-/

open Set Filter Function _root_.CategoryTheory
open scoped _root_.Topology BigOperators Simplicial

/-- A genuine proper map sends a locally finite family to a locally finite
family of images. Neither separation nor closedness of the individual sets is needed. -/
theorem locallyFinite_image_of_isProperMap
    {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsProperMap f) {A : ι → Set X} (hA : LocallyFinite A) :
    LocallyFinite (fun i => f '' A i) := by
  intro y
  let bad : Set ι := {i | (closure (A i) ∩ f ⁻¹' {y}).Nonempty}
  have hbad : bad.Finite :=
    hA.closure.finite_nonempty_inter_compact (hf.isCompact_preimage isCompact_singleton)
  let C : Set X := ⋃ i : {i // i ∉ bad}, closure (A i.1)
  have hC : IsClosed C :=
    (hA.closure.comp_injective Subtype.val_injective).isClosed_iUnion
      (fun _ => isClosed_closure)
  have hy : y ∈ (f '' C)ᶜ := by
    rintro ⟨x, hx, hxy⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    apply i.property
    exact ⟨x, hi, hxy⟩
  refine ⟨(f '' C)ᶜ, (hf.isClosedMap C hC).isOpen_compl.mem_nhds hy,
    hbad.subset ?_⟩
  intro i hi
  by_contra hibad
  obtain ⟨z, ⟨x, hx, rfl⟩, hz⟩ := hi
  apply hz
  exact ⟨x, mem_iUnion.mpr ⟨⟨i, hibad⟩, subset_closure hx⟩, rfl⟩

namespace SpatialSupport

variable {X Y ι κ : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {R : Type*} [Semiring R]

/-- Proper image transport preserves local finiteness of the nonzero weighted
support, while leaving the coefficients themselves unchanged. -/
theorem proper_image {f : X → Y} (hf : IsProperMap f)
    {imageA : ι → Set X} {c : ι → R} (hc : LocallyFiniteChains.Cycles.SpatialSupport.IsLocallyFinite imageA c) :
    LocallyFiniteChains.Cycles.SpatialSupport.IsLocallyFinite (fun i => f '' imageA i) c := by
  apply (locallyFinite_image_of_isProperMap hf hc).subset
  intro i y hy
  obtain ⟨hci, x, hx, rfl⟩ := hy
  exact ⟨x, ⟨hci, hx⟩, rfl⟩

/-- Change the space in which local finiteness is measured by applying a proper map. -/
def properImageCoefficients (f : X → Y) (hf : IsProperMap f) (imageA : ι → Set X) :
    LocallyFiniteChains.Cycles.SpatialSupport.module R imageA →ₗ[R] LocallyFiniteChains.Cycles.SpatialSupport.module R (fun i => f '' imageA i) where
  toFun c := ⟨c, proper_image hf c.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem properImageCoefficients_apply (f : X → Y) (hf : IsProperMap f)
    (imageA : ι → Set X) (c : LocallyFiniteChains.Cycles.SpatialSupport.module R imageA) (i : ι) :
    properImageCoefficients f hf imageA c i = c i := rfl

/-- Compact proper fibers and spatial local finiteness make contributing
coefficient fibers finite after transport to the target space. -/
theorem proper_finite_fiber (f : X → Y) (hf : IsProperMap f)
    {imageA : ι → Set X} {imageB : κ → Set Y} (g : ι → κ)
    (himage : ∀ i, imageB (g i) ⊆ f '' imageA i)
    (hne : ∀ j, (imageB j).Nonempty) (c : LocallyFiniteChains.Cycles.SpatialSupport.module R imageA) (j : κ) :
    ({i | g i = j} ∩ support (c : ι → R)).Finite :=
  LocallyFiniteChains.Cycles.SpatialSupport.finite_fiber g himage hne (properImageCoefficients f hf imageA c) j

/-- Finite coefficient summation along an index map, with spatial local
finiteness justified by an actual proper map of underlying spaces. -/
def properPushforward (f : X → Y) (hf : IsProperMap f)
    {imageA : ι → Set X} {imageB : κ → Set Y} (g : ι → κ)
    (himage : ∀ i, imageB (g i) ⊆ f '' imageA i)
    (hne : ∀ j, (imageB j).Nonempty) :
    LocallyFiniteChains.Cycles.SpatialSupport.module R imageA →ₗ[R] LocallyFiniteChains.Cycles.SpatialSupport.module R imageB :=
  (LocallyFiniteChains.Cycles.SpatialSupport.pushforward g himage hne).comp (properImageCoefficients f hf imageA)

@[simp]
theorem properPushforward_apply (f : X → Y) (hf : IsProperMap f)
    {imageA : ι → Set X} {imageB : κ → Set Y} (g : ι → κ)
    (himage : ∀ i, imageB (g i) ⊆ f '' imageA i)
    (hne : ∀ j, (imageB j).Nonempty) (c : LocallyFiniteChains.Cycles.SpatialSupport.module R imageA) (j : κ) :
    properPushforward f hf g himage hne c j = LocallyFiniteChains.Cycles.SpatialSupport.fiberSum g c j := rfl

end SpatialSupport

/-- Postcomposition carries the geometric image of a singular simplex to its image under f. -/
theorem singularSimplexImage_postcompose {X Y : TopCat.{0}} (f : X ⟶ Y)
    (n : ℕ) (σ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌)) :
    LocallyFiniteChains.Cycles.singularSimplexImage Y n ((TopCat.toSSet.map f).app (.op ⦋n⦌) σ) =
      f '' LocallyFiniteChains.Cycles.singularSimplexImage X n σ := by
  change Set.range (fun z => f (X.toSSetObjEquiv (.op ⦋n⦌) σ z)) =
    f '' Set.range (X.toSSetObjEquiv (.op ⦋n⦌) σ)
  exact Set.range_comp' _ _

/-- The pushforward of actual spatially locally finite singular coefficients
along a genuine continuous proper map. -/
def locallyFiniteProperMap (R : Type*) [Semiring R] {X Y : TopCat.{0}}
    (f : X ⟶ Y) (hf : IsProperMap f) (n : ℕ) :
    LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X n →ₗ[R] LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R Y n :=
  SpatialSupport.properPushforward f hf ((TopCat.toSSet.map f).app (.op ⦋n⦌))
    (fun σ => (singularSimplexImage_postcompose f n σ).le)
    (LocallyFiniteChains.Cycles.singularSimplexImage_nonempty Y n)

/-- Every coefficient in the pushforward is an actual finite sum. -/
theorem locallyFiniteProperMap_finite {R : Type*} [Semiring R] {X Y : TopCat.{0}}
    (f : X ⟶ Y) (hf : IsProperMap f) (n : ℕ)
    (c : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X n)
    (τ : (TopCat.toSSet.obj Y).obj (.op ⦋n⦌)) :
    ({σ | (TopCat.toSSet.map f).app (.op ⦋n⦌) σ = τ} ∩ support (c : _ → R)).Finite :=
  SpatialSupport.proper_finite_fiber f hf ((TopCat.toSSet.map f).app (.op ⦋n⦌))
    (fun σ => (singularSimplexImage_postcompose f n σ).le)
    (LocallyFiniteChains.Cycles.singularSimplexImage_nonempty Y n) c τ

@[simp]
theorem locallyFiniteProperMap_apply {R : Type*} [Semiring R] {X Y : TopCat.{0}}
    (f : X ⟶ Y) (hf : IsProperMap f) (n : ℕ)
    (c : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X n)
    (τ : (TopCat.toSSet.obj Y).obj (.op ⦋n⦌)) :
    locallyFiniteProperMap R f hf n c τ =
      ∑ᶠ σ ∈ {σ | (TopCat.toSSet.map f).app (.op ⦋n⦌) σ = τ}, c σ := rfl

/-- An injective continuous map induces an injective map on actual singular simplices. -/
theorem singularSimplexMap_injective {X Y : TopCat.{0}} (f : X ⟶ Y)
    (hf : Function.Injective f) (n : ℕ) :
    Function.Injective ((TopCat.toSSet.map f).app (.op ⦋n⦌)) := by
  intro σ τ h
  apply (X.toSSetObjEquiv (.op ⦋n⦌)).injective
  ext x
  apply hf
  exact congrArg (fun υ => Y.toSSetObjEquiv (.op ⦋n⦌) υ x) h

/-- For an injective proper map, the coefficient at an image simplex is the original coefficient. -/
@[simp]
theorem locallyFiniteProperMap_apply_image {R : Type*} [Semiring R] {X Y : TopCat.{0}}
    (f : X ⟶ Y) (hproper : IsProperMap f) (hinj : Function.Injective f) (n : ℕ)
    (c : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X n)
    (σ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌)) :
    locallyFiniteProperMap R f hproper n c ((TopCat.toSSet.map f).app (.op ⦋n⦌) σ) =
      c σ := by
  simp [locallyFiniteProperMap_apply, (singularSimplexMap_injective f hinj n).eq_iff]

/-- Injective proper maps induce injective coefficient pushforwards. -/
theorem locallyFiniteProperMap_injective (R : Type*) [Semiring R] {X Y : TopCat.{0}}
    (f : X ⟶ Y) (hproper : IsProperMap f) (hinj : Function.Injective f) (n : ℕ) :
    Function.Injective (locallyFiniteProperMap R f hproper n) := by
  intro c d h
  apply Subtype.ext
  funext σ
  have hcoeff := congrArg
    (fun z : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R Y n => z ((TopCat.toSSet.map f).app (.op ⦋n⦌) σ)) h
  simpa only [locallyFiniteProperMap_apply_image f hproper hinj n] using hcoeff

/-- Proper pushforward commutes with every simplicial reparametrization.
Both iterated sums are reduced to the same proved-finite source fiber. -/
theorem locallyFiniteProperMap_naturality (R : Type*) [Semiring R]
    {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : IsProperMap f)
    {a b : SimplexCategoryᵒᵖ} (g : a ⟶ b) :
    (locallyFiniteProperMap R f hf b.unop.len).comp (LocallyFiniteComplex.Cycles.locallyFiniteSimplexMap R X g) =
      (LocallyFiniteComplex.Cycles.locallyFiniteSimplexMap R Y g).comp (locallyFiniteProperMap R f hf a.unop.len) := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  funext τ
  let u : (TopCat.toSSet.obj X).obj a → (TopCat.toSSet.obj X).obj b :=
    (TopCat.toSSet.obj X).map g
  let v : (TopCat.toSSet.obj X).obj b → (TopCat.toSSet.obj Y).obj b :=
    (TopCat.toSSet.map f).app b
  let w : (TopCat.toSSet.obj X).obj a → (TopCat.toSSet.obj Y).obj a :=
    (TopCat.toSSet.map f).app a
  let z : (TopCat.toSSet.obj Y).obj a → (TopCat.toSSet.obj Y).obj b :=
    (TopCat.toSSet.obj Y).map g
  have he : v ∘ u = z ∘ w := by
    funext σ
    exact ConcreteCategory.congr_hom ((TopCat.toSSet.map f).naturality g) σ
  have hleft : ({σ | v (u σ) = τ} ∩ support (c : _ → R)).Finite :=
    SpatialSupport.proper_finite_fiber f hf (v ∘ u)
      (fun σ => (singularSimplexImage_postcompose f b.unop.len (u σ)).le.trans
        (Set.image_mono (LocallyFiniteComplex.Cycles.singularSimplexImage_map_subset X g σ)))
      (LocallyFiniteChains.Cycles.singularSimplexImage_nonempty Y b.unop.len) c τ
  have hright : ({σ | z (w σ) = τ} ∩ support (c : _ → R)).Finite := by
    change ({σ | (z ∘ w) σ = τ} ∩ support (c : _ → R)).Finite
    rw [← he]
    exact hleft
  change LocallyFiniteChains.Cycles.SpatialSupport.fiberSum v (LocallyFiniteChains.Cycles.SpatialSupport.fiberSum u c) τ =
    LocallyFiniteChains.Cycles.SpatialSupport.fiberSum z (LocallyFiniteChains.Cycles.SpatialSupport.fiberSum w c) τ
  rw [SpatialPushforward.Cycles.SpatialSupport.fiberSum_comp_of_finite u v c τ hleft,
    SpatialPushforward.Cycles.SpatialSupport.fiberSum_comp_of_finite w z c τ hright, he]

/-- The proper identity map preserves every locally finite singular chain. -/
@[simp]
theorem locallyFiniteProperMap_id (R : Type*) [Semiring R] (X : TopCat.{0}) (n : ℕ) :
    locallyFiniteProperMap R (𝟙 X) isProperMap_id n = LinearMap.id := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  funext σ
  change LocallyFiniteChains.Cycles.SpatialSupport.fiberSum id (c : _ → R) σ = c σ
  exact congrFun (SpatialPushforward.Cycles.SpatialSupport.fiberSum_id (c : _ → R)) σ

/-- Proper pushforwards compose according to the actual continuous composite map. -/
theorem locallyFiniteProperMap_comp (R : Type*) [Semiring R] {X Y Z : TopCat.{0}}
    (f : X ⟶ Y) (hf : IsProperMap f) (g : Y ⟶ Z) (hg : IsProperMap g) (n : ℕ) :
    (locallyFiniteProperMap R g hg n).comp (locallyFiniteProperMap R f hf n) =
      locallyFiniteProperMap R (f ≫ g) (hg.comp hf) n := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  funext τ
  change LocallyFiniteChains.Cycles.SpatialSupport.fiberSum ((TopCat.toSSet.map g).app (.op ⦋n⦌))
      (LocallyFiniteChains.Cycles.SpatialSupport.fiberSum ((TopCat.toSSet.map f).app (.op ⦋n⦌)) c) τ =
    LocallyFiniteChains.Cycles.SpatialSupport.fiberSum ((TopCat.toSSet.map (f ≫ g)).app (.op ⦋n⦌)) c τ
  have he : ((TopCat.toSSet.map g).app (.op ⦋n⦌)) ∘
      ((TopCat.toSSet.map f).app (.op ⦋n⦌)) =
      ((TopCat.toSSet.map (f ≫ g)).app (.op ⦋n⦌)) := by
    funext σ
    rfl
  rw [SpatialPushforward.Cycles.SpatialSupport.fiberSum_comp_of_finite]
  · rw [he]
  · change ({σ | (((TopCat.toSSet.map g).app (.op ⦋n⦌)) ∘
        ((TopCat.toSSet.map f).app (.op ⦋n⦌))) σ = τ} ∩ support (c : _ → R)).Finite
    rw [he]
    exact locallyFiniteProperMap_finite (f ≫ g) (hg.comp hf) n c τ

/-- Actual proper pushforward is a morphism of the spatially locally finite simplicial modules. -/
def locallyFiniteProperObjectMap (R : Type*) [Ring R] {X Y : TopCat.{0}}
    (f : X ⟶ Y) (hf : IsProperMap f) :
    LocallyFiniteComplex.Cycles.locallyFiniteSingularObject R X ⟶ LocallyFiniteComplex.Cycles.locallyFiniteSingularObject R Y where
  app a := ModuleCat.ofHom (locallyFiniteProperMap R f hf a.unop.len)
  naturality _ _ g := by
    apply ModuleCat.hom_ext
    exact locallyFiniteProperMap_naturality R f hf g

/-- The genuine proper pushforward chain map on spatially locally finite singular chains. -/
def locallyFiniteProperChainMap (R : Type*) [Ring R] {X Y : TopCat.{0}}
    (f : X ⟶ Y) (hf : IsProperMap f) :
    LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X ⟶ LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R Y :=
  (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat R)).map
    (locallyFiniteProperObjectMap R f hf)

@[simp]
theorem locallyFiniteProperChainMap_f (R : Type*) [Ring R] {X Y : TopCat.{0}}
    (f : X ⟶ Y) (hf : IsProperMap f) (n : ℕ) :
    ((locallyFiniteProperChainMap R f hf).f n).hom = locallyFiniteProperMap R f hf n := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Proper pushforward commutes with the actual alternating boundary. -/
theorem locallyFiniteProperMap_boundary (R : Type*) [CommRing R] {X Y : TopCat.{0}}
    (f : X ⟶ Y) (hf : IsProperMap f) (n : ℕ) :
    (LocallyFiniteChains.Cycles.locallyFiniteBoundary R Y n).comp (locallyFiniteProperMap R f hf (n + 1)) =
      (locallyFiniteProperMap R f hf n).comp (LocallyFiniteChains.Cycles.locallyFiniteBoundary R X n) := by
  have h := congrArg ModuleCat.Hom.hom ((locallyFiniteProperChainMap R f hf).comm (n + 1) n)
  simpa only [ModuleCat.hom_comp, locallyFiniteProperChainMap_f,
    LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex_d] using h

/-- The induced map of genuine locally finite singular homology for a proper map. -/
abbrev locallyFiniteProperHomologyMap (R : Type*) [Ring R] {X Y : TopCat.{0}}
    (f : X ⟶ Y) (hf : IsProperMap f) (n : ℕ) :
    (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).homology n ⟶
      (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R Y).homology n :=
  HomologicalComplex.homologyMap (locallyFiniteProperChainMap R f hf) n

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteProperMap.Cycles
