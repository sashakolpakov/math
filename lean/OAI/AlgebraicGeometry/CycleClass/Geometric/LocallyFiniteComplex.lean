import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains
import OAI.AlgebraicGeometry.CycleClass.Geometric.SpatialPushforward
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Category.ModuleCat.Basic

/-! # Locally Finite Complex -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles

noncomputable section

/-!
# The actual locally finite singular chain complex

Every simplicial reparametrization has image inside its source singular
simplex. The spatially locally finite coefficient pushforwards consequently
form a simplicial module. Its standard alternating face complex is the
locally finite singular chain complex.
-/

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

open _root_.CategoryTheory Opposite Set
open scoped Simplicial BigOperators

/-- An arbitrary simplicial reparametrization has image contained in the
image of the original singular simplex. -/
theorem singularSimplexImage_map_subset (X : TopCat.{0})
    {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b)
    (σ : (TopCat.toSSet.obj X).obj a) :
    LocallyFiniteChains.Cycles.singularSimplexImage X b.unop.len ((TopCat.toSSet.obj X).map f σ) ⊆
      LocallyFiniteChains.Cycles.singularSimplexImage X a.unop.len σ := by
  rintro x ⟨y, rfl⟩
  exact ⟨Convexity.StdSimplex.map f.unop y,
    (TopCat.toSSetObjEquiv_naturality_apply f.unop σ y).symm⟩

/-- Finite-fiber pushforward for any actual simplicial reparametrization. -/
def locallyFiniteSimplexMap (R : Type*) [Semiring R] (X : TopCat.{0})
    {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X a.unop.len →ₗ[R]
      LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X b.unop.len :=
  LocallyFiniteChains.Cycles.SpatialSupport.pushforward ((TopCat.toSSet.obj X).map f)
    (singularSimplexImage_map_subset X f)
    (LocallyFiniteChains.Cycles.singularSimplexImage_nonempty X b.unop.len)

@[simp]
theorem locallyFiniteSimplexMap_apply {R : Type*} [Semiring R] (X : TopCat.{0})
    {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b)
    (c : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X a.unop.len)
    (τ : (TopCat.toSSet.obj X).obj b) :
    locallyFiniteSimplexMap R X f c τ =
      ∑ᶠ σ ∈ {σ | (TopCat.toSSet.obj X).map f σ = τ}, c σ := rfl

@[simp]
theorem locallyFiniteSimplexMap_face (R : Type*) [Semiring R] (X : TopCat.{0})
    (n : ℕ) (i : Fin (n + 2)) :
    locallyFiniteSimplexMap R X (SimplexCategory.δ i).op =
      LocallyFiniteChains.Cycles.locallyFiniteFace R X n i := rfl

@[simp]
theorem locallyFiniteSimplexMap_id (R : Type*) [Semiring R] (X : TopCat.{0})
    (a : SimplexCategoryᵒᵖ) :
    locallyFiniteSimplexMap R X (𝟙 a) = LinearMap.id := by
  have hmap : (fun σ => (TopCat.toSSet.obj X).map (𝟙 a) σ) = id := by
    funext σ
    exact ConcreteCategory.congr_hom ((TopCat.toSSet.obj X).map_id a) σ
  exact (SpatialPushforward.Cycles.SpatialSupport.pushforward_congr hmap _ _ _).trans
    (SpatialPushforward.Cycles.SpatialSupport.pushforward_id _ _)

@[simp]
theorem locallyFiniteSimplexMap_comp (R : Type*) [Semiring R] (X : TopCat.{0})
    {a b c : SimplexCategoryᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) :
    locallyFiniteSimplexMap R X (f ≫ g) =
      (locallyFiniteSimplexMap R X g).comp (locallyFiniteSimplexMap R X f) := by
  unfold locallyFiniteSimplexMap
  rw [SpatialPushforward.Cycles.SpatialSupport.pushforward_comp]
  apply SpatialPushforward.Cycles.SpatialSupport.pushforward_congr
  funext σ
  exact ConcreteCategory.congr_hom ((TopCat.toSSet.obj X).map_comp f g) σ

/-- Spatially locally finite singular coefficients, with their actual
finite-fiber simplicial reparametrization maps. -/
def locallyFiniteSingularObject (R : Type*) [Ring R] (X : TopCat.{0}) :
    SimplicialObject (ModuleCat R) where
  obj a := ModuleCat.of R (LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X a.unop.len)
  map f := ModuleCat.ofHom (locallyFiniteSimplexMap R X f)
  map_id a := by
    apply ModuleCat.hom_ext
    exact locallyFiniteSimplexMap_id R X a
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact locallyFiniteSimplexMap_comp R X f g

@[simp]
theorem locallyFiniteSingularObject_obj (R : Type*) [Ring R] (X : TopCat.{0})
    (a : SimplexCategoryᵒᵖ) :
    (locallyFiniteSingularObject R X).obj a =
      ModuleCat.of R (LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X a.unop.len) := rfl

@[simp]
theorem locallyFiniteSingularObject_map (R : Type*) [Ring R] (X : TopCat.{0})
    {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    ((locallyFiniteSingularObject R X).map f).hom =
      locallyFiniteSimplexMap R X f := rfl

@[simp]
theorem locallyFiniteSingularObject_face (R : Type*) [Ring R] (X : TopCat.{0})
    (n : ℕ) (i : Fin (n + 2)) :
    ((locallyFiniteSingularObject R X).δ i).hom =
      LocallyFiniteChains.Cycles.locallyFiniteFace R X n i := rfl

/-- The genuine singular chain complex with spatially locally finite support.
The complex relation is the proved alternating-face relation for the actual
simplicial module, not an additional assumption. -/
def locallyFiniteSingularComplex (R : Type*) [Ring R] (X : TopCat.{0}) :
    ChainComplex (ModuleCat R) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat R)).obj
    (locallyFiniteSingularObject R X)

@[simp]
theorem locallyFiniteSingularComplex_X (R : Type*) [Ring R] (X : TopCat.{0})
    (n : ℕ) :
    (locallyFiniteSingularComplex R X).X n =
      ModuleCat.of R (LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X n) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Its boundary is the usual alternating sum of actual singular faces. -/
theorem locallyFiniteSingularComplex_d_int (R : Type*) [Ring R] (X : TopCat.{0})
    (n : ℕ) :
    ((locallyFiniteSingularComplex R X).d (n + 1) n).hom =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • LocallyFiniteChains.Cycles.locallyFiniteFace R X n i := by
  simp only [locallyFiniteSingularComplex,
    AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD,
    ModuleCat.hom_sum, ModuleCat.hom_zsmul, locallyFiniteSingularObject_face]

set_option backward.isDefEq.respectTransparency false in
/-- The boundary agrees with the coefficient-ring signed boundary defined
directly on spatially locally finite chains. -/
theorem locallyFiniteSingularComplex_d (R : Type*) [CommRing R] (X : TopCat.{0})
    (n : ℕ) :
    ((locallyFiniteSingularComplex R X).d (n + 1) n).hom =
      LocallyFiniteChains.Cycles.locallyFiniteBoundary R X n := by
  rw [locallyFiniteSingularComplex_d_int]
  unfold LocallyFiniteChains.Cycles.locallyFiniteBoundary
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using
    (Int.cast_smul_eq_zsmul R ((-1 : ℤ) ^ i.val) (LocallyFiniteChains.Cycles.locallyFiniteFace R X n i)).symm

/-- The directly defined alternating boundary squares to zero. -/
theorem locallyFiniteBoundary_squared (R : Type*) [CommRing R] (X : TopCat.{0})
    (n : ℕ) :
    (LocallyFiniteChains.Cycles.locallyFiniteBoundary R X n).comp (LocallyFiniteChains.Cycles.locallyFiniteBoundary R X (n + 1)) = 0 := by
  rw [← locallyFiniteSingularComplex_d, ← locallyFiniteSingularComplex_d]
  exact congrArg ModuleCat.Hom.hom
    ((locallyFiniteSingularComplex R X).d_comp_d (n + 2) (n + 1) n)

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles
