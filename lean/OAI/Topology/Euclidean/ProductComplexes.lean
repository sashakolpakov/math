import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Exact

/-! # Product Complexes -/

namespace OAI.Topology.Euclidean.ProductComplexes.Globalization

noncomputable section

/-!
# Arbitrarily indexed products of module cochain complexes

This is the arbitrary-index extension of the countable construction in
`Globalization.ProductComplex`. Its degree objects are actual Cartesian
products and its differentials act coordinatewise. Choosing preimages in
each coordinate proves exactness of the product functor and preservation
of exactness at each degree and of quasi-isomorphisms.
-/

open _root_.CategoryTheory

universe u v

variable (R : Type u) [Ring R] (I : Type v)

/-- The actual Cartesian product functor for a family of modules. -/
def moduleIndexedProduct :
    (Discrete I ⥤ ModuleCat.{v} R) ⥤ ModuleCat.{v} R where
  obj F := ModuleCat.of R (∀ i : I, F.obj ⟨i⟩)
  map f := ModuleCat.ofHom
    { toFun := fun x i => f.app ⟨i⟩ (x i)
      map_add' := by
        intro x y
        funext i
        exact map_add (f.app ⟨i⟩).hom (x i) (y i)
      map_smul' := by
        intro r x
        funext i
        exact map_smul (f.app ⟨i⟩).hom r (x i) }
  map_id F := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    rfl

instance moduleIndexedProduct_preservesZeroMorphisms :
    (moduleIndexedProduct R I).PreservesZeroMorphisms where
  map_zero F G := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    rfl

instance moduleIndexedProduct_additive : (moduleIndexedProduct R I).Additive where
  map_add := by
    intro _ _ _ _
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    rfl

/-- Kernel elements in a product have coordinatewise preimages whenever the
input short complex is exact. -/
theorem moduleIndexedProduct_map_exact
    (S : ShortComplex (Discrete I ⥤ ModuleCat.{v} R)) (hS : S.Exact) :
    (S.map (moduleIndexedProduct R I)).Exact := by
  classical
  apply (ShortComplex.moduleCat_exact_iff _).2
  intro x hx
  have hi : ∀ i : I, ∃ y : S.X₁.obj ⟨i⟩, S.f.app ⟨i⟩ y = x i := by
    intro i
    have hs := hS.map ((evaluation (Discrete I) (ModuleCat.{v} R)).obj ⟨i⟩)
    apply (ShortComplex.moduleCat_exact_iff _).1 hs (x i)
    exact congrFun hx i
  choose y hy using hi
  exact ⟨y, funext hy⟩

instance moduleIndexedProduct_preservesHomology :
    (moduleIndexedProduct R I).PreservesHomology :=
  Functor.preservesHomology_of_map_exact (moduleIndexedProduct R I)
    (moduleIndexedProduct_map_exact R I)

variable {I}

/-- A family of actual cochain complexes as one complex of module-valued
functors on the discrete index category. -/
def cochainIndexedFamily (K : I → CochainComplex (ModuleCat.{v} R) ℕ) :
    CochainComplex (Discrete I ⥤ ModuleCat.{v} R) ℕ where
  X n := Discrete.functor (fun i => (K i).X n)
  d n m := Discrete.natTrans (fun i => (K i.as).d n m)
  shape := by
    intro n m h
    apply NatTrans.ext
    funext i
    exact (K i.as).shape n m h
  d_comp_d' := by
    intro n m k _ _
    apply NatTrans.ext
    funext i
    exact (K i.as).d_comp_d n m k

/-- A family of cochain maps, viewed as a map of complexes of functors. -/
def cochainIndexedMap {K L : I → CochainComplex (ModuleCat.{v} R) ℕ}
    (f : ∀ i, K i ⟶ L i) : cochainIndexedFamily R K ⟶ cochainIndexedFamily R L where
  f n := Discrete.natTrans (fun i => (f i.as).f n)
  comm' := by
    intro n m _
    apply NatTrans.ext
    funext i
    exact (f i.as).comm n m

/-- The cochain complex with Cartesian products in every degree and the
componentwise differential. -/
def indexedProductComplex (K : I → CochainComplex (ModuleCat.{v} R) ℕ) :
    CochainComplex (ModuleCat.{v} R) ℕ :=
  ((moduleIndexedProduct R I).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (cochainIndexedFamily R K)

@[simp]
theorem indexedProductComplex_X (K : I → CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    (indexedProductComplex R K).X n = ModuleCat.of R (∀ i, (K i).X n) := rfl

@[simp]
theorem indexedProductComplex_d_apply (K : I → CochainComplex (ModuleCat.{v} R) ℕ)
    (n m : ℕ) (x : ∀ i, (K i).X n) (i : I) :
    (indexedProductComplex R K).d n m x i = (K i).d n m (x i) := rfl

/-- Componentwise exactness gives exactness of the actual product complex,
including at degree zero. -/
theorem indexedProductComplex_exactAt (K : I → CochainComplex (ModuleCat.{v} R) ℕ)
    (n : ℕ) (hK : ∀ i, (K i).ExactAt n) : (indexedProductComplex R K).ExactAt n := by
  classical
  change ((indexedProductComplex R K).sc n).Exact
  apply (ShortComplex.moduleCat_exact_iff _).2
  intro x hx
  have hi : ∀ i : I, ∃ y : ((K i).sc n).X₁, ((K i).sc n).f y = x i := by
    intro i
    apply (ShortComplex.moduleCat_exact_iff _).1 (hK i) (x i)
    exact congrFun hx i
  choose y hy using hi
  exact ⟨y, funext hy⟩

/-- The actual coordinatewise map between product complexes. -/
def indexedProductMap {K L : I → CochainComplex (ModuleCat.{v} R) ℕ}
    (f : ∀ i, K i ⟶ L i) : indexedProductComplex R K ⟶ indexedProductComplex R L :=
  ((moduleIndexedProduct R I).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (cochainIndexedMap R f)

@[simp]
theorem indexedProductMap_f_apply {K L : I → CochainComplex (ModuleCat.{v} R) ℕ}
    (f : ∀ i, K i ⟶ L i) (n : ℕ) (x : ∀ i, (K i).X n) (i : I) :
    (indexedProductMap R f).f n x i = (f i).f n (x i) := rfl

theorem cochainIndexedMap_quasiIso {K L : I → CochainComplex (ModuleCat.{v} R) ℕ}
    (f : ∀ i, K i ⟶ L i) (hf : ∀ i, QuasiIso (f i)) :
    QuasiIso (cochainIndexedMap R f) := by
  apply (HomologicalComplex.quasiIso_iff_evaluation _).2
  intro i
  exact hf i.as

/-- A coordinatewise quasi-isomorphism is a quasi-isomorphism on products,
because the proved product functor preserves homology. -/
theorem indexedProductMap_quasiIso {K L : I → CochainComplex (ModuleCat.{v} R) ℕ}
    (f : ∀ i, K i ⟶ L i) (hf : ∀ i, QuasiIso (f i)) :
    QuasiIso (indexedProductMap R f) := by
  have := cochainIndexedMap_quasiIso R f hf
  change QuasiIso (((moduleIndexedProduct R I).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (cochainIndexedMap R f))
  infer_instance

end

end OAI.Topology.Euclidean.ProductComplexes.Globalization
