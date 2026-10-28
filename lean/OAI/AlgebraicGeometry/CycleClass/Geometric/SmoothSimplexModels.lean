import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSimplexComposition
import Mathlib.AlgebraicTopology.SingularHomology.Basic

/-! # Smooth Simplex Models -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Geometric.SmoothSimplexModels.Cycles

/-!
# Singular subcomplexes closed under smooth simplex substitution

An object is a topological space with a specified singular subcomplex, closed
under precomposition by genuine ambient-smooth maps between closed standard
simplices. Morphisms are continuous maps preserving that subcomplex. This
concrete category accommodates both smooth manifolds and the closed simplex
models used to construct their subdivision homotopy.

The closure condition is an explicit property of actual maps. Instances for
the smooth singular sets are established separately from their definitions.
-/

open _root_.CategoryTheory _root_.AlgebraicTopology Opposite
open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex Simplicial

/-- A specified singular subcomplex closed under actual smooth substitutions. -/
structure SmoothSimplexSpace where
  space : TopCat.{0}
  smooth : (TopCat.toSSet.obj space).Subcomplex
  precomp_mem {n m : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), space))
    (hσ : (space.toSSetObjEquiv (.op ⦋n⦌)).symm σ ∈ smooth.obj (.op ⦋n⦌))
    (τ : C(Convexity.StdSimplex ℝ (Fin (m + 1)), Convexity.StdSimplex ℝ (Fin (n + 1))))
    (hτ : OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSimplexComposition.IsSmoothSimplexMap τ) :
    (space.toSSetObjEquiv (.op ⦋m⦌)).symm (σ.comp τ) ∈ smooth.obj (.op ⦋m⦌)

namespace SmoothSimplexSpace

/-- A continuous map preserving the specified singular subcomplexes. -/
structure Hom (X Y : SmoothSimplexSpace) where
  map : X.space ⟶ Y.space
  map_mem (n : SimplexCategoryᵒᵖ) (s : X.smooth.toSSet.obj n) :
    (TopCat.toSSet.map map).app n s.val ∈ Y.smooth.obj n

@[ext]
theorem Hom.ext {X Y : SmoothSimplexSpace} {f g : SmoothSimplexSpace.Hom X Y}
    (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance : Category SmoothSimplexSpace where
  Hom := SmoothSimplexSpace.Hom
  id X :=
    { map := 𝟙 X.space
      map_mem := by
        intro n s
        simp }
  comp f g :=
    { map := f.map ≫ g.map
      map_mem := by
        intro n s
        simpa only [Functor.map_comp, NatTrans.comp_app, types_comp_apply] using
          g.map_mem n ⟨(TopCat.toSSet.map f.map).app n s.val, f.map_mem n s⟩ }
  id_comp f := SmoothSimplexSpace.Hom.ext (Category.id_comp f.map)
  comp_id f := SmoothSimplexSpace.Hom.ext (Category.comp_id f.map)
  assoc f g h := SmoothSimplexSpace.Hom.ext (Category.assoc f.map g.map h.map)

@[simp]
theorem id_map (X : SmoothSimplexSpace) : (𝟙 X : X ⟶ X).map = 𝟙 X.space := rfl

@[simp]
theorem comp_map {X Y Z : SmoothSimplexSpace} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).map = f.map ≫ g.map := rfl

/-- The underlying topological space is unchanged. -/
def toTop : SmoothSimplexSpace ⥤ TopCat.{0} where
  obj X := X.space
  map f := f.map

/-- The actual restricted map on the specified singular simplicial sets. -/
def mapSmooth {X Y : SmoothSimplexSpace} (f : X ⟶ Y) :
    X.smooth.toSSet ⟶ Y.smooth.toSSet where
  app n := ↾fun s => ⟨(TopCat.toSSet.map f.map).app n s.val, f.map_mem n s⟩
  naturality n m θ := by
    apply ConcreteCategory.ext_apply
    intro s
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((TopCat.toSSet.map f.map).naturality θ) s.val

@[simp]
theorem mapSmooth_app_val {X Y : SmoothSimplexSpace} (f : X ⟶ Y)
    (n : SimplexCategoryᵒᵖ) (s : X.smooth.toSSet.obj n) :
    ((mapSmooth f).app n s).val = (TopCat.toSSet.map f.map).app n s.val := rfl

/-- The functor of the specified smooth singular simplicial sets. -/
def toSSet : SmoothSimplexSpace ⥤ SSet.{0} where
  obj X := X.smooth.toSSet
  map f := mapSmooth f
  map_id X := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.ext_apply
    intro s
    apply Subtype.ext
    simp only [mapSmooth_app_val, id_map]
    rfl
  map_comp f g := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.ext_apply
    intro s
    apply Subtype.ext
    simp only [mapSmooth_app_val, comp_map, Functor.map_comp, NatTrans.comp_app]
    rfl

/-- Inclusion into ordinary singular simplices commutes with every morphism. -/
@[reassoc]
theorem mapSmooth_inclusion {X Y : SmoothSimplexSpace} (f : X ⟶ Y) :
    mapSmooth f ≫ Y.smooth.ι = X.smooth.ι ≫ TopCat.toSSet.map f.map := rfl

/-- The actual integral smooth singular chains, functorially in these spaces. -/
def chainFunctor : SmoothSimplexSpace ⥤ ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  SmoothSimplexSpace.toSSet ⋙ (SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)

abbrev chains (X : SmoothSimplexSpace) : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  chainFunctor.obj X

abbrev chainMap {X Y : SmoothSimplexSpace} (f : X ⟶ Y) : chains X ⟶ chains Y :=
  chainFunctor.map f

/-- The degreewise integral chain functor. -/
abbrev degreeFunctor (n : ℕ) : SmoothSimplexSpace ⥤ ModuleCat.{0} ℤ :=
  chainFunctor ⋙ HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n

/-- The boundary is a natural transformation on the concrete category. -/
def boundaryNatural (i j : ℕ) : degreeFunctor i ⟶ degreeFunctor j where
  app X := (chains X).d i j
  naturality _ _ f := (chainMap f).comm i j

/-- The genuine chain functor regarded as a complex of functors. -/
abbrev naturalChains : ChainComplex (SmoothSimplexSpace ⥤ ModuleCat.{0} ℤ) ℕ where
  X := degreeFunctor
  d := boundaryNatural
  shape i j h := by
    apply NatTrans.ext
    funext X
    exact (chains X).shape i j h
  d_comp_d' i j k _ _ := by
    apply NatTrans.ext
    funext X
    exact (chains X).d_comp_d i j k

end SmoothSimplexSpace

end AlgebraicGeometry.CycleClass.Geometric.SmoothSimplexModels.Cycles

namespace AlgebraicGeometry.CycleClass.Geometric.SmoothSimplexModels.Cycles.SmoothSimplexSpace

/-!
# Actual closed simplex models for smooth singular chains

The smooth singular subcomplexes of normed subsets and manifolds satisfy the
explicit substitution condition. Every chosen smooth simplex then gives a
continuous, smooth-simplex-preserving map from its closed standard simplex
model. Evaluation on the identity simplex and postcomposition are literal.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex Simplicial

open OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSimplexComposition

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual ambient-smooth singular structure of an arbitrary normed subset. -/
def ofSubset (U : Set E) : SmoothSimplexSpace where
  space := TopCat.of U
  smooth := OAI.AlgebraicTopology.Cohomology.Singular.SmoothOpen.subsetSmoothSingularSubcomplex U
  precomp_mem σ hσ τ hτ := by
    change OAI.AlgebraicTopology.Cohomology.Singular.SmoothOpen.IsSmoothSimplexIn U σ at hσ
    change OAI.AlgebraicTopology.Cohomology.Singular.SmoothOpen.IsSmoothSimplexIn U (σ.comp τ)
    exact hσ.comp hτ

/-- The actual neighborhood-smooth singular structure of a charted manifold. -/
def ofManifold (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type) [TopologicalSpace M] [ChartedSpace E M] : SmoothSimplexSpace where
  space := TopCat.of M
  smooth := OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M
  precomp_mem σ hσ τ hτ := by
    change OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.IsManifoldSmoothSimplex E σ at hσ
    change OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.IsManifoldSmoothSimplex E (σ.comp τ)
    exact hσ.comp hτ

/-- The model is the closed geometric simplex with its actual ambient smooth structure. -/
def model (n : ℕ) : SmoothSimplexSpace where
  space := TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 1)))
  smooth := OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSimplexComposition.simplexSmoothSingularSubcomplex n
  precomp_mem σ hσ τ hτ := by
    change OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSimplexComposition.IsSmoothSimplexMap σ at hσ
    change OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSimplexComposition.IsSmoothSimplexMap (σ.comp τ)
    exact hσ.comp hτ

/-- The universal simplex is the identity of the actual geometric simplex. -/
def modelSimplex (n : ℕ) : (model n).smooth.toSSet.obj (.op ⦋n⦌) :=
  ⟨((model n).space.toSSetObjEquiv (.op ⦋n⦌)).symm
    (ContinuousMap.id (Convexity.StdSimplex ℝ (Fin (n + 1)))),
    OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSimplexComposition.isSmoothSimplexIn_stdSimplex_id n⟩

/-- Each actual smooth simplex defines a map from its smooth closed-simplex model. -/
def fromSimplex (X : SmoothSimplexSpace) (n : ℕ)
    (σ : X.smooth.toSSet.obj (.op ⦋n⦌)) : model n ⟶ X where
  map := TopCat.ofHom (X.space.toSSetObjEquiv (.op ⦋n⦌) σ.val)
  map_mem m τ := by
    have hσ : (X.space.toSSetObjEquiv (.op ⦋n⦌)).symm
        (X.space.toSSetObjEquiv (.op ⦋n⦌) σ.val) ∈ X.smooth.obj (.op ⦋n⦌) := by
      simpa only [Equiv.symm_apply_apply] using σ.property
    exact X.precomp_mem (X.space.toSSetObjEquiv (.op ⦋n⦌) σ.val) hσ
      ((model n).space.toSSetObjEquiv m τ.val) τ.property

/-- Evaluation at the identity model simplex recovers the given simplex. -/
@[simp]
theorem fromSimplex_modelSimplex (X : SmoothSimplexSpace) (n : ℕ)
    (σ : X.smooth.toSSet.obj (.op ⦋n⦌)) :
    (mapSmooth (fromSimplex X n σ)).app (.op ⦋n⦌) (modelSimplex n) = σ := by
  apply Subtype.ext
  apply (X.space.toSSetObjEquiv (.op ⦋n⦌)).injective
  ext x
  rfl

/-- The model map associated to the identity simplex is the identity morphism. -/
@[simp]
theorem fromSimplex_modelSimplex_id (n : ℕ) :
    fromSimplex (model n) n (modelSimplex n) = 𝟙 (model n) := by
  apply SmoothSimplexSpace.Hom.ext
  rfl

/-- Postcomposition of model maps agrees with the actual simplicial action. -/
@[reassoc]
theorem fromSimplex_naturality {X Y : SmoothSimplexSpace} (f : X ⟶ Y) (n : ℕ)
    (σ : X.smooth.toSSet.obj (.op ⦋n⦌)) :
    fromSimplex X n σ ≫ f =
      fromSimplex Y n ((mapSmooth f).app (.op ⦋n⦌) σ) := by
  apply SmoothSimplexSpace.Hom.ext
  rfl

/-- The chain generator carried by the model map is exactly the chosen generator. -/
@[reassoc (attr := simp)]
theorem modelGenerator_chainMap (X : SmoothSimplexSpace) (n : ℕ)
    (σ : X.smooth.toSSet.obj (.op ⦋n⦌)) :
    (model n).smooth.toSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) (modelSimplex n) ≫
      (chainMap (fromSimplex X n σ)).f n =
        X.smooth.toSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ := by
  change _ ≫ (SSet.chainComplexMap (mapSmooth (fromSimplex X n σ))
    (ModuleCat.of ℤ ℤ)).f n = _
  rw [SSet.ι_chainComplexMap_f, fromSimplex_modelSimplex]

end AlgebraicGeometry.CycleClass.Geometric.SmoothSimplexModels.Cycles.SmoothSimplexSpace

end

end OAI
