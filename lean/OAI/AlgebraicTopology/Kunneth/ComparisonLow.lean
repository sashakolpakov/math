import OAI.AlgebraicTopology.Kunneth.ProductModelsAs
import OAI.AlgebraicTopology.Kunneth.TensorHomologyD

/-! # Comparison Low -/

namespace OAI.AlgebraicTopology.Kunneth.ComparisonLow

noncomputable section

section

/-! The initial maps in the Eilenberg–Zilber comparison for Kunneth. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicTopology _root_.HomologicalComplex
open scoped Simplicial TensorProduct

namespace Construction.LowComparison

open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

variable (k : Type) [Field k]

def tensorZeroNatIso : ProductModelsAs.Construction.ProductModels.tensorBidegreeFunctor k 0 0 ≅ (ProductModelsAs.Construction.ProductModels.tensorChains k).X 0 :=
  NatIso.ofComponents
    (fun X => TensorHomologyD.Construction.TensorLowDegrees.degreeZeroIso
      ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.1) ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.2))
    (fun {_X _Y} f => (ProductModelsAs.Construction.ProductModels.tensorSummandInclusion k 0 0 0 rfl).naturality f)

/-- The canonical pairing of vertices identifies the degree-zero modules. -/
def zeroComparison : (ProductModelsAs.Construction.ProductModels.tensorChains k).X 0 ≅ (ProductModelsAs.Construction.ProductModels.productChains k).X 0 :=
  (tensorZeroNatIso k).symm ≪≫ (ProductModelsAs.Construction.ProductModels.tensorBidegreeFreeNatIso k 0 0).symm ≪≫
    ProductModelsAs.Construction.ProductModels.productDegreeFreeNatIso k 0

variable {k}

def pairSimplex (n : ℕ) (X : ProductModelsAs.Construction.ProductModels.SpacePair)
    (s : (TopCat.toSSet.obj X.1) _⦋n⦌) (t : (TopCat.toSSet.obj X.2) _⦋n⦌) :
    (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) _⦋n⦌ :=
  (ProductModelsAs.Construction.ProductModels.productSimplexEquiv n X).symm (s.down, t.down)

@[simp]
theorem pairSimplex_face (n : ℕ) (X : ProductModelsAs.Construction.ProductModels.SpacePair)
    (s : (TopCat.toSSet.obj X.1) _⦋n + 1⦌)
    (t : (TopCat.toSSet.obj X.2) _⦋n + 1⦌) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)).δ i (pairSimplex (n + 1) X s t) =
      pairSimplex n X ((TopCat.toSSet.obj X.1).δ i s)
        ((TopCat.toSSet.obj X.2).δ i t) := rfl

@[simp]
theorem pairSimplex_map (n : ℕ) {X Y : ProductModelsAs.Construction.ProductModels.SpacePair} (f : X ⟶ Y)
    (s : (TopCat.toSSet.obj X.1) _⦋n⦌) (t : (TopCat.toSSet.obj X.2) _⦋n⦌) :
    (TopCat.toSSet.map (ProductModelsAs.Construction.ProductModels.productSpace.map f)).app _ (pairSimplex n X s t) =
      pairSimplex n Y ((TopCat.toSSet.map f.1).app _ s)
        ((TopCat.toSSet.map f.2).app _ t) := rfl

theorem tensorBidegree_hom_ext (p q : ℕ) (X : ProductModelsAs.Construction.ProductModels.SpacePair) (M : ModuleCat.{0} k)
    (f g : ProductModelsAs.Construction.ProductModels.tensorBidegree k p q X ⟶ M)
    (h : ∀ s t, f (Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.1) s ⊗ₜ[k]
        Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.2) t) =
      g (Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.1) s ⊗ₜ[k]
        Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.2) t)) : f = g := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply Cohomology.Singular.ChainDual.chainFunctional_ext (TopCat.toSSet.obj X.1)
    (ModuleCat.of k (((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.2).X q →ₗ[k] M))
  intro s
  apply Cohomology.Singular.ChainDual.chainFunctional_ext (TopCat.toSSet.obj X.2) M
  intro t
  exact h s t

@[simp]
theorem zeroComparison_simplex (X : ProductModelsAs.Construction.ProductModels.SpacePair)
    (s : (TopCat.toSSet.obj X.1) _⦋0⦌) (t : (TopCat.toSSet.obj X.2) _⦋0⦌) :
    (zeroComparison k).hom.app X
      (ιTensorObj ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.1) ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.2) 0 0 0 rfl
        (Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.1) s ⊗ₜ[k]
          Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.2) t)) =
      Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X))
        (pairSimplex 0 X s t) := by
  change (ProductModelsAs.Construction.ProductModels.productDegreeFreeIso k 0 X).hom
    (ProductModelsAs.Construction.ProductModels.tensorFreeInv k 0 0 X
      (TensorHomologyD.Construction.TensorLowDegrees.zeroProjection _ _
        (ιTensorObj ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.1) ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.2)
          0 0 0 rfl _))) = _
  have hz := ConcreteCategory.congr_hom
    (TensorHomologyD.Construction.TensorLowDegrees.zeroInclusion_projection
      ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.1) ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.2))
    (Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.1) s ⊗ₜ[k]
      Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.2) t)
  change TensorHomologyD.Construction.TensorLowDegrees.zeroProjection _ _
    (ιTensorObj ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.1) ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.2)
      0 0 0 rfl _) = _ at hz
  rw [hz]
  change (ProductModelsAs.Construction.ProductModels.productDegreeFreeIso k 0 X).hom
    (ProductModelsAs.Construction.ProductModels.pairLinear k X.1 X.2 0 0 _ _
      (Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.1) s ⊗ₜ[k]
        Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.2) t)) = _
  rw [ProductModelsAs.Construction.ProductModels.pairLinear_simplex]
  exact ConcreteCategory.congr_hom (Sigma.ι_comp_desc
    (fun f : ProductModelsAs.Construction.ProductModels.simplexModel 0 0 ⟶ X =>
      (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)).ιChainComplex
        (R := ModuleCat.of k k) ((ProductModelsAs.Construction.ProductModels.productSimplexEquiv 0 X).symm f))
    (s.down, t.down)) (1 : k)

theorem simplexChain_boundary_one (K : SSet.{0}) (s : K _⦋1⦌) :
    (K.chainComplex (ModuleCat.of k k)).d 1 0 (Cohomology.Singular.ChainDual.simplexChain (R := k) K s) =
      Cohomology.Singular.ChainDual.simplexChain (R := k) K (K.δ 0 s) - Cohomology.Singular.ChainDual.simplexChain (R := k) K (K.δ 1 s) := by
  rw [Cohomology.Singular.ChainDual.simplexChain_boundary]
  simp [Fin.sum_univ_two, sub_eq_add_neg]

/-- A natural value on pairs of simplex generators extends linearly. -/
def pairNatural (p q : ℕ) (Q : ProductModelsAs.Construction.ProductModels.SpacePair ⥤ ModuleCat.{0} k)
    (v : ∀ X : ProductModelsAs.Construction.ProductModels.SpacePair, (TopCat.toSSet.obj X.1) _⦋p⦌ →
      (TopCat.toSSet.obj X.2) _⦋q⦌ → Q.obj X)
    (hv : ∀ (X Y : ProductModelsAs.Construction.ProductModels.SpacePair) (f : X ⟶ Y) s t,
      Q.map f (v X s t) = v Y ((TopCat.toSSet.map f.1).app _ s)
        ((TopCat.toSSet.map f.2).app _ t)) : ProductModelsAs.Construction.ProductModels.tensorBidegreeFunctor k p q ⟶ Q where
  app X := ModuleCat.ofHom (ProductModelsAs.Construction.ProductModels.pairLinear k X.1 X.2 p q (Q.obj X) (v X))
  naturality X Y f := by
    apply tensorBidegree_hom_ext
    intro s t
    change ProductModelsAs.Construction.ProductModels.pairLinear k Y.1 Y.2 p q (Q.obj Y) (v Y)
      (TensorProduct.map (((ProductModelsAs.Construction.ProductModels.scalarChains k).map f.1).f p).hom
        (((ProductModelsAs.Construction.ProductModels.scalarChains k).map f.2).f q).hom
        (Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.1) s ⊗ₜ[k]
          Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.2) t)) =
      Q.map f (ProductModelsAs.Construction.ProductModels.pairLinear k X.1 X.2 p q (Q.obj X) (v X) _)
    rw [TensorProduct.map_tmul, ProductModelsAs.Construction.ProductModels.scalarChains_map_simplex, ProductModelsAs.Construction.ProductModels.scalarChains_map_simplex,
      ProductModelsAs.Construction.ProductModels.pairLinear_simplex, ProductModelsAs.Construction.ProductModels.pairLinear_simplex, hv]

@[simp]
theorem pairNatural_simplex (p q : ℕ) (Q : ProductModelsAs.Construction.ProductModels.SpacePair ⥤ ModuleCat.{0} k) (v hv)
    (X : ProductModelsAs.Construction.ProductModels.SpacePair) (s : (TopCat.toSSet.obj X.1) _⦋p⦌)
    (t : (TopCat.toSSet.obj X.2) _⦋q⦌) :
    (pairNatural p q Q v hv).app X
      (Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.1) s ⊗ₜ[k]
        Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.2) t) = v X s t :=
  ProductModelsAs.Construction.ProductModels.pairLinear_simplex k X.1 X.2 p q (Q.obj X) (v X) s t

def cross10 : ProductModelsAs.Construction.ProductModels.tensorBidegreeFunctor k 1 0 ⟶ (ProductModelsAs.Construction.ProductModels.productChains k).X 1 :=
  pairNatural 1 0 ((ProductModelsAs.Construction.ProductModels.productChains k).X 1)
    (fun X s t => Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X))
      (pairSimplex 1 X s ((TopCat.toSSet.obj X.2).σ 0 t))) (by
    intro X Y f s t
    change ((ProductModelsAs.Construction.ProductModels.scalarChains k).map (ProductModelsAs.Construction.ProductModels.productSpace.map f)).f 1 _ = _
    rw [ProductModelsAs.Construction.ProductModels.scalarChains_map_simplex, pairSimplex_map, SSet.σ_naturality_apply])

def cross01 : ProductModelsAs.Construction.ProductModels.tensorBidegreeFunctor k 0 1 ⟶ (ProductModelsAs.Construction.ProductModels.productChains k).X 1 :=
  pairNatural 0 1 ((ProductModelsAs.Construction.ProductModels.productChains k).X 1)
    (fun X s t => Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X))
      (pairSimplex 1 X ((TopCat.toSSet.obj X.1).σ 0 s) t)) (by
    intro X Y f s t
    change ((ProductModelsAs.Construction.ProductModels.scalarChains k).map (ProductModelsAs.Construction.ProductModels.productSpace.map f)).f 1 _ = _
    rw [ProductModelsAs.Construction.ProductModels.scalarChains_map_simplex, pairSimplex_map, SSet.σ_naturality_apply])

theorem cross10_boundary :
    cross10 (k := k) ≫ (ProductModelsAs.Construction.ProductModels.productChains k).d 1 0 =
      ProductModelsAs.Construction.ProductModels.tensorSummandInclusion k 1 1 0 rfl ≫ (ProductModelsAs.Construction.ProductModels.tensorChains k).d 1 0 ≫
        (zeroComparison k).hom := by
  apply NatTrans.ext
  funext X
  change (cross10 (k := k)).app X ≫ ((ProductModelsAs.Construction.ProductModels.productChainFunctor k).obj X).d 1 0 =
    ιTensorObj ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.1) ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.2) 1 0 1 rfl ≫
      (((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.1) ⊗ ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.2)).d 1 0 ≫ _
  erw [TensorHomologyD.Construction.TensorLowDegrees.inclusion10_d_assoc]
  apply tensorBidegree_hom_ext
  intro s t
  change ((ProductModelsAs.Construction.ProductModels.productChainFunctor k).obj X).d 1 0
    (ProductModelsAs.Construction.ProductModels.pairLinear k X.1 X.2 1 0 _ _
      (Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.1) s ⊗ₜ[k]
        Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.2) t)) =
    (zeroComparison k).hom.app X
      (ιTensorObj ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.1) ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.2) 0 0 0 rfl
      (TensorProduct.map (((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.1).d 1 0).hom LinearMap.id
        (Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.1) s ⊗ₜ[k]
          Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.2) t)))
  erw [ProductModelsAs.Construction.ProductModels.pairLinear_simplex]
  erw [simplexChain_boundary_one (k := k)
    (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X))]
  erw [pairSimplex_face 0 X s ((TopCat.toSSet.obj X.2).σ 0 t) 0,
    pairSimplex_face 0 X s ((TopCat.toSSet.obj X.2).σ 0 t) 1]
  erw [SSet.δ_comp_σ_self_apply (S := TopCat.toSSet.obj X.2) (0 : Fin 1) t,
    SSet.δ_comp_σ_succ_apply (S := TopCat.toSSet.obj X.2) (0 : Fin 1) t]
  erw [TensorProduct.map_tmul]
  simp only [LinearMap.id_coe, id_eq]
  erw [simplexChain_boundary_one (k := k) (TopCat.toSSet.obj X.1)]
  erw [TensorProduct.sub_tmul, map_sub, map_sub, zeroComparison_simplex,
    zeroComparison_simplex]

theorem cross01_boundary :
    cross01 (k := k) ≫ (ProductModelsAs.Construction.ProductModels.productChains k).d 1 0 =
      ProductModelsAs.Construction.ProductModels.tensorSummandInclusion k 1 0 1 rfl ≫ (ProductModelsAs.Construction.ProductModels.tensorChains k).d 1 0 ≫
        (zeroComparison k).hom := by
  apply NatTrans.ext
  funext X
  change (cross01 (k := k)).app X ≫ ((ProductModelsAs.Construction.ProductModels.productChainFunctor k).obj X).d 1 0 =
    ιTensorObj ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.1) ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.2) 0 1 1 rfl ≫
      (((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.1) ⊗ ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.2)).d 1 0 ≫ _
  erw [TensorHomologyD.Construction.TensorLowDegrees.inclusion01_d_assoc]
  apply tensorBidegree_hom_ext
  intro s t
  change ((ProductModelsAs.Construction.ProductModels.productChainFunctor k).obj X).d 1 0
    (ProductModelsAs.Construction.ProductModels.pairLinear k X.1 X.2 0 1 _ _
      (Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.1) s ⊗ₜ[k]
        Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.2) t)) =
    (zeroComparison k).hom.app X
      (ιTensorObj ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.1) ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.2) 0 0 0 rfl
      (TensorProduct.map LinearMap.id (((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.2).d 1 0).hom
        (Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.1) s ⊗ₜ[k]
          Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.2) t)))
  erw [ProductModelsAs.Construction.ProductModels.pairLinear_simplex]
  erw [simplexChain_boundary_one (k := k)
    (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X))]
  erw [pairSimplex_face 0 X ((TopCat.toSSet.obj X.1).σ 0 s) t 0,
    pairSimplex_face 0 X ((TopCat.toSSet.obj X.1).σ 0 s) t 1]
  erw [SSet.δ_comp_σ_self_apply (S := TopCat.toSSet.obj X.1) (0 : Fin 1) s,
    SSet.δ_comp_σ_succ_apply (S := TopCat.toSSet.obj X.1) (0 : Fin 1) s]
  erw [TensorProduct.map_tmul]
  simp only [LinearMap.id_coe, id_eq]
  erw [simplexChain_boundary_one (k := k) (TopCat.toSSet.obj X.2)]
  erw [TensorProduct.tmul_sub, map_sub, map_sub, zeroComparison_simplex,
    zeroComparison_simplex]

/-- Maps from the tensor total complex are determined by its bidegrees. -/
theorem tensorNatural_hom_ext (n : ℕ) (Q : ProductModelsAs.Construction.ProductModels.SpacePair ⥤ ModuleCat.{0} k)
    (f g : (ProductModelsAs.Construction.ProductModels.tensorChains k).X n ⟶ Q)
    (h : ∀ p q hpq, ProductModelsAs.Construction.ProductModels.tensorSummandInclusion k n p q hpq ≫ f =
      ProductModelsAs.Construction.ProductModels.tensorSummandInclusion k n p q hpq ≫ g) : f = g := by
  apply NatTrans.ext
  funext X
  apply mapBifunctor.hom_ext
  intro p q hpq
  exact NatTrans.congr_app (h p q hpq) X

def tensorDesc (n : ℕ) (Q : ProductModelsAs.Construction.ProductModels.SpacePair ⥤ ModuleCat.{0} k)
    (v : ∀ p q, p + q = n → (ProductModelsAs.Construction.ProductModels.tensorBidegreeFunctor k p q ⟶ Q)) :
    (ProductModelsAs.Construction.ProductModels.tensorChains k).X n ⟶ Q where
  app X := mapBifunctorDesc (fun p q hpq => (v p q hpq).app X)
  naturality X Y f := by
    apply mapBifunctor.hom_ext
    intro p q hpq
    have h := (ProductModelsAs.Construction.ProductModels.tensorSummandInclusion k n p q hpq).naturality f
    change (ProductModelsAs.Construction.ProductModels.tensorBidegreeFunctor k p q).map f ≫
      ιTensorObj ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y.1) ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y.2) p q n hpq =
        ιTensorObj ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.1) ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.2) p q n hpq ≫
          ((ProductModelsAs.Construction.ProductModels.tensorChains k).X n).map f at h
    erw [← Category.assoc, ← h, Category.assoc]
    erw [ι_mapBifunctorDesc, ← Category.assoc, ι_mapBifunctorDesc]
    exact (v p q hpq).naturality f

@[reassoc (attr := simp)]
theorem inclusion_tensorDesc (n : ℕ) (Q : ProductModelsAs.Construction.ProductModels.SpacePair ⥤ ModuleCat.{0} k) (v)
    (p q : ℕ) (hpq : p + q = n) :
    ProductModelsAs.Construction.ProductModels.tensorSummandInclusion k n p q hpq ≫ tensorDesc n Q v = v p q hpq := by
  apply NatTrans.ext
  funext X
  exact ι_mapBifunctorDesc (K₁ := (ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.1)
    (K₂ := (ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.2) (F := curriedTensor (ModuleCat.{0} k))
    (c := ComplexShape.down ℕ) (fun p q hpq => (v p q hpq).app X) p q hpq

def crossOneBidegree (p q : ℕ) (hpq : p + q = 1) :
    ProductModelsAs.Construction.ProductModels.tensorBidegreeFunctor k p q ⟶ (ProductModelsAs.Construction.ProductModels.productChains k).X 1 :=
  if hp : p = 0 then
    eqToHom (by
      have hq : q = 1 := by omega
      subst p q
      rfl) ≫ cross01
  else
    eqToHom (by
      have hp' : p = 1 := by omega
      have hq : q = 0 := by omega
      subst p q
      rfl) ≫ cross10

def crossOne : (ProductModelsAs.Construction.ProductModels.tensorChains k).X 1 ⟶ (ProductModelsAs.Construction.ProductModels.productChains k).X 1 :=
  tensorDesc 1 ((ProductModelsAs.Construction.ProductModels.productChains k).X 1) crossOneBidegree

@[reassoc (attr := simp)]
theorem inclusion01_crossOne :
    ProductModelsAs.Construction.ProductModels.tensorSummandInclusion k 1 0 1 rfl ≫ crossOne = cross01 (k := k) := by
  simp [crossOne, crossOneBidegree]

@[reassoc (attr := simp)]
theorem inclusion10_crossOne :
    ProductModelsAs.Construction.ProductModels.tensorSummandInclusion k 1 1 0 rfl ≫ crossOne = cross10 (k := k) := by
  simp [crossOne, crossOneBidegree]

theorem crossOne_boundary :
    crossOne (k := k) ≫ (ProductModelsAs.Construction.ProductModels.productChains k).d 1 0 =
      (ProductModelsAs.Construction.ProductModels.tensorChains k).d 1 0 ≫ (zeroComparison k).hom := by
  apply tensorNatural_hom_ext
  intro p q hpq
  have h : (p = 0 ∧ q = 1) ∨ (p = 1 ∧ q = 0) := by omega
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [inclusion01_crossOne_assoc, cross01_boundary]
  · rw [inclusion10_crossOne_assoc, cross10_boundary]

end Construction.LowComparison

end

section

/-! The degree-one Alexander–Whitney map for Kunneth's chain comparison. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicTopology _root_.HomologicalComplex
open scoped Simplicial TensorProduct

namespace Construction.ReverseComparison

open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels OAI.AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison

variable {k : Type} [Field k]

def firstSimplex (n : ℕ) (X : ProductModelsAs.Construction.ProductModels.SpacePair)
    (s : (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) _⦋n⦌) :
    (TopCat.toSSet.obj X.1) _⦋n⦌ := ULift.up (ProductModelsAs.Construction.ProductModels.productSimplexEquiv n X s).1

def secondSimplex (n : ℕ) (X : ProductModelsAs.Construction.ProductModels.SpacePair)
    (s : (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) _⦋n⦌) :
    (TopCat.toSSet.obj X.2) _⦋n⦌ := ULift.up (ProductModelsAs.Construction.ProductModels.productSimplexEquiv n X s).2

@[simp]
theorem first_pair (n : ℕ) (X : ProductModelsAs.Construction.ProductModels.SpacePair) (s t) :
    firstSimplex n X (LowComparison.pairSimplex n X s t) = s :=
  congrArg (fun f : ProductModelsAs.Construction.ProductModels.simplexModel n n ⟶ X => ULift.up f.1)
    ((ProductModelsAs.Construction.ProductModels.productSimplexEquiv n X).apply_symm_apply (s.down, t.down))

@[simp]
theorem second_pair (n : ℕ) (X : ProductModelsAs.Construction.ProductModels.SpacePair) (s t) :
    secondSimplex n X (LowComparison.pairSimplex n X s t) = t :=
  congrArg (fun f : ProductModelsAs.Construction.ProductModels.simplexModel n n ⟶ X => ULift.up f.2)
    ((ProductModelsAs.Construction.ProductModels.productSimplexEquiv n X).apply_symm_apply (s.down, t.down))

@[simp]
theorem pair_first_second (n : ℕ) (X : ProductModelsAs.Construction.ProductModels.SpacePair) (s) :
    LowComparison.pairSimplex n X (firstSimplex n X s) (secondSimplex n X s) = s :=
  (ProductModelsAs.Construction.ProductModels.productSimplexEquiv n X).symm_apply_apply s

/-- Extend a natural value on paired simplices to chains on the product. -/
def productNatural (n : ℕ) (Q : ProductModelsAs.Construction.ProductModels.SpacePair ⥤ ModuleCat.{0} k)
    (v : ∀ X : ProductModelsAs.Construction.ProductModels.SpacePair, (TopCat.toSSet.obj X.1) _⦋n⦌ →
      (TopCat.toSSet.obj X.2) _⦋n⦌ → Q.obj X)
    (hv : ∀ (X Y : ProductModelsAs.Construction.ProductModels.SpacePair) (f : X ⟶ Y) s t,
      Q.map f (v X s t) = v Y ((TopCat.toSSet.map f.1).app _ s)
        ((TopCat.toSSet.map f.2).app _ t)) : (ProductModelsAs.Construction.ProductModels.productChains k).X n ⟶ Q where
  app X := ModuleCat.ofHom (Cohomology.Singular.ChainDual.chainFunctionalOfFunction
    (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) (Q.obj X) n
    (fun s => v X (firstSimplex n X s) (secondSimplex n X s)))
  naturality X Y f := by
    apply ModuleCat.hom_ext
    apply Cohomology.Singular.ChainDual.chainFunctional_ext (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) (Q.obj Y)
    intro s
    change Cohomology.Singular.ChainDual.chainFunctionalOfFunction _ _ n _
      (((ProductModelsAs.Construction.ProductModels.scalarChains k).map (ProductModelsAs.Construction.ProductModels.productSpace.map f)).f n
        (Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) s)) =
      Q.map f (Cohomology.Singular.ChainDual.chainFunctionalOfFunction _ _ n _
        (Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) s))
    rw [ProductModelsAs.Construction.ProductModels.scalarChains_map_simplex]
    erw [Cohomology.Singular.ChainDual.chainFunctionalOfFunction_simplex, Cohomology.Singular.ChainDual.chainFunctionalOfFunction_simplex]
    exact (hv X Y f (firstSimplex n X s) (secondSimplex n X s)).symm

@[simp]
theorem productNatural_simplex (n : ℕ) (Q : ProductModelsAs.Construction.ProductModels.SpacePair ⥤ ModuleCat.{0} k) (v hv)
    (X : ProductModelsAs.Construction.ProductModels.SpacePair) (s : (TopCat.toSSet.obj X.1) _⦋n⦌)
    (t : (TopCat.toSSet.obj X.2) _⦋n⦌) :
    (productNatural n Q v hv).app X
      (Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X))
        (LowComparison.pairSimplex n X s t)) = v X s t := by
  change Cohomology.Singular.ChainDual.chainFunctionalOfFunction _ _ n _ (Cohomology.Singular.ChainDual.simplexChain (R := k) _ _) = _
  rw [Cohomology.Singular.ChainDual.chainFunctionalOfFunction_simplex, first_pair, second_pair]

theorem productNatural_hom_ext (n : ℕ) (Q : ProductModelsAs.Construction.ProductModels.SpacePair ⥤ ModuleCat.{0} k)
    (f g : (ProductModelsAs.Construction.ProductModels.productChains k).X n ⟶ Q)
    (h : ∀ X s t, f.app X (Cohomology.Singular.ChainDual.simplexChain (R := k)
        (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) (LowComparison.pairSimplex n X s t)) =
      g.app X (Cohomology.Singular.ChainDual.simplexChain (R := k)
        (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) (LowComparison.pairSimplex n X s t))) : f = g := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply Cohomology.Singular.ChainDual.chainFunctional_ext (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) (Q.obj X)
  intro s
  have hs := h X (firstSimplex n X s) (secondSimplex n X s)
  rw [pair_first_second] at hs
  exact hs

@[simp]
theorem tensorSummand_map_simplex (n p q : ℕ) (hpq : p + q = n)
    {X Y : ProductModelsAs.Construction.ProductModels.SpacePair} (f : X ⟶ Y)
    (s : (TopCat.toSSet.obj X.1) _⦋p⦌) (t : (TopCat.toSSet.obj X.2) _⦋q⦌) :
    ((ProductModelsAs.Construction.ProductModels.tensorChains k).X n).map f
      (ιTensorObj ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.1) ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.2) p q n hpq
        (Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.1) s ⊗ₜ[k]
          Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.2) t)) =
      ιTensorObj ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y.1) ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y.2) p q n hpq
        (Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj Y.1) ((TopCat.toSSet.map f.1).app _ s) ⊗ₜ[k]
          Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj Y.2) ((TopCat.toSSet.map f.2).app _ t)) := by
  have h := ConcreteCategory.congr_hom
    ((ProductModelsAs.Construction.ProductModels.tensorSummandInclusion k n p q hpq).naturality f)
    (Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.1) s ⊗ₜ[k]
      Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.2) t)
  change ιTensorObj ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y.1) ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y.2) p q n hpq
    (TensorProduct.map (((ProductModelsAs.Construction.ProductModels.scalarChains k).map f.1).f p).hom
      (((ProductModelsAs.Construction.ProductModels.scalarChains k).map f.2).f q).hom _) = _ at h
  rw [TensorProduct.map_tmul, ProductModelsAs.Construction.ProductModels.scalarChains_map_simplex, ProductModelsAs.Construction.ProductModels.scalarChains_map_simplex] at h
  exact h.symm

def awOneValue (X : ProductModelsAs.Construction.ProductModels.SpacePair)
    (s : (TopCat.toSSet.obj X.1) _⦋1⦌) (t : (TopCat.toSSet.obj X.2) _⦋1⦌) :
    ((ProductModelsAs.Construction.ProductModels.tensorChains k).X 1).obj X :=
  ιTensorObj ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.1) ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.2) 0 1 1 rfl
    (Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.1) ((TopCat.toSSet.obj X.1).δ 1 s) ⊗ₜ[k]
      Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.2) t) +
  ιTensorObj ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.1) ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.2) 1 0 1 rfl
    (Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.1) s ⊗ₜ[k]
      Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.2) ((TopCat.toSSet.obj X.2).δ 0 t))

def awOne : (ProductModelsAs.Construction.ProductModels.productChains k).X 1 ⟶ (ProductModelsAs.Construction.ProductModels.tensorChains k).X 1 :=
  productNatural 1 ((ProductModelsAs.Construction.ProductModels.tensorChains k).X 1) awOneValue (by
    intro X Y f s t
    dsimp only [awOneValue]
    rw [map_add, tensorSummand_map_simplex, tensorSummand_map_simplex,
      SSet.δ_naturality_apply, SSet.δ_naturality_apply])

/-- The two edge terms have cancelling middle vertices. -/
theorem awOneValue_boundary (X : ProductModelsAs.Construction.ProductModels.SpacePair)
    (s : (TopCat.toSSet.obj X.1) _⦋1⦌) (t : (TopCat.toSSet.obj X.2) _⦋1⦌) :
    (LowComparison.zeroComparison k).hom.app X
      (((ProductModelsAs.Construction.ProductModels.tensorChains k).d 1 0).app X (awOneValue (k := k) X s t)) =
      ((ProductModelsAs.Construction.ProductModels.productChains k).d 1 0).app X
        (Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X))
          (LowComparison.pairSimplex 1 X s t)) := by
  change (LowComparison.zeroComparison k).hom.app X
    ((((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.1) ⊗ ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.2)).d 1 0
      (awOneValue (k := k) X s t)) =
    ((TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)).chainComplex (ModuleCat.of k k)).d 1 0
      (Cohomology.Singular.ChainDual.simplexChain (R := k) _ (LowComparison.pairSimplex 1 X s t))
  dsimp only [awOneValue]
  erw [map_add
    ((((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.1) ⊗ ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.2)).d 1 0).hom]
  erw [TensorHomologyD.Construction.TensorLowDegrees.inclusion01_d_apply ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.1)
      ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.2),
    TensorHomologyD.Construction.TensorLowDegrees.inclusion10_d_apply ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.1)
      ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.2)]
  erw [LowComparison.simplexChain_boundary_one (k := k) (TopCat.toSSet.obj X.1) s,
    LowComparison.simplexChain_boundary_one (k := k) (TopCat.toSSet.obj X.2) t,
    LowComparison.simplexChain_boundary_one (k := k) (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X))
      (LowComparison.pairSimplex 1 X s t)]
  simp only [TensorProduct.tmul_sub, TensorProduct.sub_tmul, map_sub, map_add,
    LowComparison.zeroComparison_simplex, LowComparison.pairSimplex_face]
  abel

theorem awOne_boundary :
    awOne (k := k) ≫ (ProductModelsAs.Construction.ProductModels.tensorChains k).d 1 0 =
      (ProductModelsAs.Construction.ProductModels.productChains k).d 1 0 ≫ (LowComparison.zeroComparison k).inv := by
  apply (cancel_mono (LowComparison.zeroComparison k).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply productNatural_hom_ext
  intro X s t
  change (LowComparison.zeroComparison k).hom.app X
    (((ProductModelsAs.Construction.ProductModels.tensorChains k).d 1 0).app X
      ((productNatural 1 ((ProductModelsAs.Construction.ProductModels.tensorChains k).X 1) awOneValue _).app X
        (Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X))
          (LowComparison.pairSimplex 1 X s t)))) = _
  rw [productNatural_simplex]
  exact awOneValue_boundary X s t

end Construction.ReverseComparison

end

/-! A natural Eilenberg–Zilber equivalence, proved by acyclic models. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicTopology _root_.HomologicalComplex
open scoped TensorProduct DirectSum

namespace Construction.EilenbergZilber

open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels OAI.AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison OAI.AlgebraicTopology.Kunneth.ComparisonLow.Construction.ReverseComparison

variable (k : Type) [Field k]

/-- The cross-product comparison, normalized on vertices and edges. -/
def cross : ProductModelsAs.Construction.ProductModels.tensorChains k ⟶ ProductModelsAs.Construction.ProductModels.productChains k :=
  AcyclicModelsF.Construction.AcyclicModels.extendChainMap (ProductModelsAs.Construction.ProductModels.tensorChains k) (ProductModelsAs.Construction.ProductModels.productChains k)
    (ProductModelsAs.Construction.ProductModels.tensorPresentation k)
    (fun _ i q => ProductModelsAs.Construction.ProductModels.product_model_positive_exact k i.val.1 i.val.2 q)
    (LowComparison.zeroComparison k).hom LowComparison.crossOne LowComparison.crossOne_boundary

/-- The reverse comparison, with the Alexander–Whitney edge formula. -/
def aw : ProductModelsAs.Construction.ProductModels.productChains k ⟶ ProductModelsAs.Construction.ProductModels.tensorChains k :=
  AcyclicModelsF.Construction.AcyclicModels.extendChainMap (ProductModelsAs.Construction.ProductModels.productChains k) (ProductModelsAs.Construction.ProductModels.tensorChains k)
    (ProductModelsAs.Construction.ProductModels.productPresentation k)
    (fun n _ q => ProductModelsAs.Construction.ProductModels.tensor_model_positive_exact k n n q)
    (LowComparison.zeroComparison k).inv ReverseComparison.awOne ReverseComparison.awOne_boundary

@[simp]
theorem cross_f_zero : (cross k).f 0 = (LowComparison.zeroComparison k).hom := rfl

@[simp]
theorem cross_f_one : (cross k).f 1 = LowComparison.crossOne := rfl

@[simp]
theorem aw_f_zero : (aw k).f 0 = (LowComparison.zeroComparison k).inv := rfl

@[simp]
theorem aw_f_one : (aw k).f 1 = ReverseComparison.awOne := rfl

def cross_aw_homotopy : Homotopy (cross k ≫ aw k) (𝟙 (ProductModelsAs.Construction.ProductModels.tensorChains k)) :=
  ProductModelsAs.Construction.ProductModels.tensorNaturalHomotopy k _ _ (by
    change (cross k).f 0 ≫ (aw k).f 0 = 𝟙 _
    rw [cross_f_zero, aw_f_zero, Iso.hom_inv_id])

def aw_cross_homotopy : Homotopy (aw k ≫ cross k) (𝟙 (ProductModelsAs.Construction.ProductModels.productChains k)) :=
  ProductModelsAs.Construction.ProductModels.productNaturalHomotopy k _ _ (by
    change (aw k).f 0 ≫ (cross k).f 0 = 𝟙 _
    rw [aw_f_zero, cross_f_zero, Iso.inv_hom_id])

/-- Singular chains on a product are naturally homotopy equivalent to
 the total tensor complex of the two singular chain complexes. -/
def naturalHomotopyEquiv : HomotopyEquiv (ProductModelsAs.Construction.ProductModels.tensorChains k) (ProductModelsAs.Construction.ProductModels.productChains k) where
  hom := cross k
  inv := aw k
  homotopyHomInvId := cross_aw_homotopy k
  homotopyInvHomId := aw_cross_homotopy k

/-- Evaluation gives the chain equivalence for arbitrary topological spaces. -/
def homotopyEquiv (X Y : TopCat.{0}) :
    HomotopyEquiv (((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X) ⊗ ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y))
      ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj (TopCat.of (X × Y))) :=
  ((evaluation ProductModelsAs.Construction.ProductModels.SpacePair (ModuleCat.{0} k)).obj (X, Y)).mapHomotopyEquiv
    (naturalHomotopyEquiv k)

/-- The homological Künneth decomposition over a field, for arbitrary spaces. -/
def singularHomologyKunneth (X Y : TopCat.{0}) (n : ℕ) :
    (⨁ ij : TensorHomologyD.Construction.TensorHomology.DegreePairs n,
      (((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X).homology ij.val.1 ⊗[k]
        ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).homology ij.val.2)) ≃ₗ[k]
      ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj (TopCat.of (X × Y))).homology n :=
  (TensorHomologyD.Construction.TensorHomology.algebraicKunneth ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X)
    ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y) n).trans
      (((homotopyEquiv k X Y).toHomologyIso n).toLinearEquiv)

end Construction.EilenbergZilber

end

end OAI.AlgebraicTopology.Kunneth.ComparisonLow
