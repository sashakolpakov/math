import OAI.AlgebraicTopology.Kunneth.AlexanderWhitney
import OAI.AlgebraicTopology.Kunneth.CohomologyTensorNe
import OAI.AlgebraicTopology.Products.Cup
import OAI.AlgebraicGeometry.CycleClass.Geometric.DualComplexUniversalCoefficient
import OAI.AlgebraicTopology.Products.CupCohomology

/-! # Tensor Alexander Whitney -/

namespace OAI.AlgebraicTopology.Kunneth.TensorAlexanderWhitney

noncomputable section

section

/-! The canonical Alexander–Whitney chain map, with the actual cup formula. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.HomologicalComplex
open scoped Simplicial TensorProduct

namespace Construction.AlexanderWhitney

open OAI.AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology OAI.AlgebraicTopology.Kunneth.AlexanderWhitney.Construction.AlexanderWhitneyComponents

variable {k : Type} [Field k]

def componentInDegree (K : SSet.{0}) (n : ℕ) (ij : TensorHomologyD.Construction.TensorHomology.DegreePairs n) :
    (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).X n ⟶
      (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).X ij.val.1 ⊗
        (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).X ij.val.2 :=
  ModuleCat.ofHom ((AlexanderWhitney.Construction.AlexanderWhitneyComponents.component K ij.val.1 ij.val.2).comp (Products.Cap.chainCast K ij.property.symm))

def degreeMap (K : SSet.{0}) (n : ℕ) :
    (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).X n ⟶
      (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K ⊗ Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).X n :=
  CohomologyTensorNe.Construction.TensorProjections.lift _ _ n (componentInDegree K n)

@[reassoc (attr := simp)]
theorem degreeMap_projection (K : SSet.{0}) (n : ℕ) (ij : TensorHomologyD.Construction.TensorHomology.DegreePairs n) :
    degreeMap (k := k) K n ≫ CohomologyTensorNe.Construction.TensorProjections.projection
        (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K) (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K) n ij =
      componentInDegree K n ij :=
  CohomologyTensorNe.Construction.TensorProjections.lift_projection _ _ n _ ij

theorem degreeMap_boundary (K : SSet.{0}) (n : ℕ) :
    degreeMap (k := k) K (n + 1) ≫
        (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K ⊗ Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).d (n + 1) n =
      (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).d (n + 1) n ≫ degreeMap K n := by
  apply CohomologyTensorNe.Construction.TensorProjections.hom_ext
  intro ij
  rcases ij with ⟨⟨p, q⟩, hpq⟩
  change p + q = n at hpq
  subst n
  conv_rhs => rw [Category.assoc, degreeMap_projection]
  rw [Category.assoc, CohomologyTensorNe.Construction.TensorProjections.differential_projection,
    Preadditive.comp_add, Preadditive.comp_zsmul]
  simp only [← Category.assoc, degreeMap_projection]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change TensorProduct.map ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).d (p + 1) p).hom LinearMap.id
      (AlexanderWhitney.Construction.AlexanderWhitneyComponents.component K (p + 1) q (Products.Cap.chainCast K (by omega : p + q + 1 = (p + 1) + q) z)) +
    (-1 : ℤ) ^ p • TensorProduct.map LinearMap.id
      ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).d (q + 1) q).hom
      (AlexanderWhitney.Construction.AlexanderWhitneyComponents.component K p (q + 1) (Products.Cap.chainCast K (by omega : p + q + 1 = p + (q + 1)) z)) =
    AlexanderWhitney.Construction.AlexanderWhitneyComponents.component K p q ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).d (p + q + 1) (p + q) z)
  exact (AlexanderWhitney.Construction.AlexanderWhitneyComponents.component_boundary K p q z).symm

/-- The front/back formula defines a chain map in all degrees. -/
def diagonal (K : SSet.{0}) :
    Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K ⟶
      Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K ⊗ Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K where
  f := degreeMap K
  comm' i j hij := by
    change j + 1 = i at hij
    subst i
    exact degreeMap_boundary K j

/-- Naturality of the canonical chain map, in every degree. -/
theorem diagonal_naturality {K L : SSet.{0}} (f : K ⟶ L) :
    Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := k) f ≫ diagonal L =
      diagonal K ≫ HomologicalComplex.tensorHom
        (Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := k) f) (Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := k) f) := by
  ext n : 1
  apply CohomologyTensorNe.Construction.TensorProjections.hom_ext
  intro ij
  rcases ij with ⟨⟨p, q⟩, hpq⟩
  change p + q = n at hpq
  subst n
  change ((Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := k) f).f (p + q) ≫ degreeMap L (p + q)) ≫ _ =
    (degreeMap K (p + q) ≫ (HomologicalComplex.tensorHom
      (Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := k) f) (Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := k) f)).f (p + q)) ≫ _
  rw [Category.assoc, degreeMap_projection, Category.assoc,
    CohomologyTensorNe.Construction.TensorProjections.projection_tensorHom, ← Category.assoc, degreeMap_projection]
  apply ModuleCat.hom_ext
  exact AlexanderWhitney.Construction.AlexanderWhitneyComponents.component_naturality f p q

@[simp]
theorem diagonal_zero_simplex (K : SSet.{0}) (s : K _⦋0⦌) :
    (diagonal (k := k) K).f 0 (Cohomology.Singular.ChainDual.simplexChain (R := k) K s) =
      ιTensorObj (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K)
        (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K) 0 0 0 rfl
        (Cohomology.Singular.ChainDual.simplexChain (R := k) K s ⊗ₜ[k] Cohomology.Singular.ChainDual.simplexChain (R := k) K s) := by
  have h : degreeMap (k := k) K 0 =
      componentInDegree K 0 ⟨(0, 0), rfl⟩ ≫
        ιTensorObj (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K)
          (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K) 0 0 0 rfl := by
    apply CohomologyTensorNe.Construction.TensorProjections.hom_ext
    intro ij
    have hij : ij = (⟨(0, 0), rfl⟩ : TensorHomologyD.Construction.TensorHomology.DegreePairs 0) := by
      apply Subtype.ext
      have hsum := ij.property
      apply Prod.ext <;> dsimp at * <;> omega
    subst ij
    rw [degreeMap_projection, Category.assoc]
    erw [CohomologyTensorNe.Construction.TensorProjections.inclusion_projection_self
      (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K) (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K)
      0 ⟨(0, 0), rfl⟩, Category.comp_id]
  change degreeMap K 0 (Cohomology.Singular.ChainDual.simplexChain (R := k) K s) = _
  rw [h]
  change ιTensorObj (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K)
    (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K) 0 0 0 rfl (AlexanderWhitney.Construction.AlexanderWhitneyComponents.component K 0 0 (Cohomology.Singular.ChainDual.simplexChain K s)) = _
  rw [AlexanderWhitney.Construction.AlexanderWhitneyComponents.component_simplex, Products.Cup.frontFace_zero_right]
  erw [Products.Cup.backFace_zero_left K (p := 0) s]

end Construction.AlexanderWhitney

end

section

/-! The canonical Alexander–Whitney comparison for products of spaces. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicTopology _root_.HomologicalComplex
open scoped Simplicial TensorProduct

namespace Construction.ProductAlexanderWhitney

open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels OAI.AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison OAI.AlgebraicTopology.Kunneth.ComparisonLow.Construction.ReverseComparison

variable (k : Type) [Field k]

def productAw (X : ProductModelsAs.Construction.ProductModels.SpacePair) :
    (ProductModelsAs.Construction.ProductModels.productChainFunctor k).obj X ⟶ (ProductModelsAs.Construction.ProductModels.tensorChainFunctor k).obj X :=
  AlexanderWhitney.diagonal (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) ≫
    HomologicalComplex.tensorHom
      ((ProductModelsAs.Construction.ProductModels.scalarChains k).map (TopCat.prodFst : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.1))
      ((ProductModelsAs.Construction.ProductModels.scalarChains k).map (TopCat.prodSnd : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.2))

theorem productAw_naturality {X Y : ProductModelsAs.Construction.ProductModels.SpacePair} (f : X ⟶ Y) :
    (ProductModelsAs.Construction.ProductModels.productChainFunctor k).map f ≫ productAw k Y =
      productAw k X ≫ (ProductModelsAs.Construction.ProductModels.tensorChainFunctor k).map f := by
  have hfst : (ProductModelsAs.Construction.ProductModels.scalarChains k).map (ProductModelsAs.Construction.ProductModels.productSpace.map f) ≫
      (ProductModelsAs.Construction.ProductModels.scalarChains k).map (TopCat.prodFst : ProductModelsAs.Construction.ProductModels.productSpace.obj Y ⟶ Y.1) =
      (ProductModelsAs.Construction.ProductModels.scalarChains k).map (TopCat.prodFst : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.1) ≫
        (ProductModelsAs.Construction.ProductModels.scalarChains k).map f.1 := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
  have hsnd : (ProductModelsAs.Construction.ProductModels.scalarChains k).map (ProductModelsAs.Construction.ProductModels.productSpace.map f) ≫
      (ProductModelsAs.Construction.ProductModels.scalarChains k).map (TopCat.prodSnd : ProductModelsAs.Construction.ProductModels.productSpace.obj Y ⟶ Y.2) =
      (ProductModelsAs.Construction.ProductModels.scalarChains k).map (TopCat.prodSnd : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.2) ≫
        (ProductModelsAs.Construction.ProductModels.scalarChains k).map f.2 := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
  have hd := AlexanderWhitney.diagonal_naturality (k := k)
    (TopCat.toSSet.map (ProductModelsAs.Construction.ProductModels.productSpace.map f))
  change (ProductModelsAs.Construction.ProductModels.scalarChains k).map (ProductModelsAs.Construction.ProductModels.productSpace.map f) ≫
    AlexanderWhitney.diagonal (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj Y)) =
      AlexanderWhitney.diagonal (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) ≫
        HomologicalComplex.tensorHom ((ProductModelsAs.Construction.ProductModels.scalarChains k).map (ProductModelsAs.Construction.ProductModels.productSpace.map f))
          ((ProductModelsAs.Construction.ProductModels.scalarChains k).map (ProductModelsAs.Construction.ProductModels.productSpace.map f)) at hd
  dsimp only [productAw]
  change (ProductModelsAs.Construction.ProductModels.scalarChains k).map (ProductModelsAs.Construction.ProductModels.productSpace.map f) ≫ _ =
    _ ≫ HomologicalComplex.tensorHom ((ProductModelsAs.Construction.ProductModels.scalarChains k).map f.1) ((ProductModelsAs.Construction.ProductModels.scalarChains k).map f.2)
  rw [← Category.assoc, hd, Category.assoc]
  change _ ≫ (((ProductModelsAs.Construction.ProductModels.scalarChains k).map (ProductModelsAs.Construction.ProductModels.productSpace.map f) ⊗ₘ
    (ProductModelsAs.Construction.ProductModels.scalarChains k).map (ProductModelsAs.Construction.ProductModels.productSpace.map f)) ≫
      ((ProductModelsAs.Construction.ProductModels.scalarChains k).map TopCat.prodFst ⊗ₘ (ProductModelsAs.Construction.ProductModels.scalarChains k).map TopCat.prodSnd)) =
    (_ ≫ ((ProductModelsAs.Construction.ProductModels.scalarChains k).map TopCat.prodFst ⊗ₘ (ProductModelsAs.Construction.ProductModels.scalarChains k).map TopCat.prodSnd)) ≫
      ((ProductModelsAs.Construction.ProductModels.scalarChains k).map f.1 ⊗ₘ (ProductModelsAs.Construction.ProductModels.scalarChains k).map f.2)
  rw [tensorHom_comp_tensorHom, hfst, hsnd, ← tensorHom_comp_tensorHom, Category.assoc]

/-- The canonical product comparison as a map of complexes of functors. -/
def productChainMap : ProductModelsAs.Construction.ProductModels.productChains k ⟶ ProductModelsAs.Construction.ProductModels.tensorChains k where
  f n :=
    { app X := (productAw k X).f n
      naturality X Y f := congrArg (fun a => a.f n) (productAw_naturality k f) }
  comm' i j _ := by
    apply NatTrans.ext
    funext X
    exact (productAw k X).comm i j

@[simp]
theorem productAw_zero_simplex (X : ProductModelsAs.Construction.ProductModels.SpacePair)
    (s : (TopCat.toSSet.obj X.1) _⦋0⦌) (t : (TopCat.toSSet.obj X.2) _⦋0⦌) :
    (productAw k X).f 0
      (Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) (ComparisonLow.Construction.LowComparison.pairSimplex 0 X s t)) =
      ιTensorObj ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.1) ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.2) 0 0 0 rfl
        (Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.1) s ⊗ₜ[k]
          Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.2) t) := by
  change (HomologicalComplex.tensorHom
    ((ProductModelsAs.Construction.ProductModels.scalarChains k).map (TopCat.prodFst : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.1))
    ((ProductModelsAs.Construction.ProductModels.scalarChains k).map (TopCat.prodSnd : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.2))).f 0
      ((AlexanderWhitney.diagonal (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X))).f 0
        (Cohomology.Singular.ChainDual.simplexChain (R := k) _ (ComparisonLow.Construction.LowComparison.pairSimplex 0 X s t))) = _
  rw [AlexanderWhitney.diagonal_zero_simplex]
  have h := ConcreteCategory.congr_hom
    (CohomologyTensorNe.Construction.TensorProjections.inclusion_tensorHom
      ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X))
      ((ProductModelsAs.Construction.ProductModels.scalarChains k).map (TopCat.prodFst : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.1))
      ((ProductModelsAs.Construction.ProductModels.scalarChains k).map (TopCat.prodSnd : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.2)) 0 ⟨(0, 0), rfl⟩)
    (Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) (ComparisonLow.Construction.LowComparison.pairSimplex 0 X s t) ⊗ₜ[k]
      Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) (ComparisonLow.Construction.LowComparison.pairSimplex 0 X s t))
  change _ = ιTensorObj ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.1) ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.2) 0 0 0 rfl
    (TensorProduct.map (((ProductModelsAs.Construction.ProductModels.scalarChains k).map TopCat.prodFst).f 0).hom
      (((ProductModelsAs.Construction.ProductModels.scalarChains k).map TopCat.prodSnd).f 0).hom _) at h
  rw [TensorProduct.map_tmul] at h
  erw [ProductModelsAs.Construction.ProductModels.scalarChains_map_simplex k (TopCat.prodFst : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.1)
      0 (ComparisonLow.Construction.LowComparison.pairSimplex 0 X s t),
    ProductModelsAs.Construction.ProductModels.scalarChains_map_simplex k (TopCat.prodSnd : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.2)
      0 (ComparisonLow.Construction.LowComparison.pairSimplex 0 X s t)] at h
  change _ = ιTensorObj ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.1) ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.2) 0 0 0 rfl
    (Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.1) (ComparisonLow.Construction.ReverseComparison.firstSimplex 0 X (ComparisonLow.Construction.LowComparison.pairSimplex 0 X s t)) ⊗ₜ[k]
      Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X.2) (ComparisonLow.Construction.ReverseComparison.secondSimplex 0 X (ComparisonLow.Construction.LowComparison.pairSimplex 0 X s t))) at h
  rw [ComparisonLow.Construction.ReverseComparison.first_pair, ComparisonLow.Construction.ReverseComparison.second_pair] at h
  exact h

@[simp]
theorem productChainMap_zero : (productChainMap k).f 0 = (ComparisonLow.Construction.LowComparison.zeroComparison k).inv := by
  apply (cancel_mono (ComparisonLow.Construction.LowComparison.zeroComparison k).hom).mp
  rw [Iso.inv_hom_id]
  apply ComparisonLow.Construction.ReverseComparison.productNatural_hom_ext
  intro X s t
  change (ComparisonLow.Construction.LowComparison.zeroComparison k).hom.app X ((productAw k X).f 0
    (Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) (ComparisonLow.Construction.LowComparison.pairSimplex 0 X s t))) = _
  rw [productAw_zero_simplex, ComparisonLow.Construction.LowComparison.zeroComparison_simplex]
  rfl

/-- The acyclic-model comparison agrees, up to homotopy, with the canonical formula. -/
def comparisonHomotopy : Homotopy (productChainMap k) (ComparisonLow.Construction.EilenbergZilber.aw k) :=
  AcyclicModelsF.Construction.AcyclicModels.homotopy (ProductModelsAs.Construction.ProductModels.productChains k) (ProductModelsAs.Construction.ProductModels.tensorChains k)
    (ProductModelsAs.Construction.ProductModels.productPresentation k) (fun n _ q => ProductModelsAs.Construction.ProductModels.tensor_model_positive_exact k n n q)
    _ _ (by rw [productChainMap_zero, ComparisonLow.Construction.EilenbergZilber.aw_f_zero])

/-- The canonical Alexander–Whitney map itself is a homotopy equivalence. -/
def canonicalHomotopyEquiv : HomotopyEquiv (ProductModelsAs.Construction.ProductModels.productChains k) (ProductModelsAs.Construction.ProductModels.tensorChains k) :=
  (ComparisonLow.Construction.EilenbergZilber.naturalHomotopyEquiv k).symm.copy (comparisonHomotopy k).symm

end Construction.ProductAlexanderWhitney

end

section

/-! Cycle-representative normalization of the algebraic Künneth isomorphism. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.HomologicalComplex
open scoped TensorProduct DirectSum

namespace Construction.TensorClassNormalization

open OAI.AlgebraicTopology.Kunneth.ChainSplittingD.Construction.ChainSplitting OAI.AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology

variable {k : Type} [Field k]

theorem zeroDifferentialHomologyIso_class (K : ChainComplex (ModuleCat.{0} k) ℕ)
    (hd : ∀ i j, K.d i j = 0) (n : ℕ) (z : Cohomology.Singular.ChainRepresentatives.chainCycles K n) :
    (TensorHomologyD.Construction.TensorHomology.zeroDifferentialHomologyIso K hd n).hom (Cohomology.Singular.ChainRepresentatives.chainClass K n z) = z.val := by
  let H := ShortComplex.HomologyData.ofZeros (K.sc n) (hd _ _) (hd _ _)
  have hi := H.left.cyclesIso_hom_comp_i
  change H.left.cyclesIso.hom ≫ 𝟙 (K.X n) = (K.sc n).iCycles at hi
  erw [Category.comp_id] at hi
  rw [Cohomology.Singular.ChainRepresentatives.chainClass_eq_homologyπ]
  have h := ConcreteCategory.congr_hom H.left.homologyπ_comp_homologyIso_hom
    ((K.sc n).moduleCatCyclesIso.inv z)
  change (TensorHomologyD.Construction.TensorHomology.zeroDifferentialHomologyIso K hd n).hom
    (K.homologyπ n ((K.sc n).moduleCatCyclesIso.inv z)) =
      H.left.cyclesIso.hom ((K.sc n).moduleCatCyclesIso.inv z) at h
  rw [hi] at h
  exact h.trans (ConcreteCategory.congr_hom (K.sc n).moduleCatCyclesIso_inv_iCycles z)

theorem zeroDifferentialHomologyIso_inv (K : ChainComplex (ModuleCat.{0} k) ℕ)
    (hd : ∀ i j, K.d i j = 0) (n : ℕ) (z : Cohomology.Singular.ChainRepresentatives.chainCycles K n) :
    (TensorHomologyD.Construction.TensorHomology.zeroDifferentialHomologyIso K hd n).inv z.val = Cohomology.Singular.ChainRepresentatives.chainClass K n z := by
  apply (TensorHomologyD.Construction.TensorHomology.zeroDifferentialHomologyIso K hd n).toLinearEquiv.injective
  change (TensorHomologyD.Construction.TensorHomology.zeroDifferentialHomologyIso K hd n).hom
    ((TensorHomologyD.Construction.TensorHomology.zeroDifferentialHomologyIso K hd n).inv z.val) =
      (TensorHomologyD.Construction.TensorHomology.zeroDifferentialHomologyIso K hd n).hom (Cohomology.Singular.ChainRepresentatives.chainClass K n z)
  rw [zeroDifferentialHomologyIso_class]
  exact ConcreteCategory.congr_hom (TensorHomologyD.Construction.TensorHomology.zeroDifferentialHomologyIso K hd n).inv_hom_id z.val

variable (C D : ChainComplex (ModuleCat.{0} k) ℕ)

def homologyTensorCycle (n : ℕ) (ij : TensorHomologyD.Construction.TensorHomology.DegreePairs n)
    (a : C.homology ij.val.1) (b : D.homology ij.val.2) :
    Cohomology.Singular.ChainRepresentatives.chainCycles (ChainSplittingD.Construction.ChainSplitting.homologyComplex C ⊗ ChainSplittingD.Construction.ChainSplitting.homologyComplex D) n :=
  ⟨ιTensorObj (ChainSplittingD.Construction.ChainSplitting.homologyComplex C) (ChainSplittingD.Construction.ChainSplitting.homologyComplex D) ij.val.1 ij.val.2 n ij.property
      (a ⊗ₜ[k] b), by
    change ((ChainSplittingD.Construction.ChainSplitting.homologyComplex C ⊗ ChainSplittingD.Construction.ChainSplitting.homologyComplex D).d n ((ComplexShape.down ℕ).next n)) _ = 0
    rw [TensorHomologyD.Construction.TensorHomology.tensorHomology_d_zero]
    rfl⟩

def representativeTensorCycle (n : ℕ) (ij : TensorHomologyD.Construction.TensorHomology.DegreePairs n)
    (a : C.homology ij.val.1) (b : D.homology ij.val.2) : Cohomology.Singular.ChainRepresentatives.chainCycles (C ⊗ D) n :=
  Cohomology.Singular.EvaluationNaturality.chainCycleMap (TensorHomologyD.Construction.TensorHomology.tensorHomologySplitting C D).hom n (homologyTensorCycle C D n ij a b)

@[simp]
theorem representativeTensorCycle_val (n : ℕ) (ij : TensorHomologyD.Construction.TensorHomology.DegreePairs n)
    (a : C.homology ij.val.1) (b : D.homology ij.val.2) :
    (representativeTensorCycle C D n ij a b).val =
      ιTensorObj C D ij.val.1 ij.val.2 n ij.property
        ((ChainSplittingD.Construction.ChainSplitting.representatives C ij.val.1 a).val ⊗ₜ[k] (ChainSplittingD.Construction.ChainSplitting.representatives D ij.val.2 b).val) := by
  have h := ConcreteCategory.congr_hom
    (CohomologyTensorNe.Construction.TensorProjections.inclusion_tensorHom (ChainSplittingD.Construction.ChainSplitting.homologyComplex C) (ChainSplittingD.Construction.ChainSplitting.homologyComplex D)
      (ChainSplittingD.Construction.ChainSplitting.inclusion C) (ChainSplittingD.Construction.ChainSplitting.inclusion D) n ij) (a ⊗ₜ[k] b)
  change _ = ιTensorObj C D ij.val.1 ij.val.2 n ij.property
    (TensorProduct.map (ChainSplittingD.Construction.ChainSplitting.inclusion C |>.f ij.val.1).hom
      (ChainSplittingD.Construction.ChainSplitting.inclusion D |>.f ij.val.2).hom (a ⊗ₜ[k] b)) at h
  rw [TensorProduct.map_tmul] at h
  exact h

/-- On a tensor generator, algebraic Künneth takes the class of the tensor
 of the chosen cycle representatives. -/
theorem algebraicKunneth_lof_tmul (n : ℕ) (ij : TensorHomologyD.Construction.TensorHomology.DegreePairs n)
    (a : C.homology ij.val.1) (b : D.homology ij.val.2) :
    TensorHomologyD.Construction.TensorHomology.algebraicKunneth C D n
      (DirectSum.lof k (TensorHomologyD.Construction.TensorHomology.DegreePairs n)
        (fun d => C.homology d.val.1 ⊗[k] D.homology d.val.2) ij (a ⊗ₜ[k] b)) =
      Cohomology.Singular.ChainRepresentatives.chainClass (C ⊗ D) n (representativeTensorCycle C D n ij a b) := by
  change HomologicalComplex.homologyMap (TensorHomologyD.Construction.TensorHomology.tensorHomologySplitting C D).hom n
    ((TensorHomologyD.Construction.TensorHomology.zeroDifferentialHomologyIso (ChainSplittingD.Construction.ChainSplitting.homologyComplex C ⊗ ChainSplittingD.Construction.ChainSplitting.homologyComplex D)
      (TensorHomologyD.Construction.TensorHomology.tensorHomology_d_zero C D) n).inv
      (TensorHomologyD.Construction.TensorHomology.tensorDegreeIn (ChainSplittingD.Construction.ChainSplitting.homologyComplex C) (ChainSplittingD.Construction.ChainSplitting.homologyComplex D) n
        (DirectSum.lof k (TensorHomologyD.Construction.TensorHomology.DegreePairs n)
          (fun d => C.homology d.val.1 ⊗[k] D.homology d.val.2) ij (a ⊗ₜ[k] b)))) = _
  rw [TensorHomologyD.Construction.TensorHomology.tensorDegreeIn_lof]
  change HomologicalComplex.homologyMap (TensorHomologyD.Construction.TensorHomology.tensorHomologySplitting C D).hom n
    ((TensorHomologyD.Construction.TensorHomology.zeroDifferentialHomologyIso (ChainSplittingD.Construction.ChainSplitting.homologyComplex C ⊗ ChainSplittingD.Construction.ChainSplitting.homologyComplex D)
      (TensorHomologyD.Construction.TensorHomology.tensorHomology_d_zero C D) n).inv (homologyTensorCycle C D n ij a b).val) = _
  rw [zeroDifferentialHomologyIso_inv, Cohomology.Singular.EvaluationNaturality.chainClass_naturality]
  rfl

end Construction.TensorClassNormalization

end

section

/-! Products of closed linear functionals on tensor chain complexes. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.HomologicalComplex OAI.AlgebraicGeometry.CycleClass.Geometric.DualComplexUniversalCoefficient.Cycles
open scoped TensorProduct DirectSum

namespace Construction.TensorCocycles

variable {k : Type} [Field k]

section Pairing

variable {A B E F : Type}
variable [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
variable [AddCommGroup E] [Module k E] [AddCommGroup F] [Module k F]

def pairing (a : Module.Dual k A) (b : Module.Dual k B) : Module.Dual k (A ⊗[k] B) :=
  TensorProduct.dualDistrib k A B (a ⊗ₜ[k] b)

@[simp]
theorem pairing_tmul (a : Module.Dual k A) (b : Module.Dual k B) (x : A) (y : B) :
    pairing a b (x ⊗ₜ[k] y) = a x * b y :=
  TensorProduct.dualDistrib_apply a b x y

@[simp]
theorem pairing_zero_left (b : Module.Dual k B) : pairing (0 : Module.Dual k A) b = 0 := by
  simp only [pairing, TensorProduct.zero_tmul, map_zero]

@[simp]
theorem pairing_zero_right (a : Module.Dual k A) : pairing a (0 : Module.Dual k B) = 0 := by
  simp only [pairing, TensorProduct.tmul_zero, map_zero]

theorem pairing_map (a : Module.Dual k A) (b : Module.Dual k B)
    (f : E →ₗ[k] A) (g : F →ₗ[k] B) :
    (pairing a b).comp (TensorProduct.map f g) = pairing (a.comp f) (b.comp g) := by
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, pairing_tmul]

end Pairing

variable (C D : ChainComplex (ModuleCat.{0} k) ℕ)

def tensorFunctional (p q : ℕ) (a : Module.Dual k (C.X p)) (b : Module.Dual k (D.X q)) :
    Module.Dual k ((C ⊗ D).X (p + q)) :=
  (pairing a b).comp (CohomologyTensorNe.Construction.TensorProjections.projection C D (p + q) ⟨(p, q), rfl⟩).hom

theorem tensorFunctional_closed (p q : ℕ)
    (a : Module.Dual k (C.X p)) (b : Module.Dual k (D.X q))
    (ha : a.comp (C.d (p + 1) p).hom = 0)
    (hb : b.comp (D.d (q + 1) q).hom = 0) :
    (tensorFunctional C D p q a b).comp ((C ⊗ D).d (p + q + 1) (p + q)).hom = 0 := by
  have hleft : (pairing a b).comp (TensorProduct.map (C.d (p + 1) p).hom
      (LinearMap.id : D.X q →ₗ[k] D.X q)) = 0 := by
    rw [pairing_map, ha, pairing_zero_left]
  have hright : (pairing a b).comp (TensorProduct.map
      (LinearMap.id : C.X p →ₗ[k] C.X p) (D.d (q + 1) q).hom) = 0 := by
    rw [pairing_map, hb, pairing_zero_right]
  apply LinearMap.ext
  intro z
  have h := ConcreteCategory.congr_hom
    (CohomologyTensorNe.Construction.TensorProjections.differential_projection C D (p + q) p q rfl) z
  change CohomologyTensorNe.Construction.TensorProjections.projection C D (p + q) ⟨(p, q), rfl⟩
      ((C ⊗ D).d (p + q + 1) (p + q) z) =
    TensorProduct.map (C.d (p + 1) p).hom LinearMap.id
      (CohomologyTensorNe.Construction.TensorProjections.projection C D (p + q + 1) ⟨(p + 1, q), by omega⟩ z) +
    (-1 : ℤ) ^ p • TensorProduct.map LinearMap.id (D.d (q + 1) q).hom
      (CohomologyTensorNe.Construction.TensorProjections.projection C D (p + q + 1) ⟨(p, q + 1), by omega⟩ z) at h
  change pairing a b (CohomologyTensorNe.Construction.TensorProjections.projection C D (p + q) ⟨(p, q), rfl⟩
    ((C ⊗ D).d (p + q + 1) (p + q) z)) = 0
  rw [h, map_add, map_zsmul]
  have hl := LinearMap.congr_fun hleft
    (CohomologyTensorNe.Construction.TensorProjections.projection C D (p + q + 1) ⟨(p + 1, q), by omega⟩ z)
  have hr := LinearMap.congr_fun hright
    (CohomologyTensorNe.Construction.TensorProjections.projection C D (p + q + 1) ⟨(p, q + 1), by omega⟩ z)
  change pairing a b _ = 0 at hl hr
  rw [hl, hr, smul_zero, add_zero]

def tensorCocycle (p q : ℕ)
    (a : Module.Dual k (C.X p)) (b : Module.Dual k (D.X q))
    (ha : a.comp (C.d (p + 1) p).hom = 0)
    (hb : b.comp (D.d (q + 1) q).hom = 0) :
    Cohomology.Singular.Representatives.cochainCocycles (AlgebraicGeometry.CycleClass.Geometric.DualComplexUniversalCoefficient.Cycles.linearHomCochainComplex (C ⊗ D) (ModuleCat.of k k)) (p + q) :=
  ⟨tensorFunctional C D p q a b, by
    apply (Cohomology.Singular.Representatives.mem_cochainCocycles_iff _ _ _).mpr
    change (tensorFunctional C D p q a b).comp
      ((C ⊗ D).d (p + q + 1) (p + q)).hom = 0
    exact tensorFunctional_closed C D p q a b ha hb⟩

def tensorHomologyFunctional (p q : ℕ)
    (a : Module.Dual k (C.X p)) (b : Module.Dual k (D.X q))
    (ha : a.comp (C.d (p + 1) p).hom = 0)
    (hb : b.comp (D.d (q + 1) q).hom = 0) : Module.Dual k ((C ⊗ D).homology (p + q)) :=
  AlgebraicGeometry.CycleClass.Geometric.DualComplexUniversalCoefficient.Cycles.evaluateLinearHomCocycle (C ⊗ D) (ModuleCat.of k k) (p + q)
    (tensorCocycle C D p q a b ha hb)

@[simp]
theorem tensorHomologyFunctional_class (p q : ℕ)
    (a : Module.Dual k (C.X p)) (b : Module.Dual k (D.X q))
    (ha : a.comp (C.d (p + 1) p).hom = 0)
    (hb : b.comp (D.d (q + 1) q).hom = 0) (z : Cohomology.Singular.ChainRepresentatives.chainCycles (C ⊗ D) (p + q)) :
    tensorHomologyFunctional C D p q a b ha hb (Cohomology.Singular.ChainRepresentatives.chainClass (C ⊗ D) (p + q) z) =
      tensorFunctional C D p q a b z.val :=
  AlgebraicGeometry.CycleClass.Geometric.DualComplexUniversalCoefficient.Cycles.evaluateLinearHomCocycle_chainClass _ _ _ _ z

theorem tensorHomologyFunctional_algebraic_self (p q : ℕ)
    (a : Module.Dual k (C.X p)) (b : Module.Dual k (D.X q))
    (ha : a.comp (C.d (p + 1) p).hom = 0)
    (hb : b.comp (D.d (q + 1) q).hom = 0)
    (u : C.homology p) (v : D.homology q) :
    tensorHomologyFunctional C D p q a b ha hb
      (TensorHomologyD.Construction.TensorHomology.algebraicKunneth C D (p + q)
        (DirectSum.lof k (TensorHomologyD.Construction.TensorHomology.DegreePairs (p + q))
          (fun ij => C.homology ij.val.1 ⊗[k] D.homology ij.val.2)
          ⟨(p, q), rfl⟩ (u ⊗ₜ[k] v))) =
      a (ChainSplittingD.Construction.ChainSplitting.representatives C p u).val * b (ChainSplittingD.Construction.ChainSplitting.representatives D q v).val := by
  rw [TensorClassNormalization.algebraicKunneth_lof_tmul, tensorHomologyFunctional_class,
    TensorClassNormalization.representativeTensorCycle_val]
  have h := ConcreteCategory.congr_hom
    (CohomologyTensorNe.Construction.TensorProjections.inclusion_projection_self C D (p + q) ⟨(p, q), rfl⟩)
    ((ChainSplittingD.Construction.ChainSplitting.representatives C p u).val ⊗ₜ[k] (ChainSplittingD.Construction.ChainSplitting.representatives D q v).val)
  change CohomologyTensorNe.Construction.TensorProjections.projection C D (p + q) ⟨(p, q), rfl⟩
    (ιTensorObj C D p q (p + q) rfl _) = _ at h
  change pairing a b (CohomologyTensorNe.Construction.TensorProjections.projection C D (p + q) ⟨(p, q), rfl⟩
    (ιTensorObj C D p q (p + q) rfl _)) = _
  rw [h]
  exact pairing_tmul a b _ _

theorem tensorHomologyFunctional_algebraic_other (p q : ℕ)
    (a : Module.Dual k (C.X p)) (b : Module.Dual k (D.X q))
    (ha : a.comp (C.d (p + 1) p).hom = 0)
    (hb : b.comp (D.d (q + 1) q).hom = 0)
    (ij : TensorHomologyD.Construction.TensorHomology.DegreePairs (p + q)) (hne : ij ≠ ⟨(p, q), rfl⟩)
    (u : C.homology ij.val.1) (v : D.homology ij.val.2) :
    tensorHomologyFunctional C D p q a b ha hb
      (TensorHomologyD.Construction.TensorHomology.algebraicKunneth C D (p + q)
        (DirectSum.lof k (TensorHomologyD.Construction.TensorHomology.DegreePairs (p + q))
          (fun ij => C.homology ij.val.1 ⊗[k] D.homology ij.val.2) ij (u ⊗ₜ[k] v))) = 0 := by
  rw [TensorClassNormalization.algebraicKunneth_lof_tmul, tensorHomologyFunctional_class,
    TensorClassNormalization.representativeTensorCycle_val]
  have h := ConcreteCategory.congr_hom
    (CohomologyTensorNe.Construction.TensorProjections.inclusion_projection_ne C D (p + q) ⟨(p, q), rfl⟩ ij hne)
    ((ChainSplittingD.Construction.ChainSplitting.representatives C ij.val.1 u).val ⊗ₜ[k]
      (ChainSplittingD.Construction.ChainSplitting.representatives D ij.val.2 v).val)
  change CohomologyTensorNe.Construction.TensorProjections.projection C D (p + q) ⟨(p, q), rfl⟩
    (ιTensorObj C D ij.val.1 ij.val.2 (p + q) ij.property _) = 0 at h
  change pairing a b (CohomologyTensorNe.Construction.TensorProjections.projection C D (p + q) ⟨(p, q), rfl⟩
    (ιTensorObj C D ij.val.1 ij.val.2 (p + q) ij.property _)) = 0
  rw [h, map_zero]

end Construction.TensorCocycles

end

/-! The prescribed cup product is the dual of canonical Alexander–Whitney. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.HomologicalComplex
open scoped Simplicial TensorProduct

namespace Construction.CupTensorComparison

open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels OAI.AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.ProductAlexanderWhitney OAI.AlgebraicTopology.Kunneth.AlexanderWhitney.Construction.AlexanderWhitneyComponents OAI.AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.TensorCocycles

variable (k : Type) [Field k]

@[reassoc]
theorem productAw_projection (X : ProductModelsAs.Construction.ProductModels.SpacePair) (n : ℕ) (ij : TensorHomologyD.Construction.TensorHomology.DegreePairs n) :
    (ProductAlexanderWhitney.productAw k X).f n ≫ CohomologyTensorNe.Construction.TensorProjections.projection
      ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.1) ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.2) n ij =
      AlexanderWhitney.componentInDegree (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) n ij ≫
        (((ProductModelsAs.Construction.ProductModels.scalarChains k).map (TopCat.prodFst : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.1)).f ij.val.1 ⊗ₘ
          ((ProductModelsAs.Construction.ProductModels.scalarChains k).map (TopCat.prodSnd : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.2)).f ij.val.2) := by
  change (AlexanderWhitney.degreeMap (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) n ≫
    (HomologicalComplex.tensorHom
      ((ProductModelsAs.Construction.ProductModels.scalarChains k).map (TopCat.prodFst : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.1))
      ((ProductModelsAs.Construction.ProductModels.scalarChains k).map (TopCat.prodSnd : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.2))).f n) ≫ _ = _
  rw [Category.assoc, CohomologyTensorNe.Construction.TensorProjections.projection_tensorHom, ← Category.assoc]
  erw [AlexanderWhitney.degreeMap_projection]

/-- On all chains, evaluation of the exterior cup equals evaluation after
 the actual canonical product-chain comparison. -/
theorem cup_tensor_chain (X : ProductModelsAs.Construction.ProductModels.SpacePair) (p q : ℕ)
    (c : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of k k) X.1).X p)
    (d : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of k k) X.2).X q)
    (z : ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)).X (p + q)) :
    TensorCocycles.tensorFunctional ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.1) ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.2) p q
      (Cohomology.Singular.ChainDual.degreewiseChainDualEquiv (TopCat.toSSet.obj X.1) (ModuleCat.of k k) p c)
      (Cohomology.Singular.ChainDual.degreewiseChainDualEquiv (TopCat.toSSet.obj X.2) (ModuleCat.of k k) q d)
      ((ProductAlexanderWhitney.productAw k X).f (p + q) z) =
    Cohomology.Singular.ChainDual.degreewiseChainDualEquiv (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) (ModuleCat.of k k) (p + q)
      (Products.Cup.singularCup (ProductModelsAs.Construction.ProductModels.productSpace.obj X)
        (((Cohomology.Singular.Functor.singularPullback (ModuleCat.of k k) (TopCat.prodFst : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.1)).f p) c)
        (((Cohomology.Singular.Functor.singularPullback (ModuleCat.of k k) (TopCat.prodSnd : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.2)).f q) d)) z := by
  have h : (TensorCocycles.tensorFunctional ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.1) ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.2) p q
      (Cohomology.Singular.ChainDual.degreewiseChainDualEquiv (TopCat.toSSet.obj X.1) (ModuleCat.of k k) p c)
      (Cohomology.Singular.ChainDual.degreewiseChainDualEquiv (TopCat.toSSet.obj X.2) (ModuleCat.of k k) q d)).comp
      ((ProductAlexanderWhitney.productAw k X).f (p + q)).hom =
    Cohomology.Singular.ChainDual.degreewiseChainDualEquiv (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) (ModuleCat.of k k) (p + q)
      (Products.Cup.singularCup (ProductModelsAs.Construction.ProductModels.productSpace.obj X)
        (((Cohomology.Singular.Functor.singularPullback (ModuleCat.of k k) (TopCat.prodFst : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.1)).f p) c)
        (((Cohomology.Singular.Functor.singularPullback (ModuleCat.of k k) (TopCat.prodSnd : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.2)).f q) d)) := by
    apply Cohomology.Singular.ChainDual.chainFunctional_ext (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) (ModuleCat.of k k)
    intro s
    have hp := ConcreteCategory.congr_hom (productAw_projection k X (p + q) ⟨(p, q), rfl⟩)
      (Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) s)
    change CohomologyTensorNe.Construction.TensorProjections.projection ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.1) ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.2)
      (p + q) ⟨(p, q), rfl⟩ ((ProductAlexanderWhitney.productAw k X).f (p + q) (Cohomology.Singular.ChainDual.simplexChain (R := k) _ s)) =
      TensorProduct.map
        (((ProductModelsAs.Construction.ProductModels.scalarChains k).map (TopCat.prodFst : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.1)).f p).hom
        (((ProductModelsAs.Construction.ProductModels.scalarChains k).map (TopCat.prodSnd : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.2)).f q).hom
        (AlexanderWhitney.Construction.AlexanderWhitneyComponents.component (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) p q (Cohomology.Singular.ChainDual.simplexChain (R := k) _ s)) at hp
    change TensorCocycles.pairing _ _ (CohomologyTensorNe.Construction.TensorProjections.projection ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.1)
      ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj X.2) (p + q) ⟨(p, q), rfl⟩
        ((ProductAlexanderWhitney.productAw k X).f (p + q) (Cohomology.Singular.ChainDual.simplexChain (R := k) _ s))) = _
    rw [hp, AlexanderWhitney.Construction.AlexanderWhitneyComponents.component_simplex, TensorProduct.map_tmul]
    erw [ProductModelsAs.Construction.ProductModels.scalarChains_map_simplex k (TopCat.prodFst : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.1)
        p (Products.SimplexFaceIdentities.frontFace (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) p q s),
      ProductModelsAs.Construction.ProductModels.scalarChains_map_simplex k (TopCat.prodSnd : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.2)
        q (Products.SimplexFaceIdentities.backFace (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) p q s)]
    rw [TensorCocycles.pairing_tmul]
    erw [Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_simplex (TopCat.toSSet.obj X.1) (ModuleCat.of k k) c,
      Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_simplex (TopCat.toSSet.obj X.2) (ModuleCat.of k k) d,
      Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_simplex (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) (ModuleCat.of k k)]
    change _ = Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) (ModuleCat.of k k) s
      (Products.Cup.cupWith (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) (LinearMap.mul k k)
        (((Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of k k)
          (TopCat.toSSet.map (TopCat.prodFst : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.1))).f p) c)
        (((Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of k k)
          (TopCat.toSSet.map (TopCat.prodSnd : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.2))).f q) d))
    erw [Products.Cup.evaluation_cupWith (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X))
      (M := ModuleCat.of k k) (N := ModuleCat.of k k) (L := ModuleCat.of k k)
      (p := p) (q := q) (LinearMap.mul k k)
      (((Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of k k)
        (TopCat.toSSet.map (TopCat.prodFst : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.1))).f p) c)
      (((Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of k k)
        (TopCat.toSSet.map (TopCat.prodSnd : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.2))).f q) d) s]
    erw [Cohomology.Singular.Formulas.evaluation_pullback_apply (ModuleCat.of k k)
        (TopCat.toSSet.map (TopCat.prodFst : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.1)) c
        (Products.SimplexFaceIdentities.frontFace (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) p q s),
      Cohomology.Singular.Formulas.evaluation_pullback_apply (ModuleCat.of k k)
        (TopCat.toSSet.map (TopCat.prodSnd : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.2)) d
        (Products.SimplexFaceIdentities.backFace (TopCat.toSSet.obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) p q s)]
    rfl
  exact LinearMap.congr_fun h z

end Construction.CupTensorComparison

end

end OAI.AlgebraicTopology.Kunneth.TensorAlexanderWhitney
