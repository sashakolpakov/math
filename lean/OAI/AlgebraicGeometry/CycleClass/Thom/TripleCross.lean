import OAI.AlgebraicGeometry.CycleClass.Thom.TripleModels
import OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.Associator

/-! # Triple Cross -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TripleCross

noncomputable section

section

/-! Associativity comparison for the actual Eilenberg–Zilber cross map. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicTopology _root_.HomologicalComplex
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
open OAI.AlgebraicGeometry.CycleClass.Thom.TripleModels.Constructions
open scoped Simplicial TensorProduct

namespace Constructions

variable (k : Type) [Field k]

abbrev chains (X : TopCat.{0}) := (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X
def cross (X Y : TopCat.{0}) := (AlgebraicTopology.Kunneth.ComparisonLow.Construction.EilenbergZilber.homotopyEquiv k X Y).hom
def aw (X Y : TopCat.{0}) := (AlgebraicTopology.Kunneth.ComparisonLow.Construction.EilenbergZilber.homotopyEquiv k X Y).inv

@[reassoc]
theorem cross_natural {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y') :
    ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f ⊗ₘ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map g) ≫ cross k X' Y' =
      cross k X Y ≫ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map
        (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (X, Y) ⟶ (X', Y'))) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact ((AlgebraicTopology.Kunneth.ComparisonLow.Construction.EilenbergZilber.cross k).f n).naturality ((f, g) : (X, Y) ⟶ (X', Y'))

@[reassoc]
theorem aw_natural {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y') :
    (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (X, Y) ⟶ (X', Y'))) ≫ aw k X' Y' =
      aw k X Y ≫ ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f ⊗ₘ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map g) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact ((AlgebraicTopology.Kunneth.ComparisonLow.Construction.EilenbergZilber.aw k).f n).naturality ((f, g) : (X, Y) ⟶ (X', Y'))

def spaceAssociate (X : TripleModels.Constructions.SpaceTriple) :
    TopCat.of ((X.1.1 × X.1.2) × X.2) ≅ TopCat.of (X.1.1 × (X.1.2 × X.2)) :=
  TopCat.isoOfHomeo (Homeomorph.prodAssoc X.1.1 X.1.2 X.2)

abbrev tensorTriple (X : TripleModels.Constructions.SpaceTriple) :=
  (chains k X.1.1 ⊗ chains k X.1.2) ⊗ chains k X.2

def tensorTripleMap {X Y : TripleModels.Constructions.SpaceTriple} (f : X ⟶ Y) :
    tensorTriple k X ⟶ tensorTriple k Y :=
  ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f.1.1 ⊗ₘ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f.1.2) ⊗ₘ
    (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f.2

def leftEquiv (X : TripleModels.Constructions.SpaceTriple) :
    HomotopyEquiv (tensorTriple k X) ((TripleModels.Constructions.tripleChainFunctor k).obj X) :=
  (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.tensorHomotopyEquiv
    (AlgebraicTopology.Kunneth.ComparisonLow.Construction.EilenbergZilber.homotopyEquiv k X.1.1 X.1.2)
    (HomotopyEquiv.refl (chains k X.2))).trans
      (AlgebraicTopology.Kunneth.ComparisonLow.Construction.EilenbergZilber.homotopyEquiv k (TopCat.of (X.1.1 × X.1.2)) X.2)

def rightEquiv (X : TripleModels.Constructions.SpaceTriple) :
    HomotopyEquiv (tensorTriple k X) ((TripleModels.Constructions.tripleChainFunctor k).obj X) :=
  (HomotopyEquiv.ofIso (α_ (chains k X.1.1) (chains k X.1.2) (chains k X.2))).trans
    ((AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.tensorHomotopyEquiv (HomotopyEquiv.refl (chains k X.1.1))
      (AlgebraicTopology.Kunneth.ComparisonLow.Construction.EilenbergZilber.homotopyEquiv k X.1.2 X.2)).trans
      ((AlgebraicTopology.Kunneth.ComparisonLow.Construction.EilenbergZilber.homotopyEquiv k X.1.1 (TopCat.of (X.1.2 × X.2))).trans
        (HomotopyEquiv.ofIso ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).mapIso (spaceAssociate X).symm))))

theorem leftEquiv_inv_eq (X : TripleModels.Constructions.SpaceTriple) : (leftEquiv k X).inv =
    aw k (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.obj X.1) X.2 ≫ (aw k X.1.1 X.1.2 ⊗ₘ 𝟙 (chains k X.2)) := rfl

theorem rightEquiv_hom_eq (X : TripleModels.Constructions.SpaceTriple) : (rightEquiv k X).hom =
    (α_ (chains k X.1.1) (chains k X.1.2) (chains k X.2)).hom ≫
      (𝟙 (chains k X.1.1) ⊗ₘ cross k X.1.2 X.2) ≫
        cross k X.1.1 (TopCat.of (X.1.2 × X.2)) ≫
          (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map (spaceAssociate X).inv := rfl

theorem leftEquiv_hom_natural {X Y : TripleModels.Constructions.SpaceTriple} (f : X ⟶ Y) :
    tensorTripleMap k f ≫ (leftEquiv k Y).hom =
      (leftEquiv k X).hom ≫ (TripleModels.Constructions.tripleChainFunctor k).map f := by
  change ((_ ⊗ₘ _) ⊗ₘ _) ≫ ((cross k _ _ ⊗ₘ 𝟙 _) ≫ cross k _ _) =
    ((cross k _ _ ⊗ₘ 𝟙 _) ≫ cross k _ _) ≫ _
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, cross_natural]
  rw [← Category.id_comp ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f.2), ← tensorHom_comp_tensorHom]
  rw [Category.assoc]
  erw [cross_natural k (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map f.1) f.2]
  rw [← Category.assoc]
  rfl

theorem leftEquiv_inv_natural {X Y : TripleModels.Constructions.SpaceTriple} (f : X ⟶ Y) :
    (TripleModels.Constructions.tripleChainFunctor k).map f ≫ (leftEquiv k Y).inv =
      (leftEquiv k X).inv ≫ tensorTripleMap k f := by
  change (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map
      ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map f.1, f.2) : (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.obj X.1, X.2) ⟶
        (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.obj Y.1, Y.2))) ≫
      (aw k _ _ ≫ (aw k _ _ ⊗ₘ 𝟙 _)) =
    (aw k _ _ ≫ (aw k _ _ ⊗ₘ 𝟙 _)) ≫ ((_ ⊗ₘ _) ⊗ₘ _)
  rw [← Category.assoc, aw_natural, Category.assoc, tensorHom_comp_tensorHom,
    Category.comp_id]
  erw [aw_natural k f.1.1 f.1.2]
  rw [← Category.id_comp ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f.2), ← tensorHom_comp_tensorHom,
    ← Category.assoc]
  simp only [Category.id_comp]
  rfl

theorem rightEquiv_hom_natural {X Y : TripleModels.Constructions.SpaceTriple} (f : X ⟶ Y) :
    tensorTripleMap k f ≫ (rightEquiv k Y).hom =
      (rightEquiv k X).hom ≫ (TripleModels.Constructions.tripleChainFunctor k).map f := by
  change ((_ ⊗ₘ _) ⊗ₘ _) ≫ ((α_ _ _ _).hom ≫
      ((𝟙 _ ⊗ₘ cross k _ _) ≫ (cross k _ _ ≫ _))) =
    ((α_ _ _ _).hom ≫ ((𝟙 _ ⊗ₘ cross k _ _) ≫ (cross k _ _ ≫ _))) ≫ _
  rw [← Category.assoc, associator_naturality, Category.assoc,
    ← Category.assoc (_ ⊗ₘ _), tensorHom_comp_tensorHom, Category.comp_id,
    cross_natural]
  rw [← Category.id_comp ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f.1.1), ← tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  erw [cross_natural_assoc k f.1.1
    (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f.1.2, f.2) : (X.1.2, X.2) ⟶ (Y.1.2, Y.2)))]
  dsimp only [HomotopyEquiv.ofIso, Functor.mapIso, Iso.symm_hom,
    TripleModels.Constructions.tripleChainFunctor, Functor.comp_map]
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

def comparison (X : TripleModels.Constructions.SpaceTriple) :
    ((TripleModels.Constructions.tripleChainFunctor k).obj X) ⟶ ((TripleModels.Constructions.tripleChainFunctor k).obj X) :=
  (leftEquiv k X).inv ≫ (rightEquiv k X).hom

def naturalComparison : TripleModels.Constructions.tripleChains k ⟶ TripleModels.Constructions.tripleChains k where
  f n :=
    { app X := (comparison k X).f n
      naturality X Y f := by
        have hn : (TripleModels.Constructions.tripleChainFunctor k).map f ≫ comparison k Y =
            comparison k X ≫ (TripleModels.Constructions.tripleChainFunctor k).map f := by
          unfold comparison
          rw [← Category.assoc, leftEquiv_inv_natural, Category.assoc,
            rightEquiv_hom_natural, ← Category.assoc]
        exact congrArg (fun u => u.f n) hn }
  comm' i j _ := by
    apply NatTrans.ext
    funext X
    exact (comparison k X).comm i j

theorem cross_vertex (X Y : TopCat.{0})
    (s : (TopCat.toSSet.obj X) _⦋0⦌) (t : (TopCat.toSSet.obj Y) _⦋0⦌) :
    (cross k X Y).f 0
      (ιTensorObj (chains k X) (chains k Y) 0 0 0 rfl
        (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X) s ⊗ₜ[k]
          AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj Y) t)) =
      AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj (TopCat.of (X × Y)))
        (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 0 (X, Y) s t) :=
  AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.zeroComparison_simplex (X, Y) s t

theorem aw_vertex (X Y : TopCat.{0})
    (s : (TopCat.toSSet.obj X) _⦋0⦌) (t : (TopCat.toSSet.obj Y) _⦋0⦌) :
    (aw k X Y).f 0
      (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj (TopCat.of (X × Y)))
        (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 0 (X, Y) s t)) =
      ιTensorObj (chains k X) (chains k Y) 0 0 0 rfl
        (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X) s ⊗ₜ[k]
          AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj Y) t) := by
  have h := congrArg ((aw k X Y).f 0) (cross_vertex k X Y s t)
  have hi := ConcreteCategory.congr_hom
    (congrArg (fun u => u.app (X, Y)) (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.zeroComparison k).hom_inv_id)
    (ιTensorObj (chains k X) (chains k Y) 0 0 0 rfl
      (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X) s ⊗ₜ[k]
        AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj Y) t))
  exact h.symm.trans hi

theorem tensorHom_inclusion_apply
    {A B C D : ChainComplex (ModuleCat.{0} k) ℕ}
    (f : A ⟶ C) (g : B ⟶ D) (p q n : ℕ) (h : p + q = n)
    (a : A.X p) (b : B.X q) :
    (f ⊗ₘ g).f n (ιTensorObj A B p q n h (a ⊗ₜ[k] b)) =
      ιTensorObj C D p q n h (f.f p a ⊗ₜ[k] g.f q b) := by
  have hi := ι_mapBifunctorMap f g (curriedTensor (ModuleCat.{0} k))
    (ComplexShape.down ℕ) p q n h
  exact ConcreteCategory.congr_hom hi (a ⊗ₜ[k] b)

theorem comparison_vertex (X : TripleModels.Constructions.SpaceTriple)
    (s : (TopCat.toSSet.obj X.1.1) _⦋0⦌)
    (t : (TopCat.toSSet.obj X.1.2) _⦋0⦌)
    (u : (TopCat.toSSet.obj X.2) _⦋0⦌) :
    (comparison k X).f 0
      (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj (TripleModels.Constructions.tripleSpace.obj X))
        (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 0 (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.obj X.1, X.2)
          (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 0 X.1 s t) u)) =
      AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj (TripleModels.Constructions.tripleSpace.obj X))
        (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 0 (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.obj X.1, X.2)
          (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 0 X.1 s t) u) := by
  rw [comparison, leftEquiv_inv_eq, rightEquiv_hom_eq]
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
  erw [aw_vertex k (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.obj X.1) X.2 (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 0 X.1 s t) u]
  erw [tensorHom_inclusion_apply k (aw k X.1.1 X.1.2) (𝟙 (chains k X.2)) 0 0 0 rfl]
  erw [aw_vertex k X.1.1 X.1.2 s t]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
  erw [Tensor.Associator.Constructions.associator_hom_tensor
    (chains k X.1.1) (chains k X.1.2) (chains k X.2) 0 0 0 0 rfl]
  erw [tensorHom_inclusion_apply k (𝟙 (chains k X.1.1)) (cross k X.1.2 X.2) 0 0 0 rfl]
  erw [cross_vertex k X.1.2 X.2 t u]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
  erw [cross_vertex k X.1.1 (TopCat.of (X.1.2 × X.2)) s
    (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 0 (X.1.2, X.2) t u)]
  erw [AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains_map_simplex k (spaceAssociate X).inv 0]
  rfl

theorem naturalComparison_zero : (naturalComparison k).f 0 = 𝟙 ((TripleModels.Constructions.tripleChains k).X 0) := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply AlgebraicTopology.Cohomology.Singular.ChainDual.chainFunctional_ext (TopCat.toSSet.obj (TripleModels.Constructions.tripleSpace.obj X))
    (((TripleModels.Constructions.tripleChainFunctor k).obj X).X 0)
  intro v
  let s := ULift.up (v.down ≫ TopCat.prodFst ≫ TopCat.prodFst)
  let t := ULift.up (v.down ≫ TopCat.prodFst ≫ TopCat.prodSnd)
  let u := ULift.up (v.down ≫ TopCat.prodSnd)
  have hv : AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 0 (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.obj X.1, X.2)
      (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 0 X.1 s t) u = v := by
    apply ULift.ext
    apply TopCat.ext
    intro z
    rfl
  change (comparison k X).f 0 (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := k) _ v) = AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := k) _ v
  simpa only [hv] using comparison_vertex k X s t u

def naturalComparisonHomotopy : Homotopy (naturalComparison k) (𝟙 (TripleModels.Constructions.tripleChains k)) :=
  TripleModels.Constructions.tripleNaturalHomotopy k _ _ (naturalComparison_zero k)

def comparisonHomotopy (X : TripleModels.Constructions.SpaceTriple) :
    Homotopy (comparison k X) (𝟙 ((TripleModels.Constructions.tripleChainFunctor k).obj X)) :=
  ((evaluation TripleModels.Constructions.SpaceTriple (ModuleCat.{0} k)).obj X).mapHomotopy
    (naturalComparisonHomotopy k)

theorem comparisonHomotopy_natural {X Y : TripleModels.Constructions.SpaceTriple} (f : X ⟶ Y) (a b : ℕ) :
    ((TripleModels.Constructions.tripleChainFunctor k).map f).f a ≫ (comparisonHomotopy k Y).hom a b =
      (comparisonHomotopy k X).hom a b ≫ ((TripleModels.Constructions.tripleChainFunctor k).map f).f b :=
  ((naturalComparisonHomotopy k).hom a b).naturality f

/-- The two actual iterated cross maps are chain homotopic, with the native
tensor associator and the usual reassociation of cartesian products. -/
def crossAssociativity (X : TripleModels.Constructions.SpaceTriple) :
    Homotopy (leftEquiv k X).hom (rightEquiv k X).hom :=
  ((comparisonHomotopy k X).compLeftId (leftEquiv k X).hom).symm.trans
    ((Homotopy.ofEq (Category.assoc (leftEquiv k X).hom (leftEquiv k X).inv
      (rightEquiv k X).hom).symm).trans
        ((leftEquiv k X).homotopyHomInvId.compRightId (rightEquiv k X).hom))

end Constructions

end

/-! The actual homogeneous summands in a three-factor tensor complex. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.HomologicalComplex OAI.AlgebraicGeometry.CycleClass.Thom.TripleCross.Constructions
open scoped TensorProduct

namespace Constructions.TensorDegree

variable {k : Type} [Field k]

abbrev tripleInclusion (A B C : ChainComplex (ModuleCat.{0} k) ℕ)
    (p q r n : ℕ) (h : (p + q) + r = n) :
    (A.X p ⊗ B.X q) ⊗ C.X r ⟶ ((A ⊗ B) ⊗ C).X n :=
  mapBifunctor₁₂.ι (curriedTensor (ModuleCat.{0} k)) (curriedTensor (ModuleCat.{0} k))
    A B C (ComplexShape.down ℕ) (ComplexShape.down ℕ) p q r n h

theorem tripleInclusion_apply (A B C : ChainComplex (ModuleCat.{0} k) ℕ)
    (p q r n : ℕ) (h : (p + q) + r = n) (x : A.X p ⊗[k] B.X q) (z : C.X r) :
    tripleInclusion A B C p q r n h (x ⊗ₜ[k] z) =
      ιTensorObj (A ⊗ B) C (p + q) r n h
        (ιTensorObj A B p q (p + q) rfl x ⊗ₜ[k] z) := by
  rw [tripleInclusion, mapBifunctor₁₂.ι_eq _ _ _ _ _ _ _ p q r (p + q) n rfl h]
  rfl

theorem tripleInclusion_natural
    {A B C A' B' C' : ChainComplex (ModuleCat.{0} k) ℕ}
    (f : A ⟶ A') (g : B ⟶ B') (u : C ⟶ C') (p q r n : ℕ) (h : (p + q) + r = n) :
    tripleInclusion A B C p q r n h ≫ ((f ⊗ₘ g) ⊗ₘ u).f n =
      ((f.f p ⊗ₘ g.f q) ⊗ₘ u.f r) ≫ tripleInclusion A' B' C' p q r n h := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x z
  change ((f ⊗ₘ g) ⊗ₘ u).f n (tripleInclusion A B C p q r n h (x ⊗ₜ[k] z)) =
    tripleInclusion A' B' C' p q r n h ((f.f p ⊗ₘ g.f q) x ⊗ₜ[k] u.f r z)
  rw [tripleInclusion_apply, tensorHom_inclusion_apply, tripleInclusion_apply]
  have hi := ι_mapBifunctorMap f g (curriedTensor (ModuleCat.{0} k))
    (ComplexShape.down ℕ) p q (p + q) rfl
  have hi' : ιTensorObj A B p q (p + q) rfl ≫ (f ⊗ₘ g).f (p + q) =
      (f.f p ⊗ₘ g.f q) ≫ ιTensorObj A' B' p q (p + q) rfl := by
    rw [tensorHom_def (f.f p) (g.f q), Category.assoc]
    exact hi
  have hx : (f ⊗ₘ g).f (p + q) (ιTensorObj A B p q (p + q) rfl x) =
      ιTensorObj A' B' p q (p + q) rfl ((f.f p ⊗ₘ g.f q) x) :=
    ConcreteCategory.congr_hom hi' x
  rw [hx]

def tripleDegreeDesc (A B C : ChainComplex (ModuleCat.{0} k) ℕ) (n : ℕ)
    {M : ModuleCat.{0} k}
    (f : ∀ p q r (_h : (p + q) + r = n), (A.X p ⊗ B.X q) ⊗ C.X r ⟶ M) :
    ((A ⊗ B) ⊗ C).X n ⟶ M :=
  mapBifunctor₁₂.mapBifunctor₁₂Desc f

theorem tripleDegreeDesc_fac (A B C : ChainComplex (ModuleCat.{0} k) ℕ) (n : ℕ)
    {M : ModuleCat.{0} k}
    (f : ∀ p q r (_h : (p + q) + r = n), (A.X p ⊗ B.X q) ⊗ C.X r ⟶ M)
    (p q r : ℕ) (h : (p + q) + r = n) :
    tripleInclusion A B C p q r n h ≫ tripleDegreeDesc A B C n f = f p q r h :=
  mapBifunctor₁₂.ι_mapBifunctor₁₂Desc
    (F₁₂ := curriedTensor (ModuleCat.{0} k)) (G := curriedTensor (ModuleCat.{0} k))
    (K₁ := A) (K₂ := B) (K₃ := C) (c₁₂ := ComplexShape.down ℕ)
    (c₄ := ComplexShape.down ℕ) f p q r h

theorem tripleDegree_hom_ext (A B C : ChainComplex (ModuleCat.{0} k) ℕ) (n : ℕ)
    {M : ModuleCat.{0} k} {f g : ((A ⊗ B) ⊗ C).X n ⟶ M}
    (h : ∀ p q r (hpqr : (p + q) + r = n),
      tripleInclusion A B C p q r n hpqr ≫ f = tripleInclusion A B C p q r n hpqr ≫ g) :
    f = g :=
  mapBifunctor₁₂.hom_ext h

end Constructions.TensorDegree

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TripleCross
