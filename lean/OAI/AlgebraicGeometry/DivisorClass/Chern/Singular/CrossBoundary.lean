import OAI.AlgebraicGeometry.DivisorClass.Chern.TensorPoint
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCrossSupport

/-! # Cross Boundary -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.CrossBoundary

noncomputable section

section

/-!
# ChernClass: the actual singular cross product with a specified point

This chain map uses the original Eilenberg–Zilber comparison. Its
naturality follows from the naturality of that comparison.
-/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type) [Field k]

def scalarPointChain (X : TopCat.{0}) (x : X) : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X).X 0 :=
  AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := k) (TopCat.toSSet.obj X) ((TopCat.toSSetObj₀Equiv (X := X)).symm x)

theorem scalarPointChain_map {X Y : TopCat.{0}} (f : X ⟶ Y) (x : X) :
    ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f).f 0 (scalarPointChain k X x) = scalarPointChain k Y (f x) := by
  rw [scalarPointChain, AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains_map_simplex]
  rfl

def singularPointCross (X Y : TopCat.{0}) (x : X) :
    (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y ⟶ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj (TopCat.of (X × Y)) :=
  TensorPoint.tensorPointChain ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X) ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y) (scalarPointChain k X x) ≫
    HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.singularChainCross k X Y

theorem singularPointCross_naturality {X X' Y Y' : TopCat.{0}}
    (f : X ⟶ X') (g : Y ⟶ Y') (x : X) :
    singularPointCross k X Y x ≫ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map
        (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (X, Y) ⟶ (X', Y'))) =
      (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map g ≫ singularPointCross k X' Y' (f x) := by
  unfold singularPointCross
  rw [Category.assoc, ← HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.singularChainCross_naturality, ← Category.assoc,
    TensorPoint.tensorPointChain_naturality, scalarPointChain_map, Category.assoc]

def pointProductInclusion (X Y : TopCat.{0}) (x : X) : Y ⟶ TopCat.of (X × Y) :=
  TopCat.ofHom ⟨fun y => (x, y), continuous_const.prodMk continuous_id⟩

def unitPointProjection (Y : TopCat.{0}) : (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y ⟶ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y :=
  singularPointCross k (TopCat.of Unit) Y () ≫ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map TopCat.prodSnd

theorem unitPointProjection_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f ≫ unitPointProjection k Y =
      unitPointProjection k X ≫ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f := by
  have hn := singularPointCross_naturality k (𝟙 (TopCat.of Unit)) f ()
  change singularPointCross k (TopCat.of Unit) X () ≫ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map
      (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((𝟙 (TopCat.of Unit), f) : (TopCat.of Unit, X) ⟶ (TopCat.of Unit, Y))) =
    (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f ≫ singularPointCross k (TopCat.of Unit) Y () at hn
  unfold unitPointProjection
  rw [← Category.assoc, ← hn, Category.assoc, ← Functor.map_comp,
    Category.assoc, ← Functor.map_comp]
  rfl

end

section

/-!
# ChernClass: boundary formulas for the original singular cross product

The cross product is the existing chain comparison. Its chain-map
equation transports the proved tensor differential, with its signs,
to actual singular chains on the product space.
-/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type) [Field k]

def singularCrossChain (X Y : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (x : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X).X p) (y : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).X q) :
    ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj (TopCat.of (X × Y))).X n :=
  (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.singularChainCross k X Y).f n
    (ιTensorObj ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X) ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y) p q n h (x ⊗ₜ[k] y))

theorem singularCrossChain_add_left (X Y : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (x x' : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X).X p) (y : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).X q) :
    singularCrossChain k X Y p q n h (x + x') y =
      singularCrossChain k X Y p q n h x y + singularCrossChain k X Y p q n h x' y := by
  simp only [singularCrossChain, TensorProduct.add_tmul, map_add]

theorem singularCrossChain_add_right (X Y : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (x : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X).X p) (y y' : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).X q) :
    singularCrossChain k X Y p q n h x (y + y') =
      singularCrossChain k X Y p q n h x y + singularCrossChain k X Y p q n h x y' := by
  simp only [singularCrossChain, TensorProduct.tmul_add, map_add]

theorem singularCrossChain_point (X Y : TopCat.{0}) (x : X) (n : ℕ)
    (y : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).X n) :
    singularCrossChain k X Y 0 n n (by omega) (scalarPointChain k X x) y =
      (singularPointCross k X Y x).f n y := rfl

theorem singularCrossChain_boundary_point (X Y : TopCat.{0}) (q : ℕ)
    (x : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X).X 0) (y : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).X (q + 1)) :
    ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj (TopCat.of (X × Y))).d (q + 1) q
      (singularCrossChain k X Y 0 (q + 1) (q + 1) (by omega) x y) =
      singularCrossChain k X Y 0 q q (by omega) x (((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).d (q + 1) q y) := by
  have h := ConcreteCategory.congr_hom ((HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.singularChainCross k X Y).comm (q + 1) q)
    (ιTensorObj ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X) ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y) 0 (q + 1) (q + 1)
      (by omega) (x ⊗ₜ[k] y))
  change _ = (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.singularChainCross k X Y).f q
    (((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X ⊗ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).d (q + 1) q _) at h
  rw [TensorBoundary.tensorBoundary_point_apply] at h
  exact h

theorem singularCrossChain_boundary_interval (X Y : TopCat.{0}) (q : ℕ)
    (x : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X).X 1) (y : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).X (q + 1)) :
    ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj (TopCat.of (X × Y))).d (1 + (q + 1)) (0 + (q + 1))
      (singularCrossChain k X Y 1 (q + 1) (1 + (q + 1)) rfl x y) =
      singularCrossChain k X Y 0 (q + 1) (0 + (q + 1)) rfl
          (((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X).d 1 0 x) y -
        singularCrossChain k X Y 1 q (0 + (q + 1)) (by omega)
          x (((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).d (q + 1) q y) := by
  have h := ConcreteCategory.congr_hom
    ((HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.singularChainCross k X Y).comm (1 + (q + 1)) (0 + (q + 1)))
    (ιTensorObj ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X) ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y) 1 (q + 1) (1 + (q + 1))
      rfl (x ⊗ₜ[k] y))
  change _ = (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.singularChainCross k X Y).f (0 + (q + 1))
    (((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X ⊗ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).d (1 + (q + 1)) (0 + (q + 1)) _) at h
  rw [TensorBoundary.tensorBoundary_interval_apply, map_sub] at h
  exact h

theorem singularCrossChain_boundary_disk (X Y : TopCat.{0}) (q : ℕ)
    (x : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X).X 2) (y : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).X (q + 1)) :
    ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj (TopCat.of (X × Y))).d (2 + (q + 1)) (1 + (q + 1))
      (singularCrossChain k X Y 2 (q + 1) (2 + (q + 1)) rfl x y) =
      singularCrossChain k X Y 1 (q + 1) (1 + (q + 1)) rfl
          (((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X).d 2 1 x) y +
        singularCrossChain k X Y 2 q (1 + (q + 1)) (by omega)
          x (((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).d (q + 1) q y) := by
  have h := ConcreteCategory.congr_hom
    ((HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.singularChainCross k X Y).comm (2 + (q + 1)) (1 + (q + 1)))
    (ιTensorObj ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X) ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y) 2 (q + 1) (2 + (q + 1))
      rfl (x ⊗ₜ[k] y))
  change _ = (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.singularChainCross k X Y).f (1 + (q + 1))
    (((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X ⊗ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).d (2 + (q + 1)) (1 + (q + 1)) _) at h
  rw [TensorBoundary.tensorBoundary_disk_apply, map_add] at h
  exact h

end

section

/-! Naturality and additive identities for the actual cross-product chain values. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type) [Field k]

theorem singularCrossChain_naturality {X X' Y Y' : TopCat.{0}}
    (f : X ⟶ X') (g : Y ⟶ Y') (p q n : ℕ) (h : p + q = n)
    (x : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X).X p) (y : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).X q) :
    ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (X, Y) ⟶ (X', Y')))).f n
      (singularCrossChain k X Y p q n h x y) =
      singularCrossChain k X' Y' p q n h
        (((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f).f p x) (((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map g).f q y) := by
  let C := (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X
  let D := (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y
  let C' := (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X'
  let D' := (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y'
  let F := (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f
  let G := (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map g
  have hn := ConcreteCategory.congr_hom
    (congrArg (fun u => u.f n) (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.singularChainCross_naturality k f g))
    (ιTensorObj C D p q n h (x ⊗ₜ[k] y))
  change (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.singularChainCross k X' Y').f n
      ((HomologicalComplex.tensorHom F G).f n (ιTensorObj C D p q n h (x ⊗ₜ[k] y))) = _ at hn
  have hi := ConcreteCategory.congr_hom
    (AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.TensorProjections.inclusion_tensorHom C D F G n ⟨(p,q),h⟩)
    (x ⊗ₜ[k] y)
  change (HomologicalComplex.tensorHom F G).f n (ιTensorObj C D p q n h _) =
    ιTensorObj C' D' p q n h (TensorProduct.map (F.f p).hom (G.f q).hom _) at hi
  rw [TensorProduct.map_tmul] at hi
  refine hn.symm.trans ?_
  exact congrArg ((HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.singularChainCross k X' Y').f n) hi

theorem singularCrossChain_zero_left (X Y : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (y : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).X q) :
    singularCrossChain k X Y p q n h 0 y = 0 := by
  simp only [singularCrossChain, TensorProduct.zero_tmul, map_zero]

theorem singularCrossChain_zero_right (X Y : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (x : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X).X p) :
    singularCrossChain k X Y p q n h x 0 = 0 := by
  simp only [singularCrossChain, TensorProduct.tmul_zero, map_zero]

theorem singularCrossChain_sub_left (X Y : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (x x' : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X).X p) (y : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).X q) :
    singularCrossChain k X Y p q n h (x - x') y =
      singularCrossChain k X Y p q n h x y - singularCrossChain k X Y p q n h x' y := by
  simp only [singularCrossChain, TensorProduct.sub_tmul, map_sub]

theorem singularCrossChain_sub_right (X Y : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (x : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X).X p) (y y' : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).X q) :
    singularCrossChain k X Y p q n h x (y - y') =
      singularCrossChain k X Y p q n h x y - singularCrossChain k X Y p q n h x y' := by
  simp only [singularCrossChain, TensorProduct.tmul_sub, map_sub]

end

/-!
# ChernClass: cross-product boundary formulas at specified total degrees

Only equalities of natural-number degrees are transported. The chains,
the comparison map, and the differential signs are unchanged.
-/

open _root_.CategoryTheory OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type) [Field k]

theorem singularCrossChain_boundary_interval_at (X Y : TopCat.{0}) (q n m : ℕ)
    (hn : 1 + (q + 1) = n) (hm : 0 + (q + 1) = m)
    (x : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X).X 1) (y : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).X (q + 1)) :
    ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj (TopCat.of (X × Y))).d n m
      (singularCrossChain k X Y 1 (q + 1) n hn x y) =
      singularCrossChain k X Y 0 (q + 1) m hm (((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X).d 1 0 x) y -
        singularCrossChain k X Y 1 q m (by omega) x (((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).d (q + 1) q y) := by
  subst n m
  exact singularCrossChain_boundary_interval k X Y q x y

theorem singularCrossChain_boundary_disk_at (X Y : TopCat.{0}) (q n m : ℕ)
    (hn : 2 + (q + 1) = n) (hm : 1 + (q + 1) = m)
    (x : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X).X 2) (y : ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).X (q + 1)) :
    ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj (TopCat.of (X × Y))).d n m
      (singularCrossChain k X Y 2 (q + 1) n hn x y) =
      singularCrossChain k X Y 1 (q + 1) m hm (((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj X).d 2 1 x) y +
        singularCrossChain k X Y 2 q m (by omega) x (((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).obj Y).d (q + 1) q y) := by
  subst n m
  exact singularCrossChain_boundary_disk k X Y q x y

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.CrossBoundary
