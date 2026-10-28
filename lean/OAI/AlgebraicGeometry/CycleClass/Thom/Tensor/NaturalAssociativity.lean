import OAI.AlgebraicGeometry.CycleClass.Thom.TripleCross
import OAI.AlgebraicTopology.Kunneth.Add

/-! # Natural Associativity -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.NaturalAssociativity

noncomputable section

section

/-! Naturality of tensor homotopies, needed for relative product supports. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open OAI.AlgebraicTopology.Kunneth.Add.Construction OAI.AlgebraicGeometry.CycleClass.Thom.TripleCross.Constructions
open scoped TensorProduct

namespace Constructions.HomotopyNaturality

variable {k : Type} [Field k]

theorem tensorHomotopyLeft_inclusion
    {A B : ChainComplex (ModuleCat.{0} k) ℕ} {f g : A ⟶ A}
    (H : Homotopy f g) (p q n : ℕ) (h : p + q = n)
    (a : A.X p) (b : B.X q) :
    (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.tensorHomotopyLeft H (𝟙 B)).hom n (n + 1)
      (ιTensorObj A B p q n h (a ⊗ₜ[k] b)) =
    ιTensorObj A B (p + 1) q (n + 1) (by omega)
      (H.hom p (p + 1) a ⊗ₜ[k] b) := by
  have hi := mapBifunctorMapHomotopy.ιMapBifunctor_hom₁ H (𝟙 B)
    (curriedTensor (ModuleCat.{0} k)) (ComplexShape.down ℕ)
    (p + 1) p q n (n + 1) h (ChainComplex.prev ℕ p)
  rw [ιMapBifunctorOrZero_eq _ _ _ _ (p + 1) q (n + 1)
    (by change p + 1 + q = n + 1; omega)] at hi
  have heps : (ComplexShape.down ℕ).ε₁ (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (p + 1, q) = 1 := rfl
  rw [heps, one_smul, HomologicalComplex.id_f, CategoryTheory.Functor.map_id,
    Category.id_comp] at hi
  exact ConcreteCategory.congr_hom hi (a ⊗ₜ[k] b)

theorem tensorHomotopyLeft_natural
    {A A' B B' : ChainComplex (ModuleCat.{0} k) ℕ}
    {f g : A ⟶ A} {f' g' : A' ⟶ A'}
    (H : Homotopy f g) (H' : Homotopy f' g') (u : A ⟶ A') (v : B ⟶ B')
    (hn : ∀ a b, u.f a ≫ H'.hom a b = H.hom a b ≫ u.f b) (n m : ℕ) :
    (u ⊗ₘ v).f n ≫ (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.tensorHomotopyLeft H' (𝟙 B')).hom n m =
      (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.tensorHomotopyLeft H (𝟙 B)).hom n m ≫ (u ⊗ₘ v).f m := by
  by_cases hm : m = n + 1
  · subst m
    apply mapBifunctor.hom_ext
    intro p q hpq
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro a b
    change (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.tensorHomotopyLeft H' (𝟙 B')).hom n (n + 1)
        ((u ⊗ₘ v).f n (ιTensorObj A B p q n hpq (a ⊗ₜ[k] b))) =
      (u ⊗ₘ v).f (n + 1)
        ((AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.tensorHomotopyLeft H (𝟙 B)).hom n (n + 1)
          (ιTensorObj A B p q n hpq (a ⊗ₜ[k] b)))
    rw [TripleCross.Constructions.tensorHom_inclusion_apply, tensorHomotopyLeft_inclusion,
      tensorHomotopyLeft_inclusion, TripleCross.Constructions.tensorHom_inclusion_apply]
    have he := ConcreteCategory.congr_hom (hn p (p + 1)) a
    change H'.hom p (p + 1) (u.f p a) = u.f (p + 1) (H.hom p (p + 1) a) at he
    rw [he]
  · have hh : ¬ (ComplexShape.down ℕ).Rel m n := by
      change ¬ n + 1 = m
      exact fun h => hm h.symm
    rw [(AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.tensorHomotopyLeft H' (𝟙 B')).zero n m hh,
      (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.tensorHomotopyLeft H (𝟙 B)).zero n m hh, comp_zero, zero_comp]

end Constructions.HomotopyNaturality

end

/-! A natural associativity homotopy, suitable for relative quotient descent. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.HomologicalComplex OAI.AlgebraicTopology.Kunneth.Add.Construction OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
open OAI.AlgebraicGeometry.CycleClass.Thom.TripleModels.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.TripleCross.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.NaturalAssociativity.Constructions.HomotopyNaturality
open scoped TensorProduct

namespace Constructions

private theorem sandwich_natural {C : Type*} [Category* C]
    {A B C₁ D A' B' C₁' D' : C}
    {f : A ⟶ B} {g : B ⟶ C₁} {h : C₁ ⟶ D}
    {f' : A' ⟶ B'} {g' : B' ⟶ C₁'} {h' : C₁' ⟶ D'}
    {u : A ⟶ A'} {v : B ⟶ B'} {w : C₁ ⟶ C₁'} {z : D ⟶ D'}
    (hf : u ≫ f' = f ≫ v) (hg : v ≫ g' = g ≫ w) (hh : w ≫ h' = h ≫ z) :
    u ≫ (f' ≫ g' ≫ h') = (f ≫ g ≫ h) ≫ z := by
  rw [← Category.assoc, hf, Category.assoc, ← Category.assoc v,
    hg, Category.assoc, hh]
  simp only [Category.assoc]

variable (k : Type) [Field k]

private theorem hasNaturalTensorRetraction : Nonempty
    (Homotopy (AlgebraicTopology.Kunneth.ComparisonLow.Construction.EilenbergZilber.cross k ≫ AlgebraicTopology.Kunneth.ComparisonLow.Construction.EilenbergZilber.aw k) (𝟙 (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.tensorChains k))) :=
  ⟨AlgebraicTopology.Kunneth.ComparisonLow.Construction.EilenbergZilber.cross_aw_homotopy k⟩

/-- Select a natural homotopy whose existence is given by the actual Eilenberg–Zilber
construction. Keeping the existence proof opaque avoids unfolding its acyclic-model
recursion when this homotopy is tensored with a third complex. -/
def naturalTensorRetraction :
    Homotopy (AlgebraicTopology.Kunneth.ComparisonLow.Construction.EilenbergZilber.cross k ≫ AlgebraicTopology.Kunneth.ComparisonLow.Construction.EilenbergZilber.aw k) (𝟙 (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.tensorChains k)) :=
  Classical.choice (hasNaturalTensorRetraction k)

def tensorRetraction (X Y : TopCat.{0}) :
    Homotopy (TripleCross.Constructions.cross k X Y ≫ TripleCross.Constructions.aw k X Y) (𝟙 (TripleCross.Constructions.chains k X ⊗ TripleCross.Constructions.chains k Y)) :=
  ((evaluation AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.SpacePair (ModuleCat.{0} k)).obj (X, Y)).mapHomotopy (naturalTensorRetraction k)

theorem tensorRetraction_natural {X X' Y Y' : TopCat.{0}}
    (f : X ⟶ X') (g : Y ⟶ Y') (a b : ℕ) :
    ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f ⊗ₘ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map g).f a ≫
        (tensorRetraction k X' Y').hom a b =
      (tensorRetraction k X Y).hom a b ≫
        ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f ⊗ₘ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map g).f b :=
  ((naturalTensorRetraction k).hom a b).naturality
    ((f, g) : (X, Y) ⟶ (X', Y'))

abbrev outerChains (X : TripleModels.Constructions.SpaceTriple) :=
  TripleCross.Constructions.chains k (TopCat.of (X.1.1 × X.1.2)) ⊗ TripleCross.Constructions.chains k X.2

def partialCross (X : TripleModels.Constructions.SpaceTriple) : TripleCross.Constructions.tensorTriple k X ⟶ outerChains k X :=
  TripleCross.Constructions.cross k X.1.1 X.1.2 ⊗ₘ 𝟙 (TripleCross.Constructions.chains k X.2)
def partialAW (X : TripleModels.Constructions.SpaceTriple) : outerChains k X ⟶ TripleCross.Constructions.tensorTriple k X :=
  TripleCross.Constructions.aw k X.1.1 X.1.2 ⊗ₘ 𝟙 (TripleCross.Constructions.chains k X.2)
def outerMap {X Y : TripleModels.Constructions.SpaceTriple} (f : X ⟶ Y) : outerChains k X ⟶ outerChains k Y :=
  (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map f.1) ⊗ₘ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f.2

theorem partialCross_natural {X Y : TripleModels.Constructions.SpaceTriple} (f : X ⟶ Y) :
    TripleCross.Constructions.tensorTripleMap k f ≫ partialCross k Y = partialCross k X ≫ outerMap k f := by
  change ((_ ⊗ₘ _) ⊗ₘ _) ≫ (_ ⊗ₘ 𝟙 _) = (_ ⊗ₘ 𝟙 _) ≫ (_ ⊗ₘ _)
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
    Category.comp_id, Category.id_comp, TripleCross.Constructions.cross_natural]
  rfl

theorem partialAW_natural {X Y : TripleModels.Constructions.SpaceTriple} (f : X ⟶ Y) :
    outerMap k f ≫ partialAW k Y = partialAW k X ≫ TripleCross.Constructions.tensorTripleMap k f := by
  change (_ ⊗ₘ _) ≫ (_ ⊗ₘ 𝟙 _) = (_ ⊗ₘ 𝟙 _) ≫ ((_ ⊗ₘ _) ⊗ₘ _)
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
    Category.comp_id, Category.id_comp]
  erw [TripleCross.Constructions.aw_natural k f.1.1 f.1.2]

theorem outerRetraction_natural {X Y : TripleModels.Constructions.SpaceTriple} (f : X ⟶ Y) (a b : ℕ) :
    (outerMap k f).f a ≫ (tensorRetraction k (TopCat.of (Y.1.1 × Y.1.2)) Y.2).hom a b =
      (tensorRetraction k (TopCat.of (X.1.1 × X.1.2)) X.2).hom a b ≫ (outerMap k f).f b :=
  ((naturalTensorRetraction k).hom a b).naturality
    ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map f.1, f.2) : (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.obj X.1, X.2) ⟶
      (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.obj Y.1, Y.2))

theorem innerRetraction_natural {X Y : TripleModels.Constructions.SpaceTriple} (f : X ⟶ Y) (a b : ℕ) :
    (TripleCross.Constructions.tensorTripleMap k f).f a ≫
      (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.tensorHomotopyLeft (tensorRetraction k Y.1.1 Y.1.2)
        (𝟙 (TripleCross.Constructions.chains k Y.2))).hom a b =
    (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.tensorHomotopyLeft (tensorRetraction k X.1.1 X.1.2)
      (𝟙 (TripleCross.Constructions.chains k X.2))).hom a b ≫ (TripleCross.Constructions.tensorTripleMap k f).f b := by
  have h := HomotopyNaturality.tensorHomotopyLeft_natural
    (tensorRetraction k X.1.1 X.1.2) (tensorRetraction k Y.1.1 Y.1.2)
    ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f.1.1 ⊗ₘ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f.1.2)
    ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map f.2) (tensorRetraction_natural k f.1.1 f.1.2) a b
  simpa only [TripleCross.Constructions.tensorTriple, TripleCross.Constructions.tensorTripleMap, TripleCross.Constructions.chains] using h

def leftRetraction (X : TripleModels.Constructions.SpaceTriple) :
    Homotopy ((TripleCross.Constructions.leftEquiv k X).hom ≫ (TripleCross.Constructions.leftEquiv k X).inv) (𝟙 (TripleCross.Constructions.tensorTriple k X)) :=
  (Homotopy.ofEq (show (TripleCross.Constructions.leftEquiv k X).hom ≫ (TripleCross.Constructions.leftEquiv k X).inv =
      (partialCross k X ≫ (TripleCross.Constructions.cross k (TopCat.of (X.1.1 × X.1.2)) X.2 ≫
        TripleCross.Constructions.aw k (TopCat.of (X.1.1 × X.1.2)) X.2)) ≫ partialAW k X from by
      change (partialCross k X ≫ TripleCross.Constructions.cross k (TopCat.of (X.1.1 × X.1.2)) X.2) ≫
        (TripleCross.Constructions.aw k (TopCat.of (X.1.1 × X.1.2)) X.2 ≫ partialAW k X) = _
      simp only [Category.assoc])).trans
    ((((tensorRetraction k (TopCat.of (X.1.1 × X.1.2)) X.2).compLeftId
      (partialCross k X)).compRight (partialAW k X)).trans
        ((Homotopy.ofEq (show partialCross k X ≫ partialAW k X =
            (TripleCross.Constructions.cross k X.1.1 X.1.2 ≫ TripleCross.Constructions.aw k X.1.1 X.1.2) ⊗ₘ 𝟙 (TripleCross.Constructions.chains k X.2) from by
            exact (tensorHom_comp_tensorHom _ _ _ _).trans (by rw [Category.id_comp]))).trans
          ((AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.tensorHomotopyLeft (tensorRetraction k X.1.1 X.1.2)
            (𝟙 (TripleCross.Constructions.chains k X.2))).trans (Homotopy.ofEq (id_tensorHom_id _ _)))))

theorem leftRetraction_hom (X : TripleModels.Constructions.SpaceTriple) (a b : ℕ) :
    (leftRetraction k X).hom a b =
      (partialCross k X).f a ≫ (tensorRetraction k (TopCat.of (X.1.1 × X.1.2)) X.2).hom a b ≫
        (partialAW k X).f b +
      (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.tensorHomotopyLeft (tensorRetraction k X.1.1 X.1.2)
        (𝟙 (TripleCross.Constructions.chains k X.2))).hom a b := by
  simp only [leftRetraction, Homotopy.trans_hom, Homotopy.ofEq_hom,
    Homotopy.compRight_hom, Homotopy.compLeftId_hom, Pi.zero_apply,
    zero_add, add_zero, Category.assoc]

theorem leftRetraction_natural {X Y : TripleModels.Constructions.SpaceTriple} (f : X ⟶ Y) (a b : ℕ) :
    (TripleCross.Constructions.tensorTripleMap k f).f a ≫ (leftRetraction k Y).hom a b =
      (leftRetraction k X).hom a b ≫ (TripleCross.Constructions.tensorTripleMap k f).f b := by
  rw [leftRetraction_hom, leftRetraction_hom, Preadditive.comp_add, Preadditive.add_comp]
  congr 1
  · have hc := HomologicalComplex.congr_hom (partialCross_natural k f) a
    have ha := HomologicalComplex.congr_hom (partialAW_natural k f) b
    simp only [HomologicalComplex.comp_f] at hc ha
    exact sandwich_natural (C := ModuleCat.{0} k)
      (f := (partialCross k X).f a) (f' := (partialCross k Y).f a)
      (g := (tensorRetraction k (TopCat.of (X.1.1 × X.1.2)) X.2).hom a b)
      (g' := (tensorRetraction k (TopCat.of (Y.1.1 × Y.1.2)) Y.2).hom a b)
      (h := (partialAW k X).f b) (h' := (partialAW k Y).f b)
      (u := (TripleCross.Constructions.tensorTripleMap k f).f a) (v := (outerMap k f).f a)
      (w := (outerMap k f).f b) (z := (TripleCross.Constructions.tensorTripleMap k f).f b)
      hc (outerRetraction_natural k f a b) ha
  · exact innerRetraction_natural k f a b

def associativity (X : TripleModels.Constructions.SpaceTriple) : Homotopy (TripleCross.Constructions.leftEquiv k X).hom (TripleCross.Constructions.rightEquiv k X).hom :=
  ((TripleCross.Constructions.comparisonHomotopy k X).compLeftId (TripleCross.Constructions.leftEquiv k X).hom).symm.trans
    ((Homotopy.ofEq (Category.assoc (TripleCross.Constructions.leftEquiv k X).hom (TripleCross.Constructions.leftEquiv k X).inv
      (TripleCross.Constructions.rightEquiv k X).hom).symm).trans
        ((leftRetraction k X).compRightId (TripleCross.Constructions.rightEquiv k X).hom))

theorem associativity_hom (X : TripleModels.Constructions.SpaceTriple) (a b : ℕ) :
    (associativity k X).hom a b =
      -((TripleCross.Constructions.leftEquiv k X).hom.f a ≫ (TripleCross.Constructions.comparisonHomotopy k X).hom a b) +
        (leftRetraction k X).hom a b ≫ (TripleCross.Constructions.rightEquiv k X).hom.f b := by
  simp only [associativity, Homotopy.trans_hom, Homotopy.symm_hom,
    Homotopy.compLeftId_hom, Homotopy.ofEq_hom, Homotopy.compRightId_hom,
    Pi.zero_apply, zero_add]

theorem associativity_natural {X Y : TripleModels.Constructions.SpaceTriple} (f : X ⟶ Y) (a b : ℕ) :
    (TripleCross.Constructions.tensorTripleMap k f).f a ≫ (associativity k Y).hom a b =
      (associativity k X).hom a b ≫ ((TripleModels.Constructions.tripleChainFunctor k).map f).f b := by
  rw [associativity_hom, associativity_hom, Preadditive.comp_add, Preadditive.add_comp,
    Preadditive.comp_neg, Preadditive.neg_comp]
  congr 1
  · congr 1
    rw [← Category.assoc, ← HomologicalComplex.comp_f, TripleCross.Constructions.leftEquiv_hom_natural,
      HomologicalComplex.comp_f, Category.assoc, TripleCross.Constructions.comparisonHomotopy_natural,
      ← Category.assoc]
  · rw [← Category.assoc, leftRetraction_natural, Category.assoc,
      ← HomologicalComplex.comp_f, TripleCross.Constructions.rightEquiv_hom_natural, HomologicalComplex.comp_f,
      ← Category.assoc]

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.NaturalAssociativity
