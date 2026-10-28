import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Extensive

/-! # Partition Base Maps -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.PartitionBaseMaps

noncomputable section

section

/-! Products with a fixed scheme over the base preserve a finite
disjoint decomposition of the parameter scheme. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace FiniteBasePartition
variable {S : Scheme.{0}} {I : Type} [Finite I]
    (U : I → Over S) (T : Over S) (j : ∀ i, U i ⟶ T)
    (H : IsColimit (Cofan.mk T.left (fun i => (j i).left)))

def productCofanIsColimit (X : Over S) :
    IsColimit (Cofan.mk (T ⨯ X).left (fun i => (prod.map (j i) (𝟙 X)).left)) := by
  have hP (V : Over S) : IsPullback (prod.snd : V ⨯ X ⟶ X).left
      (prod.fst : V ⨯ X ⟶ V).left X.hom V.hom :=
    (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd V X)).flip
  let h := FinitaryPreExtensive.isUniversal_finiteCoproducts H
  apply Classical.choice
  refine h.nonempty_isColimit_of_isPullback_left (fun i => (U i).hom) T.hom X.hom
    (fun i => (prod.snd : U i ⨯ X ⟶ X).left)
    (fun i => (prod.fst : U i ⨯ X ⟶ U i).left) (fun i => hP (U i)) (hP T)
    (Cofan.mk (T ⨯ X).left (fun i => (prod.map (j i) (𝟙 X)).left)) (Iso.refl _) ?_ ?_ ?_
  · exact fun i => (j i).w
  · intro i
    change (prod.map (j i) (𝟙 X)).left ≫ (prod.snd : T ⨯ X ⟶ X).left = _
    rw [← Over.comp_left, prod.map_snd, Category.comp_id]
  · intro i
    change (prod.map (j i) (𝟙 X)).left ≫ (prod.fst : T ⨯ X ⟶ T).left = _
    rw [← Over.comp_left, prod.map_fst, Over.comp_left]
    rfl

include H in
theorem product_hom_ext (X Y : Over S) (f g : T ⨯ X ⟶ Y)
    (h : ∀ i, prod.map (j i) (𝟙 X) ≫ f = prod.map (j i) (𝟙 X) ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  apply Cofan.IsColimit.hom_ext (productCofanIsColimit U T j H X)
  intro i
  exact congrArg Over.Hom.left (h i)

def glue (X Y : Over S) (f : ∀ i, U i ⨯ X ⟶ Y) : T ⨯ X ⟶ Y := by
  let C := productCofanIsColimit U T j H X
  let m := Cofan.IsColimit.desc C (fun i => (f i).left)
  refine Over.homMk m ?_
  apply Cofan.IsColimit.hom_ext C
  intro i
  change (prod.map (j i) (𝟙 X)).left ≫ (m ≫ Y.hom) =
    (prod.map (j i) (𝟙 X)).left ≫ (T ⨯ X).hom
  have hm : (prod.map (j i) (𝟙 X)).left ≫ m = (f i).left :=
    Cofan.IsColimit.fac C (fun i => (f i).left) i
  rw [← Category.assoc, hm]
  exact (f i).w.trans (prod.map (j i) (𝟙 X)).w.symm

theorem glue_restrict (X Y : Over S) (f : ∀ i, U i ⨯ X ⟶ Y) (i : I) :
    prod.map (j i) (𝟙 X) ≫ glue U T j H X Y f = f i := by
  apply Over.OverMorphism.ext
  exact Cofan.IsColimit.fac (productCofanIsColimit U T j H X) (fun i => (f i).left) i

end FiniteBasePartition

end

/-! Maps out of a finite disjoint parameter decomposition glue over the
original base, with their exact component restrictions. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace FiniteBasePartition
variable {S : Scheme.{0}} {I : Type}
    (U : I → Over S) (T : Over S) (j : ∀ i, U i ⟶ T)
    (H : IsColimit (Cofan.mk T.left (fun i => (j i).left)))

include H in
theorem base_hom_ext (Y : Over S) (f g : T ⟶ Y)
    (h : ∀ i, j i ≫ f = j i ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  apply Cofan.IsColimit.hom_ext H
  exact fun i => congrArg Over.Hom.left (h i)

def glueBase (Y : Over S) (f : ∀ i, U i ⟶ Y) : T ⟶ Y := by
  let m := Cofan.IsColimit.desc H (fun i => (f i).left)
  refine Over.homMk m ?_
  apply Cofan.IsColimit.hom_ext H
  intro i
  have hm : (j i).left ≫ m = (f i).left := Cofan.IsColimit.fac H (fun i => (f i).left) i
  change (j i).left ≫ (m ≫ Y.hom) = (j i).left ≫ T.hom
  rw [← Category.assoc, hm]
  exact (f i).w.trans (j i).w.symm

theorem glueBase_restrict (Y : Over S) (f : ∀ i, U i ⟶ Y) (i : I) :
    j i ≫ glueBase U T j H Y f = f i := by
  apply Over.OverMorphism.ext
  exact Cofan.IsColimit.fac H (fun i => (f i).left) i

end FiniteBasePartition

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.PartitionBaseMaps
