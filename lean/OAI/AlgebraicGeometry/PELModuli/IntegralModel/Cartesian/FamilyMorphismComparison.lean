import OAI.ArithmeticGeometry.Models.SpreadingOut.GroupReflection
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DescentCocycleChange

/-! # Family Morphism Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.FamilyMorphismComparison

noncomputable section

section

/-! Exact pullback images of the descended identity and inverse, using
the actual cartesian comparison with the covering group family. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem over_pullback_map_fst {B T : Scheme.{0}} (u : T ⟶ B)
    {X Y : Over B} (f : X ⟶ Y) :
    ((Over.pullback u).map f).left ≫ pullback.fst Y.hom u =
      pullback.fst X.hom u ≫ f.left := by
  simp only [Over.pullback_map_left, pullback.lift_fst]

variable {B T : Scheme.{0}} (u : T ⟶ B) (G : Over T) [GrpObj G]
    (A : Over B) (e : G ≅ (Over.pullback u).obj A) (q : G.left ⟶ A.left)
    (he : e.hom.left ≫ pullback.fst A.hom u = q)

include he

theorem cartesian_group_one_image (z : 𝟙_ (Over B) ⟶ A)
    (hz : u ≫ z.left = (MonObj.one : 𝟙_ (Over T) ⟶ G).left ≫ q) :
    letI : GrpObj ((Over.pullback u).obj A) := GrpObj.ofIso e
    (Over.pullback u).map z = Functor.OplaxMonoidal.η (Over.pullback u) ≫
      (MonObj.one : 𝟙_ (Over T) ⟶ (Over.pullback u).obj A) := by
  let : GrpObj ((Over.pullback u).obj A) := GrpObj.ofIso e
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change ((Over.pullback u).map z).left ≫ pullback.fst A.hom u =
      ((Functor.OplaxMonoidal.η (Over.pullback u)).left ≫
        ((MonObj.one : 𝟙_ (Over T) ⟶ G).left ≫ e.hom.left)) ≫ pullback.fst A.hom u
    rw [over_pullback_map_fst, Category.assoc, Category.assoc, he, ← hz, ← Category.assoc]
    have h : pullback.fst (𝟙 B) u = pullback.snd (𝟙 B) u ≫ u := by
      simpa only [Category.comp_id] using pullback.condition (f := 𝟙 B) (g := u)
    exact congrArg (fun k => k ≫ z.left) h
  · exact ((Over.pullback u).map z).w.trans
      (Functor.OplaxMonoidal.η (Over.pullback u) ≫
        (MonObj.one : 𝟙_ (Over T) ⟶ (Over.pullback u).obj A)).w.symm

theorem cartesian_group_inverse_image (d : A ⟶ A)
    (hd : q ≫ d.left = (GrpObj.inv : G ⟶ G).left ≫ q) :
    letI : GrpObj ((Over.pullback u).obj A) := GrpObj.ofIso e
    (Over.pullback u).map d = (GrpObj.inv : (Over.pullback u).obj A ⟶ (Over.pullback u).obj A) := by
  let : GrpObj ((Over.pullback u).obj A) := GrpObj.ofIso e
  have hi : e.inv.left ≫ q = pullback.fst A.hom u := by
    rw [← he, ← Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left, Category.id_comp]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change ((Over.pullback u).map d).left ≫ pullback.fst A.hom u =
      ((e.inv.left ≫ (GrpObj.inv : G ⟶ G).left) ≫ e.hom.left) ≫ pullback.fst A.hom u
    rw [over_pullback_map_fst, Category.assoc, he, Category.assoc, ← hd, ← Category.assoc, hi]
  · exact ((Over.pullback u).map d).w.trans
      (GrpObj.inv : (Over.pullback u).obj A ⟶ (Over.pullback u).obj A).w.symm

end

/-! The literal covering equation identifies a descended family
morphism after native pullback through the given cartesian comparisons. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem cartesian_family_morphism_comparison {S T : Scheme.{0}} (u : T ⟶ S)
    (G H : Over T) (A D : Over S)
    (eA : G ≅ (Over.pullback u).obj A) (eD : H ≅ (Over.pullback u).obj D)
    (qA : G.left ⟶ A.left) (qD : H.left ⟶ D.left)
    (hA : eA.hom.left ≫ pullback.fst A.hom u = qA)
    (hD : eD.hom.left ≫ pullback.fst D.hom u = qD)
    (m : G ⟶ H) (f : A ⟶ D) (hc : qA ≫ f.left = m.left ≫ qD) :
    eA.hom ≫ (Over.pullback u).map f = m ≫ eD.hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (eA.hom.left ≫ ((Over.pullback u).map f).left) ≫ pullback.fst D.hom u =
      (m.left ≫ eD.hom.left) ≫ pullback.fst D.hom u
    rw [Category.assoc, over_pullback_map_fst, ← Category.assoc, hA, hc, Category.assoc, hD]
  · exact (eA.hom ≫ (Over.pullback u).map f).w.trans (m ≫ eD.hom).w.symm

theorem cartesian_family_morphism_image {S T : Scheme.{0}} (u : T ⟶ S)
    (G H : Over T) (A D : Over S)
    (eA : G ≅ (Over.pullback u).obj A) (eD : H ≅ (Over.pullback u).obj D)
    (m : G ⟶ H) (f : A ⟶ D)
    (hc : eA.hom ≫ (Over.pullback u).map f = m ≫ eD.hom) :
    (Over.pullback u).map f = eA.inv ≫ m ≫ eD.hom := by
  rw [← hc]
  simp

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.FamilyMorphismComparison
