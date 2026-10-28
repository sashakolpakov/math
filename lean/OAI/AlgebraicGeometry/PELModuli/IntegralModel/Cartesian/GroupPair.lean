import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.FamilyMorphismComparison
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Group Pair -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.GroupPair

noncomputable section

section

/-! Identify the cover of the quotient's relative square with the
product comparison induced by its actual cartesian family isomorphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

theorem cartesian_group_pair_comparison {B T : Scheme.{0}} (u : T ⟶ B)
    (G : Over T) (A : Over B) (e : G ≅ (Over.pullback u).obj A)
    (q : G.left ⟶ A.left) (he : e.hom.left ≫ pullback.fst A.hom u = q)
    (qp : (G ⊗ G).left ⟶ (A ⊗ A).left)
    (h₁ : qp ≫ (fst A A).left = (fst G G).left ≫ q)
    (h₂ : qp ≫ (snd A A).left = (snd G G).left ≫ q) :
    (Functor.OplaxMonoidal.δ (Over.pullback u) A A ≫ (e.inv ⊗ₘ e.inv)).left ≫ qp =
      pullback.fst (A ⊗ A).hom u := by
  let F := Over.pullback u
  let l := Functor.OplaxMonoidal.δ F A A ≫ (e.inv ⊗ₘ e.inv)
  have hi : e.inv.left ≫ q = pullback.fst A.hom u := by
    rw [← he, ← Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left, Category.id_comp]
  have hl₁ : l.left ≫ (fst G G).left = (F.map (fst A A)).left ≫ e.inv.left := by
    change (l ≫ fst G G).left = (F.map (fst A A) ≫ e.inv).left
    apply congrArg Over.Hom.left
    change (Functor.OplaxMonoidal.δ F A A ≫ (e.inv ⊗ₘ e.inv)) ≫ fst G G = _
    rw [Category.assoc, tensorHom_fst, ← Category.assoc, Functor.OplaxMonoidal.δ_fst]
  have hl₂ : l.left ≫ (snd G G).left = (F.map (snd A A)).left ≫ e.inv.left := by
    change (l ≫ snd G G).left = (F.map (snd A A) ≫ e.inv).left
    apply congrArg Over.Hom.left
    change (Functor.OplaxMonoidal.δ F A A ≫ (e.inv ⊗ₘ e.inv)) ≫ snd G G = _
    rw [Category.assoc, tensorHom_snd, ← Category.assoc, Functor.OplaxMonoidal.δ_snd]
  change qp ≫ pullback.fst A.hom A.hom = (fst G G).left ≫ q at h₁
  change qp ≫ pullback.snd A.hom A.hom = (snd G G).left ≫ q at h₂
  apply pullback.hom_ext
  · change (l.left ≫ qp) ≫ pullback.fst A.hom A.hom = _
    rw [Category.assoc, h₁, ← Category.assoc, hl₁, Category.assoc, hi]
    exact FamilyMorphismComparison.over_pullback_map_fst u (fst A A)
  · change (l.left ≫ qp) ≫ pullback.snd A.hom A.hom = _
    rw [Category.assoc, h₂, ← Category.assoc, hl₂, Category.assoc, hi]
    exact FamilyMorphismComparison.over_pullback_map_fst u (snd A A)

end

section

/-! Identify multiplication after pullback with the actual covering
group family's multiplication. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem cartesian_group_multiplication_image {B T : Scheme.{0}} (u : T ⟶ B)
    (G : Over T) [GrpObj G] (A : Over B) (e : G ≅ (Over.pullback u).obj A)
    (q : G.left ⟶ A.left) (he : e.hom.left ≫ pullback.fst A.hom u = q)
    (qp : (G ⊗ G).left ⟶ (A ⊗ A).left)
    (h₁ : qp ≫ (fst A A).left = (fst G G).left ≫ q)
    (h₂ : qp ≫ (snd A A).left = (snd G G).left ≫ q)
    (m : A ⊗ A ⟶ A) (hm : qp ≫ m.left = (MonObj.mul : G ⊗ G ⟶ G).left ≫ q) :
    letI : GrpObj ((Over.pullback u).obj A) := GrpObj.ofIso e
    (Over.pullback u).map m = Functor.OplaxMonoidal.δ (Over.pullback u) A A ≫
      (MonObj.mul : (Over.pullback u).obj A ⊗ (Over.pullback u).obj A ⟶ (Over.pullback u).obj A) := by
  let : GrpObj ((Over.pullback u).obj A) := GrpObj.ofIso e
  let F := Over.pullback u
  let l := Functor.OplaxMonoidal.δ F A A ≫ (e.inv ⊗ₘ e.inv)
  have hl : l.left ≫ qp = pullback.fst (A ⊗ A).hom u :=
    cartesian_group_pair_comparison u G A e q he qp h₁ h₂
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (F.map m).left ≫ pullback.fst A.hom u =
      ((Functor.OplaxMonoidal.δ F A A).left ≫
        (((e.inv ⊗ₘ e.inv).left ≫ (MonObj.mul : G ⊗ G ⟶ G).left) ≫ e.hom.left)) ≫
          pullback.fst A.hom u
    rw [FamilyMorphismComparison.over_pullback_map_fst, Category.assoc, Category.assoc, he]
    change _ = l.left ≫ ((MonObj.mul : G ⊗ G ⟶ G).left ≫ q)
    rw [← hm, ← Category.assoc, hl]
  · exact (F.map m).w.trans
      (Functor.OplaxMonoidal.δ F A A ≫
        (MonObj.mul : F.obj A ⊗ F.obj A ⟶ F.obj A)).w.symm

end

/-! All commutative group laws descend from the constructed operations
and their actual cartesian covering-family equations. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem commutative_group_descends_from_cartesian_operations {B T : Scheme.{0}}
    (u : T ⟶ B) [Flat u] [Surjective u] [LocallyOfFinitePresentation u]
    (G : Over T) [GrpObj G] [IsCommMonObj G] (A : Over B)
    (e : G ≅ (Over.pullback u).obj A)
    (q : G.left ⟶ A.left) (he : e.hom.left ≫ pullback.fst A.hom u = q)
    (qp : (G ⊗ G).left ⟶ (A ⊗ A).left)
    (h₁ : qp ≫ (fst A A).left = (fst G G).left ≫ q)
    (h₂ : qp ≫ (snd A A).left = (snd G G).left ≫ q)
    (z : 𝟙_ (Over B) ⟶ A) (m : A ⊗ A ⟶ A) (d : A ⟶ A)
    (hz : u ≫ z.left = (MonObj.one : 𝟙_ (Over T) ⟶ G).left ≫ q)
    (hm : qp ≫ m.left = (MonObj.mul : G ⊗ G ⟶ G).left ≫ q)
    (hd : q ≫ d.left = (GrpObj.inv : G ⟶ G).left ≫ q) :
    ∃ gA : GrpObj A, (letI := gA; IsCommMonObj A) ∧
      (letI := gA; IsMonHom e.hom) := by
  let F := Over.pullback u
  let : GrpObj (F.obj A) := GrpObj.ofIso e
  have : IsCommMonObj (F.obj A) := ArithmeticGeometry.Models.SpreadingOut.GroupReflection.Construction.commutative_group_of_iso e
  have hOne := FamilyMorphismComparison.cartesian_group_one_image u G A e q he z hz
  have hMul := cartesian_group_multiplication_image u G A e q he qp h₁ h₂ m hm
  have hInv := FamilyMorphismComparison.cartesian_group_inverse_image u G A e q he d hd
  let gA := ArithmeticGeometry.Models.SpreadingOut.GroupReflection.Construction.groupObjectOfMappedOperations F A z m d hOne hMul hInv
    F.map_injective F.map_injective F.map_injective F.map_injective
  have himage := ArithmeticGeometry.Models.SpreadingOut.GroupReflection.Construction.groupObjectOfMappedOperations_image F A z m d hOne hMul hInv
    F.map_injective F.map_injective F.map_injective F.map_injective
  refine ⟨gA, ArithmeticGeometry.Models.SpreadingOut.GroupReflection.Construction.groupObjectOfMappedOperations_comm F A z m d hOne hMul hInv
    F.map_injective F.map_injective F.map_injective F.map_injective F.map_injective, ?_⟩
  let := gA
  let : GrpObj (F.obj A) := Functor.grpObjObj (F := F) (G := A)
  have hi : IsMonHom e.inv := ArithmeticGeometry.Models.SpreadingOut.GroupReflection.Construction.image_group_iso_isMonHom F A G e.symm gA himage
  have : IsMonHom e.symm.hom := hi
  exact inferInstanceAs (IsMonHom e.symm.inv)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.GroupPair
