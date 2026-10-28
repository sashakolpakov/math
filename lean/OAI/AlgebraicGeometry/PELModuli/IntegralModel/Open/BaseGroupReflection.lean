import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ActionDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons
import Mathlib.AlgebraicGeometry.Gluing

/-! # Base Group Reflection -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.BaseGroupReflection

noncomputable section

section

/-! Pullback to an open base cover is jointly faithful and reflects
the actual unit and multiplication equations of group homomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.Functor
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem over_hom_ext_of_open_base_cover
    {S : Scheme.{0}} (C : S.OpenCover) {X Y : Over S} (f g : X ⟶ Y)
    (h : ∀ i, (Over.pullback (C.f i)).map f = (Over.pullback (C.f i)).map g) : f = g := by
  apply Over.OverMorphism.ext
  apply Scheme.Cover.hom_ext (C.pullback₁ X.hom)
  intro i
  change pullback.fst X.hom (C.f i) ≫ f.left = pullback.fst X.hom (C.f i) ≫ g.left
  rw [← AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst, ← AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst, h i]

theorem isMonHom_of_open_base_cover
    {S : Scheme.{0}} (C : S.OpenCover) {X Y : Over S} [MonObj X] [MonObj Y]
    (f : X ⟶ Y) (h : ∀ i, IsMonHom ((Over.pullback (C.f i)).map f)) : IsMonHom f where
  one_hom := by
    apply over_hom_ext_of_open_base_cover C
    intro i
    let F := Over.pullback (C.f i)
    have := h i
    change F.map (MonObj.one ≫ f) = F.map MonObj.one
    apply (cancel_epi (LaxMonoidal.ε F)).mp
    have he := IsMonHom.one_hom (F.map f)
    change (LaxMonoidal.ε F ≫ F.map MonObj.one) ≫ F.map f =
      LaxMonoidal.ε F ≫ F.map MonObj.one at he
    simpa only [Category.assoc, F.map_comp] using he
  mul_hom := by
    apply over_hom_ext_of_open_base_cover C
    intro i
    let F := Over.pullback (C.f i)
    have := h i
    change F.map (MonObj.mul ≫ f) = F.map ((f ⊗ₘ f) ≫ MonObj.mul)
    apply (cancel_epi (LaxMonoidal.μ F X X)).mp
    have he := IsMonHom.mul_hom (F.map f)
    change (LaxMonoidal.μ F X X ≫ F.map MonObj.mul) ≫ F.map f =
      (F.map f ⊗ₘ F.map f) ≫ LaxMonoidal.μ F Y Y ≫ F.map MonObj.mul at he
    rw [LaxMonoidal.μ_natural_assoc] at he
    simpa only [Category.assoc, F.map_comp] using he

end

/-! Actual relative morphisms glue across an open base cover, using
the literal overlap of the pulled-back source schemes. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S : Scheme.{0}} (C : S.OpenCover) {X Y : Over S}

def OpenBaseMorphismCompatible
    (f : ∀ i, (Over.pullback (C.f i)).obj X ⟶ (Over.pullback (C.f i)).obj Y) : Prop :=
  ∀ i j, pullback.fst (pullback.fst X.hom (C.f i)) (pullback.fst X.hom (C.f j)) ≫
      (f i).left ≫ pullback.fst Y.hom (C.f i) =
    pullback.snd (pullback.fst X.hom (C.f i)) (pullback.fst X.hom (C.f j)) ≫
      (f j).left ≫ pullback.fst Y.hom (C.f j)

theorem existsUnique_morphism_of_open_base_cover
    (f : ∀ i, (Over.pullback (C.f i)).obj X ⟶ (Over.pullback (C.f i)).obj Y)
    (hf : OpenBaseMorphismCompatible C f) :
    ∃! q : X ⟶ Y, ∀ i, (Over.pullback (C.f i)).map q = f i := by
  let D : X.left.OpenCover := C.pullback₁ X.hom
  let m := fun i => (f i).left ≫ pullback.fst Y.hom (C.f i)
  let a := D.glueMorphisms m hf
  have ha (i) : pullback.fst X.hom (C.f i) ≫ a = m i := D.ι_glueMorphisms m hf i
  have hb : a ≫ Y.hom = X.hom := by
    apply D.hom_ext
    intro i
    change pullback.fst X.hom (C.f i) ≫ (a ≫ Y.hom) =
      pullback.fst X.hom (C.f i) ≫ X.hom
    rw [← Category.assoc, ha i]
    change ((f i).left ≫ pullback.fst Y.hom (C.f i)) ≫ Y.hom = _
    have hi : (f i).left ≫ pullback.snd Y.hom (C.f i) = pullback.snd X.hom (C.f i) := (f i).w
    rw [Category.assoc, pullback.condition, ← Category.assoc, hi]
    exact (pullback.condition (f := X.hom) (g := C.f i)).symm
  let q : X ⟶ Y := Over.homMk a hb
  have hq (i) : (Over.pullback (C.f i)).map q = f i := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans (ha i)
    · exact (pullback.lift_snd _ _ _).trans (f i).w.symm
  refine ⟨q, hq, fun r hr => ?_⟩
  exact over_hom_ext_of_open_base_cover C r q (fun i => (hr i).trans (hq i).symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.BaseGroupReflection
