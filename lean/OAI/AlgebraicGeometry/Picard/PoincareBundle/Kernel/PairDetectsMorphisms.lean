import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.DescentObjectIso
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # Pair Detects Morphisms -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.PairDetectsMorphisms

noncomputable section

/-!
# Compatibility on the actual kernel pair determines all ordinary descent-morphism equations
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v u' v'

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) {X Y : C} (f : X ⟶ Y)
  (D E : F.DescentData (fun (_ : PUnit.{1}) => f)) (a : D.obj PUnit.unit ⟶ E.obj PUnit.unit)
  (ha : (F.map (pullback.fst f f).op.toLoc).toFunctor.map a ≫
      E.hom (pullback.snd f f ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit)
        (pullback.fst f f) (pullback.snd f f) pullback.condition rfl =
    D.hom (pullback.snd f f ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit)
        (pullback.fst f f) (pullback.snd f f) pullback.condition rfl ≫
      (F.map (pullback.snd f f).op.toLoc).toFunctor.map a)

include ha in
/-- Pulling back the kernel-pair equation proves compatibility on every equal-image pair of test points. -/
theorem compatible {T : C} (q : T ⟶ Y) (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q) :
    (F.map x.op.toLoc).toFunctor.map a ≫ E.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy =
      D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy ≫ (F.map y.op.toLoc).toFunctor.map a := by
  let t := pullback.lift x y (hx.trans hy.symm)
  have htx : t ≫ pullback.fst f f = x := pullback.lift_fst _ _ _
  have hty : t ≫ pullback.snd f f = y := pullback.lift_snd _ _ _
  have htq : t ≫ (pullback.snd f f ≫ f) = q := by rw [← Category.assoc, hty, hy]
  have he := congrArg (fun b => pullHom (F := F) b t x y htx hty) ha
  rw [PullHom.pullHom_comp _ _ t x x y htx htx hty,
    PullHom.pullHom_comp _ _ t x y y htx hty hty,
    Ordinary.DescentObjectIso.pullHom_map,
    E.pullHom_hom t (pullback.snd f f ≫ f) q htq (pullback.fst f f) (pullback.snd f f)
      pullback.condition rfl x y htx hty,
    D.pullHom_hom t (pullback.snd f f ≫ f) q htq (pullback.fst f f) (pullback.snd f f)
      pullback.condition rfl x y htx hty,
    Ordinary.DescentObjectIso.pullHom_map] at he
  exact he

/-- The actual source morphism therefore defines a morphism of the full ordinary descent data. -/
def descentHom : D ⟶ E where
  hom _ := a
  comm _T q i j x y hx hy := by
    cases i
    cases j
    exact compatible F f D E a ha q x y hx hy

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.PairDetectsMorphisms
