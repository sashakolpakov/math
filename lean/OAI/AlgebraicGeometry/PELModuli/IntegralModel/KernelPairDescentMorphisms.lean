import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.PairDetectsMorphisms

/-! # Kernel Pair Descent Morphisms -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.KernelPairDescentMorphisms

noncomputable section

/-! Compatibility on a specified kernel-pair presentation determines
the full ordinary descent morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v u' v'

variable {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) {X Y R : C}
    (f : X ⟶ Y) (s t : R ⟶ X) (hk : IsKernelPair f s t)
    (D E : F.DescentData (fun (_ : PUnit.{1}) => f)) (a : D.obj PUnit.unit ⟶ E.obj PUnit.unit)
    (ha : (F.map s.op.toLoc).toFunctor.map a ≫
        E.hom (t ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit) s t hk.w rfl =
      D.hom (t ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit) s t hk.w rfl ≫
        (F.map t.op.toLoc).toFunctor.map a)

include hk ha in
theorem kernelPair_descent_compatible {T : C} (q : T ⟶ Y) (x y : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q) :
    (F.map x.op.toLoc).toFunctor.map a ≫ E.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy =
      D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy ≫ (F.map y.op.toLoc).toFunctor.map a := by
  let r := hk.lift x y (hx.trans hy.symm)
  have hrs : r ≫ s = x := hk.lift_fst _ _ _
  have hrt : r ≫ t = y := hk.lift_snd _ _ _
  have hrq : r ≫ (t ≫ f) = q := by rw [← Category.assoc, hrt, hy]
  have he := congrArg (fun b => pullHom (F := F) b r x y hrs hrt) ha
  rw [Picard.PoincareBundle.PullHom.pullHom_comp _ _ r x x y hrs hrs hrt,
    Picard.PoincareBundle.PullHom.pullHom_comp _ _ r x y y hrs hrt hrt,
    Picard.PoincareBundle.Ordinary.DescentObjectIso.pullHom_map,
    E.pullHom_hom r (t ≫ f) q hrq s t hk.w rfl x y hrs hrt,
    D.pullHom_hom r (t ≫ f) q hrq s t hk.w rfl x y hrs hrt,
    Picard.PoincareBundle.Ordinary.DescentObjectIso.pullHom_map] at he
  exact he

def kernelPair_descentHom : D ⟶ E where
  hom _ := a
  comm _T q i j x y hx hy := by
    cases i
    cases j
    exact kernelPair_descent_compatible F f s t hk D E a ha q x y hx hy

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.KernelPairDescentMorphisms
