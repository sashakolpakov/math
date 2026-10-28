import OAI.AlgebraicGeometry.PELModuli.CMPoints.FixedCoefficientModels

/-! # Model Lifts -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.ModelLifts

noncomputable section

/-! Projection-preserving lifts for models under arbitrary base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S T U : Scheme} (X : Over S) {G : Over U}
  (p : G.left ⟶ X.left) (f : T ⟶ S) (v : U ⟶ T)
  (hp : p ≫ X.hom = G.hom ≫ v ≫ f)

def modelLift : G.left ⟶ ((Over.pullback f).obj X).left :=
  pullback.lift p (G.hom ≫ v) (hp.trans (Category.assoc _ _ _).symm)

@[reassoc]
theorem modelLift_fst : modelLift X p f v hp ≫ pullback.fst X.hom f = p :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem modelLift_snd : modelLift X p f v hp ≫ pullback.snd X.hom f = G.hom ≫ v :=
  pullback.lift_snd _ _ _

theorem modelLift_cartesian
    (hcart : IsPullback p G.hom X.hom (v ≫ f)) :
    IsPullback (modelLift X p f v hp) G.hom ((Over.pullback f).obj X).hom v := by
  apply IsPullback.of_right ?_ (modelLift_snd X p f v hp)
    (IsPullback.of_hasPullback X.hom f)
  rw [modelLift_fst]
  exact hcart

theorem modelLift_map
    {Y : Over S} {H : Over U} (pY : H.left ⟶ Y.left)
    (hpY : pY ≫ Y.hom = H.hom ≫ v ≫ f)
    (a : G ⟶ H) (b : X ⟶ Y) (hab : p ≫ b.left = a.left ≫ pY) :
    modelLift X p f v hp ≫ ((Over.pullback f).map b).left =
      a.left ≫ modelLift Y pY f v hpY := by
  apply pullback.hom_ext
  · erw [Category.assoc, pullback.lift_fst, ← Category.assoc,
      modelLift_fst, hab, Category.assoc, modelLift_fst]
  · erw [Category.assoc, pullback.lift_snd, modelLift_snd,
      Category.assoc, modelLift_snd, ← Category.assoc, a.w]

theorem modelLift_iterated {V : Scheme} (h : V ⟶ T) (g : V ⟶ S)
    (w : h ≫ f = g) (r : U ⟶ V) (hr : r ≫ h = v)
    (hp' : p ≫ X.hom = G.hom ≫ r ≫ g) :
    modelLift ((Over.pullback f).obj X) (modelLift X p f v hp) h r
        ((modelLift_snd X p f v hp).trans (congrArg (fun z => G.hom ≫ z) hr.symm)) ≫
      (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso X f h g w).hom.left =
        modelLift X p g r hp' := by
  apply pullback.hom_ext
  · rw [Category.assoc, IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso_fst, ← Category.assoc]
    exact (congrArg (fun z => z ≫ pullback.fst X.hom f)
      (modelLift_fst ((Over.pullback f).obj X) _ h r _)).trans
      ((modelLift_fst X p f v hp).trans (modelLift_fst X p g r hp').symm)
  · rw [Category.assoc]
    change _ ≫ ((IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso X f h g w).hom.left ≫
      ((Over.pullback g).obj X).hom) = _
    rw [(IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso X f h g w).hom.w]
    exact (modelLift_snd ((Over.pullback f).obj X) _ h r _).trans
      (modelLift_snd X p g r hp').symm

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.ModelLifts
