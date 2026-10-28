import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupBaseChange
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FiberGeneration

/-! # Group Fiber Points -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupFiberPoints.CM

noncomputable section

/-! The pullback adjunction preserves multiplication on the points of
any group scheme. No polarization or projective presentation is needed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupBaseChange.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM

variable {S S' : Scheme}

/-- The pullback adjunction identifies points over a changed base. -/
def baseChangePointsEquiv (A : CommGrp (Over S)) (f : S' ⟶ S) (T : Over S') :
    (T ⟶ (GroupBaseChange.CM.changedGroup A f).X) ≃ ((Over.map f).obj T ⟶ A.X) :=
  ((Over.mapPullbackAdj f).homEquiv T A.X).symm

@[simp]
theorem baseChangePointsEquiv_apply (A : CommGrp (Over S)) (f : S' ⟶ S)
    (T : Over S') (x : (T ⟶ (GroupBaseChange.CM.changedGroup A f).X)) :
    (baseChangePointsEquiv A f T x).left =
      x.left ≫ Limits.pullback.fst A.X.hom f := rfl

/-- The base-change identification preserves the group law on points. -/
def baseChangePointsMulEquiv (A : CommGrp (Over S)) (f : S' ⟶ S) (T : Over S') :
    (T ⟶ (GroupBaseChange.CM.changedGroup A f).X) ≃* ((Over.map f).obj T ⟶ A.X) where
  toEquiv := baseChangePointsEquiv A f T
  map_mul' x y := by
    let F := Over.pullback f
    let p := Limits.pullback.fst A.X.hom f
    let p₂ := Limits.pullback.fst (A.X ⊗ A.X).hom f
    have hμ : μ[(GroupBaseChange.CM.changedGroup A f).X].left ≫ p =
        (Functor.LaxMonoidal.μ F A.X A.X).left ≫ p₂ ≫ μ[A.X].left := by
      change (Functor.LaxMonoidal.μ F A.X A.X ≫ F.map μ[A.X]).left ≫ p = _
      simp only [F, p, p₂, Over.comp_left, Over.pullback_map_left,
        Category.assoc, Limits.pullback.lift_fst]
    have hassoc (z : (A.X ⊗ A.X).left ⟶ A.X.left) :
        ((lift x y).left ≫ (Functor.LaxMonoidal.μ F A.X A.X).left ≫ p₂) ≫ z =
          (lift x y).left ≫ ((Functor.LaxMonoidal.μ F A.X A.X).left ≫ p₂ ≫ z) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun a => (lift x y).left ≫ a) (Category.assoc _ _ _))
    have hpair : (lift x y).left ≫ (Functor.LaxMonoidal.μ F A.X A.X).left ≫ p₂ =
        (lift (baseChangePointsEquiv A f T x) (baseChangePointsEquiv A f T y)).left := by
      apply Over.tensorObj_ext
      · calc
          _ = (lift x y).left ≫
              ((Functor.LaxMonoidal.μ F A.X A.X).left ≫ p₂ ≫
                Limits.pullback.fst A.X.hom A.X.hom) := hassoc _
          _ = (lift x y).left ≫
              (Limits.pullback.fst (GroupBaseChange.CM.changedGroup A f).X.hom (GroupBaseChange.CM.changedGroup A f).X.hom ≫ p) :=
            congrArg (fun a => (lift x y).left ≫ a)
              (Over.μ_pullback_left_fst_fst (f := f) A.X A.X)
          _ = x.left ≫ p := (Category.assoc _ _ _).symm.trans
            (congrArg (fun a => a ≫ p) (show (lift x y).left ≫
                Limits.pullback.fst (GroupBaseChange.CM.changedGroup A f).X.hom (GroupBaseChange.CM.changedGroup A f).X.hom = x.left by
              simp only [Over.lift_left, Limits.pullback.lift_fst]))
          _ = _ := by
            simp only [Over.lift_left, Limits.pullback.lift_fst, baseChangePointsEquiv_apply, p]
      · calc
          _ = (lift x y).left ≫
              ((Functor.LaxMonoidal.μ F A.X A.X).left ≫ p₂ ≫
                Limits.pullback.snd A.X.hom A.X.hom) := hassoc _
          _ = (lift x y).left ≫
              (Limits.pullback.snd (GroupBaseChange.CM.changedGroup A f).X.hom (GroupBaseChange.CM.changedGroup A f).X.hom ≫ p) :=
            congrArg (fun a => (lift x y).left ≫ a)
              (Over.μ_pullback_left_fst_snd (f := f) A.X A.X)
          _ = y.left ≫ p := (Category.assoc _ _ _).symm.trans
            (congrArg (fun a => a ≫ p) (show (lift x y).left ≫
                Limits.pullback.snd (GroupBaseChange.CM.changedGroup A f).X.hom (GroupBaseChange.CM.changedGroup A f).X.hom = y.left by
              simp only [Over.lift_left, Limits.pullback.lift_snd]))
          _ = _ := by
            simp only [Over.lift_left, Limits.pullback.lift_snd, baseChangePointsEquiv_apply, p]
    apply Over.OverMorphism.ext
    change ((lift x y).left ≫ μ[(GroupBaseChange.CM.changedGroup A f).X].left) ≫ p =
      (lift (baseChangePointsEquiv A f T x) (baseChangePointsEquiv A f T y)).left ≫ μ[A.X].left
    calc
      _ = (lift x y).left ≫ (μ[(GroupBaseChange.CM.changedGroup A f).X].left ≫ p) := Category.assoc _ _ _
      _ = (lift x y).left ≫
          ((Functor.LaxMonoidal.μ F A.X A.X).left ≫ p₂ ≫ μ[A.X].left) :=
        congrArg (fun a => (lift x y).left ≫ a) hμ
      _ = ((lift x y).left ≫ (Functor.LaxMonoidal.μ F A.X A.X).left ≫ p₂) ≫
          μ[A.X].left := (hassoc μ[A.X].left).symm
      _ = _ := congrArg (fun a => a ≫ μ[A.X].left) hpair

def fiberMulEquiv (A : CommGrp (Over S)) {k : Type} [Field k]
    (b : Spec (.of k) ⟶ S) :
    (Geometric.PointExt.CM.pointBase k ⟶ (GroupBaseChange.CM.changedGroup A b).X) ≃* (Over.mk b ⟶ A.X) :=
  (baseChangePointsMulEquiv A b (Geometric.PointExt.CM.pointBase k)).trans
    (FiberGeneration.CM.testPointMulEquiv (FiberGeneration.CM.mappedPointIso b))

theorem fiberMulEquiv_apply (A : CommGrp (Over S)) {k : Type} [Field k]
    (b : Spec (.of k) ⟶ S) (p : Geometric.PointExt.CM.pointBase k ⟶ (GroupBaseChange.CM.changedGroup A b).X) :
    fiberMulEquiv A b p = FiberGeneration.CM.fiberPointsEquiv A.X b p := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupFiberPoints.CM
