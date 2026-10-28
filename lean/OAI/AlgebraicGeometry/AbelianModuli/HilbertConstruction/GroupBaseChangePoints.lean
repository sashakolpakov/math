import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

/-! # Group Base Change Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GroupBaseChangePoints

noncomputable section

/-! The pullback adjunction preserves the group law on points for every group scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S S' : Scheme.{u}}

/-- The pullback adjunction identifies points over a changed base. -/
def groupBaseChangePointsEquiv (A : Over S) [GrpObj A] (f : S' ⟶ S) (T : Over S') :
    (T ⟶ (Over.pullback f).obj A) ≃ ((Over.map f).obj T ⟶ A) :=
  ((Over.mapPullbackAdj f).homEquiv T A).symm

@[simp]
theorem groupBaseChangePointsEquiv_apply (A : Over S) [GrpObj A] (f : S' ⟶ S)
    (T : Over S') (x : (T ⟶ (Over.pullback f).obj A)) :
    (groupBaseChangePointsEquiv A f T x).left =
      x.left ≫ Limits.pullback.fst A.hom f := rfl

/-- The base-change identification preserves the group law on points. -/
def groupBaseChangePointsMulEquiv (A : Over S) [GrpObj A] (f : S' ⟶ S) (T : Over S') :
    (T ⟶ (Over.pullback f).obj A) ≃* ((Over.map f).obj T ⟶ A) where
  toEquiv := groupBaseChangePointsEquiv A f T
  map_mul' x y := by
    let F := Over.pullback f
    let p := Limits.pullback.fst A.hom f
    let p₂ := Limits.pullback.fst (A ⊗ A).hom f
    have hμ : μ[((Over.pullback f).obj A)].left ≫ p =
        (Functor.LaxMonoidal.μ F A A).left ≫ p₂ ≫ μ[A].left := by
      change (Functor.LaxMonoidal.μ F A A ≫ F.map μ[A]).left ≫ p = _
      simp only [F, p, p₂, Over.comp_left, Over.pullback_map_left,
        Category.assoc, Limits.pullback.lift_fst]
    have hassoc (z : (A ⊗ A).left ⟶ A.left) :
        ((lift x y).left ≫ (Functor.LaxMonoidal.μ F A A).left ≫ p₂) ≫ z =
          (lift x y).left ≫ ((Functor.LaxMonoidal.μ F A A).left ≫ p₂ ≫ z) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun a => (lift x y).left ≫ a) (Category.assoc _ _ _))
    have hpair : (lift x y).left ≫ (Functor.LaxMonoidal.μ F A A).left ≫ p₂ =
        (lift (groupBaseChangePointsEquiv A f T x) (groupBaseChangePointsEquiv A f T y)).left := by
      apply Over.tensorObj_ext
      · calc
          _ = (lift x y).left ≫
              ((Functor.LaxMonoidal.μ F A A).left ≫ p₂ ≫
                Limits.pullback.fst A.hom A.hom) := hassoc _
          _ = (lift x y).left ≫
              (Limits.pullback.fst ((Over.pullback f).obj A).hom ((Over.pullback f).obj A).hom ≫ p) :=
            congrArg (fun a => (lift x y).left ≫ a)
              (Over.μ_pullback_left_fst_fst (f := f) A A)
          _ = x.left ≫ p := (Category.assoc _ _ _).symm.trans
            (congrArg (fun a => a ≫ p) (show (lift x y).left ≫
                Limits.pullback.fst ((Over.pullback f).obj A).hom ((Over.pullback f).obj A).hom = x.left by
              simp only [Over.lift_left, Limits.pullback.lift_fst]))
          _ = _ := by
            simp only [Over.lift_left, Limits.pullback.lift_fst, groupBaseChangePointsEquiv_apply, p]
      · calc
          _ = (lift x y).left ≫
              ((Functor.LaxMonoidal.μ F A A).left ≫ p₂ ≫
                Limits.pullback.snd A.hom A.hom) := hassoc _
          _ = (lift x y).left ≫
              (Limits.pullback.snd ((Over.pullback f).obj A).hom ((Over.pullback f).obj A).hom ≫ p) :=
            congrArg (fun a => (lift x y).left ≫ a)
              (Over.μ_pullback_left_fst_snd (f := f) A A)
          _ = y.left ≫ p := (Category.assoc _ _ _).symm.trans
            (congrArg (fun a => a ≫ p) (show (lift x y).left ≫
                Limits.pullback.snd ((Over.pullback f).obj A).hom ((Over.pullback f).obj A).hom = y.left by
              simp only [Over.lift_left, Limits.pullback.lift_snd]))
          _ = _ := by
            simp only [Over.lift_left, Limits.pullback.lift_snd, groupBaseChangePointsEquiv_apply, p]
    apply Over.OverMorphism.ext
    change ((lift x y).left ≫ μ[((Over.pullback f).obj A)].left) ≫ p =
      (lift (groupBaseChangePointsEquiv A f T x) (groupBaseChangePointsEquiv A f T y)).left ≫ μ[A].left
    calc
      _ = (lift x y).left ≫ (μ[((Over.pullback f).obj A)].left ≫ p) := Category.assoc _ _ _
      _ = (lift x y).left ≫
          ((Functor.LaxMonoidal.μ F A A).left ≫ p₂ ≫ μ[A].left) :=
        congrArg (fun a => (lift x y).left ≫ a) hμ
      _ = ((lift x y).left ≫ (Functor.LaxMonoidal.μ F A A).left ≫ p₂) ≫
          μ[A].left := (hassoc μ[A].left).symm
      _ = _ := congrArg (fun a => a ≫ μ[A].left) hpair

def groupBaseChangeYonedaIso (A : Over S) [GrpObj A] (f : S' ⟶ S) :
    yonedaGrpObj ((Over.pullback f).obj A) ≅ (Over.map f).op ⋙ yonedaGrpObj A :=
  NatIso.ofComponents (fun T => MulEquiv.toGrpIso (groupBaseChangePointsMulEquiv A f T.unop)) (by
    intro T U h
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Over.OverMorphism.ext
    exact Category.assoc h.unop.left x.left (Limits.pullback.fst A.hom f))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GroupBaseChangePoints
