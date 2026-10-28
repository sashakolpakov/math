import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Functor-of-points compatibility of full level structures with base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {g N : ℕ} {S S' : Scheme.{u}}

/-- The pullback adjunction identifies points over a changed base. -/
def Abelian.Schemes.AbelianScheme.baseChangePointsEquiv (A : Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S) (T : Over S') :
    (A.pullback f).Points T ≃ A.Points ((Over.map f).obj T) :=
  ((Over.mapPullbackAdj f).homEquiv T A.scheme).symm

@[simp]
theorem Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_apply (A : Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S)
    (T : Over S') (x : (A.pullback f).Points T) :
    (A.baseChangePointsEquiv f T x).left =
      x.left ≫ Limits.pullback.fst A.scheme.hom f := rfl

/-- The base-change identification preserves the group law on points. -/
def Abelian.Schemes.AbelianScheme.baseChangePointsMulEquiv (A : Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S) (T : Over S') :
    (A.pullback f).Points T ≃* A.Points ((Over.map f).obj T) where
  toEquiv := A.baseChangePointsEquiv f T
  map_mul' x y := by
    let F := Over.pullback f
    let p := Limits.pullback.fst A.scheme.hom f
    let p₂ := Limits.pullback.fst (A.scheme ⊗ A.scheme).hom f
    have hμ : μ[(A.pullback f).scheme].left ≫ p =
        (Functor.LaxMonoidal.μ F A.scheme A.scheme).left ≫ p₂ ≫ μ[A.scheme].left := by
      change (Functor.LaxMonoidal.μ F A.scheme A.scheme ≫ F.map μ[A.scheme]).left ≫ p = _
      simp only [F, p, p₂, Over.comp_left, Over.pullback_map_left,
        Category.assoc, Limits.pullback.lift_fst]
    have hassoc (z : (A.scheme ⊗ A.scheme).left ⟶ A.scheme.left) :
        ((lift x y).left ≫ (Functor.LaxMonoidal.μ F A.scheme A.scheme).left ≫ p₂) ≫ z =
          (lift x y).left ≫ ((Functor.LaxMonoidal.μ F A.scheme A.scheme).left ≫ p₂ ≫ z) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun a => (lift x y).left ≫ a) (Category.assoc _ _ _))
    have hpair : (lift x y).left ≫ (Functor.LaxMonoidal.μ F A.scheme A.scheme).left ≫ p₂ =
        (lift (A.baseChangePointsEquiv f T x) (A.baseChangePointsEquiv f T y)).left := by
      apply Over.tensorObj_ext
      · calc
          _ = (lift x y).left ≫
              ((Functor.LaxMonoidal.μ F A.scheme A.scheme).left ≫ p₂ ≫
                Limits.pullback.fst A.scheme.hom A.scheme.hom) := hassoc _
          _ = (lift x y).left ≫
              (Limits.pullback.fst (A.pullback f).scheme.hom (A.pullback f).scheme.hom ≫ p) :=
            congrArg (fun a => (lift x y).left ≫ a)
              (Over.μ_pullback_left_fst_fst (f := f) A.scheme A.scheme)
          _ = x.left ≫ p := (Category.assoc _ _ _).symm.trans
            (congrArg (fun a => a ≫ p) (show (lift x y).left ≫
                Limits.pullback.fst (A.pullback f).scheme.hom (A.pullback f).scheme.hom = x.left by
              simp only [Over.lift_left, Limits.pullback.lift_fst]))
          _ = _ := by
            simp only [Over.lift_left, Limits.pullback.lift_fst, Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_apply, p]
      · calc
          _ = (lift x y).left ≫
              ((Functor.LaxMonoidal.μ F A.scheme A.scheme).left ≫ p₂ ≫
                Limits.pullback.snd A.scheme.hom A.scheme.hom) := hassoc _
          _ = (lift x y).left ≫
              (Limits.pullback.snd (A.pullback f).scheme.hom (A.pullback f).scheme.hom ≫ p) :=
            congrArg (fun a => (lift x y).left ≫ a)
              (Over.μ_pullback_left_fst_snd (f := f) A.scheme A.scheme)
          _ = y.left ≫ p := (Category.assoc _ _ _).symm.trans
            (congrArg (fun a => a ≫ p) (show (lift x y).left ≫
                Limits.pullback.snd (A.pullback f).scheme.hom (A.pullback f).scheme.hom = y.left by
              simp only [Over.lift_left, Limits.pullback.lift_snd]))
          _ = _ := by
            simp only [Over.lift_left, Limits.pullback.lift_snd, Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_apply, p]
    apply Over.OverMorphism.ext
    change ((lift x y).left ≫ μ[(A.pullback f).scheme].left) ≫ p =
      (lift (A.baseChangePointsEquiv f T x) (A.baseChangePointsEquiv f T y)).left ≫ μ[A.scheme].left
    calc
      _ = (lift x y).left ≫ (μ[(A.pullback f).scheme].left ≫ p) := Category.assoc _ _ _
      _ = (lift x y).left ≫
          ((Functor.LaxMonoidal.μ F A.scheme A.scheme).left ≫ p₂ ≫ μ[A.scheme].left) :=
        congrArg (fun a => (lift x y).left ≫ a) hμ
      _ = ((lift x y).left ≫ (Functor.LaxMonoidal.μ F A.scheme A.scheme).left ≫ p₂) ≫
          μ[A.scheme].left := (hassoc μ[A.scheme].left).symm
      _ = _ := congrArg (fun a => a ≫ μ[A.scheme].left) hpair

/-- The point identification restricts to the `N`-torsion subgroups. -/
def Abelian.Schemes.AbelianScheme.torsionBaseChangeEquiv (A : Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S) (T : Over S') (N : ℕ) :
    (A.pullback f).torsionPoints N T ≃* A.torsionPoints N ((Over.map f).obj T) where
  toFun x := ⟨A.baseChangePointsMulEquiv f T x.val, by
    change (A.baseChangePointsMulEquiv f T x.val) ^ N = 1
    rw [← map_pow, (Abelian.Schemes.AbelianScheme.mem_torsionPoints _ _ _ _).mp x.property, map_one]⟩
  invFun x := ⟨(A.baseChangePointsMulEquiv f T).symm x.val, by
    change ((A.baseChangePointsMulEquiv f T).symm x.val) ^ N = 1
    rw [← map_pow, (Abelian.Schemes.AbelianScheme.mem_torsionPoints _ _ _ _).mp x.property, map_one]⟩
  left_inv x := Subtype.ext ((A.baseChangePointsMulEquiv f T).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((A.baseChangePointsMulEquiv f T).apply_symm_apply x.val)
  map_mul' x y := Subtype.ext ((A.baseChangePointsMulEquiv f T).map_mul x.val y.val)

/-- Compatibility with pullback of test schemes makes this an isomorphism of functors. -/
def Abelian.Schemes.AbelianScheme.torsionBaseChangeIso (A : Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S) (N : ℕ) :
    (A.pullback f).torsionFunctor N ≅ (Over.map f).op ⋙ A.torsionFunctor N :=
  NatIso.ofComponents (fun T => MulEquiv.toGrpIso (A.torsionBaseChangeEquiv f T.unop N))
    (by
      intro T U h
      apply GrpCat.hom_ext
      apply MonoidHom.ext
      intro x
      apply Subtype.ext
      apply Over.OverMorphism.ext
      exact Category.assoc _ _ _)

/-- Full ordered level structures pull back along every base morphism. -/
def Abelian.Schemes.AbelianScheme.FullLevel.pullback {A : Abelian.Schemes.AbelianScheme g S} (level : A.FullLevel N) (f : S' ⟶ S) :
    (A.pullback f).FullLevel N :=
  Functor.isoWhiskerLeft (Over.map f).op level ≪≫ (A.torsionBaseChangeIso f N).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
