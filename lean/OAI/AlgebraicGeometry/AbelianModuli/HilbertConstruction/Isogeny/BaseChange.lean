import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogenies
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.BaseChange

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Isogenies and their geometric kernel types commute with arbitrary base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {g h : ℕ} {S S' : Scheme.{u}}

/-- A finite flat surjective group morphism remains one after base change. -/
def Abelian.Schemes.AbelianScheme.Isogeny.pullback {A : Abelian.Schemes.AbelianScheme g S} {B : Abelian.Schemes.AbelianScheme h S}
    (p : Abelian.Schemes.AbelianScheme.Isogeny A B) (f : S' ⟶ S) : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback f) (B.pullback f) where
  hom := (Over.pullback f).map p.hom
  preservesGroup := inferInstanceAs (IsMonHom ((Over.pullback f).map p.hom))
  finite := MorphismProperty.overPullbackMap f p.hom p.finite
  flat := MorphismProperty.overPullbackMap f p.hom p.flat
  surjective := MorphismProperty.overPullbackMap f p.hom p.surjective

/-- The base-change bijection of points commutes with group-scheme morphisms. -/
theorem Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map {A : Abelian.Schemes.AbelianScheme g S} {B : Abelian.Schemes.AbelianScheme h S}
    (p : A.scheme ⟶ B.scheme) (f : S' ⟶ S) (T : Over S')
    (x : (A.pullback f).Points T) :
    B.baseChangePointsEquiv f T (x ≫ (Over.pullback f).map p) =
      A.baseChangePointsEquiv f T x ≫ p := by
  apply Over.OverMorphism.ext
  change (x.left ≫ ((Over.pullback f).map p).left) ≫ pullback.fst B.scheme.hom f =
    (x.left ≫ pullback.fst A.scheme.hom f) ≫ p.left
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => x.left ≫ z) (pullback.lift_fst _ _ _)).trans
      (Category.assoc _ _ _).symm)

/-- Kernel points after base change are exactly the original kernel points
over the same test scheme, now regarded as a scheme over the old base. -/
def Abelian.Schemes.AbelianScheme.Isogeny.kernelBaseChangeEquiv {A : Abelian.Schemes.AbelianScheme g S} {B : Abelian.Schemes.AbelianScheme h S}
    (p : Abelian.Schemes.AbelianScheme.Isogeny A B) (f : S' ⟶ S) (T : Over S') :
    (p.pullback f).kernelAt T ≃* p.kernelAt ((Over.map f).obj T) where
  toFun x := ⟨A.baseChangePointsMulEquiv f T x.val, by
    change A.baseChangePointsEquiv f T x.val ≫ p.hom = 1
    rw [← Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map]
    change B.baseChangePointsMulEquiv f T
      ((A.pullback f).mapPoints (B.pullback f) (p.pullback f).hom T x.val) = 1
    rw [MonoidHom.mem_ker.mp x.property, map_one]⟩
  invFun x := ⟨(A.baseChangePointsMulEquiv f T).symm x.val, by
    change ((A.pullback f).mapPoints (B.pullback f) (p.pullback f).hom T)
      ((A.baseChangePointsMulEquiv f T).symm x.val) = 1
    apply (B.baseChangePointsMulEquiv f T).injective
    change B.baseChangePointsEquiv f T
      ((A.baseChangePointsMulEquiv f T).symm x.val ≫ (Over.pullback f).map p.hom) =
      B.baseChangePointsMulEquiv f T 1
    rw [Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map, map_one]
    change A.baseChangePointsMulEquiv f T
      ((A.baseChangePointsMulEquiv f T).symm x.val) ≫ p.hom = 1
    rw [MulEquiv.apply_symm_apply]
    exact MonoidHom.mem_ker.mp x.property⟩
  left_inv x := Subtype.ext ((A.baseChangePointsMulEquiv f T).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((A.baseChangePointsMulEquiv f T).apply_symm_apply x.val)
  map_mul' x y := Subtype.ext ((A.baseChangePointsMulEquiv f T).map_mul x.val y.val)

/-- The elementary-divisor type on geometric fibers is stable under base change. -/
theorem Abelian.Schemes.AbelianScheme.Isogeny.HasPolarizationType.pullback {A B : Abelian.Schemes.AbelianScheme g S}
    {p : Abelian.Schemes.AbelianScheme.Isogeny A B} {δ : Fin g → ℕ} (hp : p.HasPolarizationType δ) (f : S' ⟶ S) :
    (p.pullback f).HasPolarizationType δ where
  degree b := by
    have hrectangle : IsPullback (pullback.fst A.scheme.hom f)
        (((Over.pullback f).map p.hom).left ≫ (B.pullback f).scheme.hom)
        (p.hom.left ≫ B.scheme.hom) f := by
      exact (congrArg₂ (fun (a : Limits.pullback A.scheme.hom f ⟶ S')
        (b : A.scheme.left ⟶ S) => IsPullback (pullback.fst A.scheme.hom f) a b f)
        ((Over.pullback f).map p.hom).w.symm p.hom.w.symm).mp
          (IsPullback.of_hasPullback A.scheme.hom f)
    have hsquare : IsPullback (pullback.fst A.scheme.hom f)
        ((Over.pullback f).map p.hom).left p.hom.left (pullback.fst B.scheme.hom f) :=
      IsPullback.of_bot hrectangle (pullback.lift_fst _ _ _).symm
        (IsPullback.of_hasPullback B.scheme.hom f)
    exact (Scheme.Hom.finrank_of_isPullback _ _ _ _ hsquare b).trans
      (hp.degree (pullback.fst B.scheme.hom f b))
  geometricKernel K _ _ s := by
    obtain ⟨e⟩ := hp.geometricKernel K (s ≫ f)
    exact ⟨(p.kernelBaseChangeEquiv f (Over.mk s)).trans e⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
