import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FieldBaseChangeRigidity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.BaseChangeFunctions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionScheme

/-! # Family Map Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian

noncomputable section

/-! Rigidity for constant abelian families over arbitrary connected parameter schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {K : Type u} [Field K] {g h : ℕ} {T Y : Scheme.{u}}

theorem Schemes.AbelianScheme.pullback_map_rigidity (A : Schemes.AbelianScheme g (Spec (.of K)))
    (t : T ⟶ Spec (.of K)) [PreconnectedSpace T]
    (f : (A.pullback t).scheme.left ⟶ Y) [Y.IsSeparated]
    (s : T) (y : Y)
    (hy : ∀ z : (A.pullback t).scheme.left, (A.pullback t).scheme.hom z = s → f z = y) :
    f = (A.pullback t).scheme.hom ≫ η[(A.pullback t).scheme].left ≫ f := by
  have : IsReduced A.scheme.left := A.reduced_overField
  have : ConnectedSpace A.scheme.left := A.connected_overField
  exact Proper.FieldBaseChangeRigidity.properField_baseChange_globalRigidity A.scheme.hom η[A.scheme].left η[A.scheme].w
    (IsPullback.of_hasPullback A.scheme.hom t) (A.pullback t).scheme.hom.isOpenMap
    η[(A.pullback t).scheme].left η[(A.pullback t).scheme].w f s y hy

theorem Schemes.AbelianScheme.pullback_hom_eq_one_of_constant_fiber
    (A : Schemes.AbelianScheme g (Spec (.of K))) (B : Schemes.AbelianScheme h (Spec (.of K)))
    (t : T ⟶ Spec (.of K)) [PreconnectedSpace T]
    (f : (A.pullback t).scheme ⟶ (B.pullback t).scheme) [IsMonHom f]
    (s : T) (y : B.scheme.left)
    (hy : ∀ z : (A.pullback t).scheme.left, (A.pullback t).scheme.hom z = s →
      Limits.pullback.fst B.scheme.hom t (f.left z) = y) : f = 1 := by
  have : B.scheme.left.IsSeparated := by
    have : IsSeparated (B.scheme.hom ≫ Limits.terminal.from (Spec (.of K))) := inferInstance
    rw [Limits.terminal.comp_from] at this
    exact ⟨this⟩
  have H := A.pullback_map_rigidity t (f.left ≫ Limits.pullback.fst B.scheme.hom t) s y hy
  have hunit : η[(A.pullback t).scheme].left ≫ f.left = η[(B.pullback t).scheme].left :=
    congrArg Over.Hom.left (IsMonHom.one_hom f)
  apply Over.OverMorphism.ext
  apply Limits.pullback.hom_ext
  · calc
      f.left ≫ Limits.pullback.fst B.scheme.hom t =
          (A.pullback t).scheme.hom ≫ η[(A.pullback t).scheme].left ≫
            f.left ≫ Limits.pullback.fst B.scheme.hom t := H
      _ = (A.pullback t).scheme.hom ≫ η[(B.pullback t).scheme].left ≫
          Limits.pullback.fst B.scheme.hom t :=
        congrArg (fun q : T ⟶ B.scheme.left => (A.pullback t).scheme.hom ≫ q)
          ((Category.assoc η[(A.pullback t).scheme].left f.left
            (Limits.pullback.fst B.scheme.hom t)).symm.trans
            (congrArg (fun q : T ⟶ (B.pullback t).scheme.left =>
              q ≫ Limits.pullback.fst B.scheme.hom t) hunit))
      _ = (1 : (A.pullback t).scheme ⟶ (B.pullback t).scheme).left ≫
          Limits.pullback.fst B.scheme.hom t := (Category.assoc _ _ _).symm
  · exact f.w.trans (1 : (A.pullback t).scheme ⟶ (B.pullback t).scheme).w.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian
