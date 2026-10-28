import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionScheme

/-! # Kernel Scheme -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The scheme-theoretic kernel of an actual finite-flat isogeny, its universal point, and its point and rank comparisons. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

variable {S : Scheme.{u}} {g h : ℕ} {A : Abelian.Schemes.AbelianScheme g S} {B : Abelian.Schemes.AbelianScheme h S}
variable (p : Abelian.Schemes.AbelianScheme.Isogeny A B)

def Abelian.Schemes.AbelianScheme.Isogeny.kernelScheme : Over S := Over.mk (pullback.snd p.hom.left η[B.scheme].left)

def Abelian.Schemes.AbelianScheme.Isogeny.kernelInclusion : p.kernelScheme ⟶ A.scheme :=
  Over.homMk (pullback.fst p.hom.left η[B.scheme].left) (by
    have hz : η[B.scheme].left ≫ B.scheme.hom = 𝟙 S := η[B.scheme].w
    calc
      _ = pullback.fst p.hom.left η[B.scheme].left ≫ p.hom.left ≫ B.scheme.hom :=
        congrArg (fun f => pullback.fst p.hom.left η[B.scheme].left ≫ f) p.hom.w.symm
      _ = pullback.snd p.hom.left η[B.scheme].left ≫ η[B.scheme].left ≫ B.scheme.hom :=
        pullback.condition_assoc B.scheme.hom
      _ = _ := (congrArg (fun f => pullback.snd p.hom.left η[B.scheme].left ≫ f) hz).trans
        (Category.comp_id _))

theorem Abelian.Schemes.AbelianScheme.Isogeny.kernel_condition_iff (T : Over S) (x : A.Points T) :
    x.left ≫ p.hom.left = T.hom ≫ η[B.scheme].left ↔ x ≫ p.hom = 1 := by
  constructor
  · intro h
    exact Over.OverMorphism.ext h
  · intro h
    exact congrArg (fun f : B.Points T => f.left) h

theorem Abelian.Schemes.AbelianScheme.Isogeny.kernelInclusion_comp : p.kernelInclusion ≫ p.hom = 1 :=
  (p.kernel_condition_iff p.kernelScheme p.kernelInclusion).mp pullback.condition

def Abelian.Schemes.AbelianScheme.Isogeny.kernelSchemePointsEquiv (T : Over S) : (T ⟶ p.kernelScheme) ≃ p.kernelAt T where
  toFun t := ⟨t ≫ p.kernelInclusion, by
    change (t ≫ p.kernelInclusion) ≫ p.hom = 1
    rw [Category.assoc, Abelian.Schemes.AbelianScheme.Isogeny.kernelInclusion_comp, MonObj.comp_one]⟩
  invFun x := Over.homMk (pullback.lift x.val.left T.hom
    ((p.kernel_condition_iff T x.val).mpr (MonoidHom.mem_ker.mp x.property)))
      (pullback.lift_snd _ _ _)
  left_inv t := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans t.w.symm
  right_inv x := by
    apply Subtype.ext
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _

instance Abelian.Schemes.AbelianScheme.Isogeny.kernelScheme_finite : IsFinite p.kernelScheme.hom :=
  inferInstanceAs (IsFinite (pullback.snd p.hom.left η[B.scheme].left))

instance Abelian.Schemes.AbelianScheme.Isogeny.kernelScheme_flat : Flat p.kernelScheme.hom :=
  inferInstanceAs (Flat (pullback.snd p.hom.left η[B.scheme].left))

instance Abelian.Schemes.AbelianScheme.Isogeny.kernelInclusion_closedImmersion : IsClosedImmersion p.kernelInclusion.left :=
  inferInstanceAs (IsClosedImmersion (pullback.fst p.hom.left η[B.scheme].left))

theorem Abelian.Schemes.AbelianScheme.Isogeny.kernelScheme_finrank (s : S) : p.kernelScheme.hom.finrank s = p.hom.left.finrank (η[B.scheme].left s) :=
  Scheme.Hom.finrank_of_isPullback _ _ _ _ (IsPullback.of_hasPullback p.hom.left η[B.scheme].left) s

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
