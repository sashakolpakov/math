import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogenies
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionScheme
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Isogeny Kernel Scheme -/

namespace OAI.RepresentationTheory.Theta.Geometric.IsogenyKernelScheme

noncomputable section

/-! The actual zero fiber represents the kernel functor of an isogeny. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {g h : ℕ} {S : Scheme.{u}} {A : OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
  (p : OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)

def isogenyKernelPullback {T U : Over S} (f : T ⟶ U) : p.kernelAt U →* p.kernelAt T where
  toFun x := ⟨f ≫ x.val, by
    change (f ≫ x.val) ≫ p.hom = 1
    rw [Category.assoc, show x.val ≫ p.hom = 1 from x.property, MonObj.comp_one]⟩
  map_one' := Subtype.ext (MonObj.comp_one f)
  map_mul' x y := Subtype.ext (MonObj.comp_mul f x.val y.val)

def isogenyKernelFunctor : (Over S)ᵒᵖ ⥤ GrpCat.{u} where
  obj T := GrpCat.of (p.kernelAt T.unop)
  map f := GrpCat.ofHom (isogenyKernelPullback p f.unop)
  map_id T := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact Subtype.ext (Category.id_comp x.val)
  map_comp f h := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact Subtype.ext (Category.assoc _ _ x.val)

def isogenyKernelScheme : Over S := Over.mk (pullback.snd p.hom.left η[B.scheme].left)

def isogenyKernelInclusion : isogenyKernelScheme p ⟶ A.scheme :=
  Over.homMk (pullback.fst p.hom.left η[B.scheme].left) (by
    have hz := η[B.scheme].w
    change η[B.scheme].left ≫ B.scheme.hom = 𝟙 S at hz
    calc
      _ = pullback.fst p.hom.left η[B.scheme].left ≫ p.hom.left ≫ B.scheme.hom :=
        congrArg (fun a => _ ≫ a) p.hom.w.symm
      _ = pullback.snd p.hom.left η[B.scheme].left ≫ η[B.scheme].left ≫ B.scheme.hom :=
        pullback.condition_assoc B.scheme.hom
      _ = _ := (congrArg (fun a => pullback.snd p.hom.left η[B.scheme].left ≫ a) hz).trans
        (Category.comp_id _))

theorem isogenyKernelInclusion_comp : isogenyKernelInclusion p ≫ p.hom = 1 :=
  Over.OverMorphism.ext pullback.condition

def isogenyKernelPointsEquiv (T : Over S) :
    (T ⟶ isogenyKernelScheme p) ≃ p.kernelAt T where
  toFun t := ⟨t ≫ isogenyKernelInclusion p, by
    change (t ≫ isogenyKernelInclusion p) ≫ p.hom = 1
    rw [Category.assoc, isogenyKernelInclusion_comp, MonObj.comp_one]⟩
  invFun x := Over.homMk (pullback.lift x.val.left T.hom
    (congrArg (fun a : B.Points T => a.left) x.property)) (pullback.lift_snd _ _ _)
  left_inv t := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans t.w.symm
  right_inv x := by
    apply Subtype.ext
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _

def isogenyKernelRepresentable :
    (isogenyKernelFunctor p ⋙ forget GrpCat).RepresentableBy (isogenyKernelScheme p) where
  homEquiv := isogenyKernelPointsEquiv p _
  homEquiv_comp h t := Subtype.ext (Category.assoc h t (isogenyKernelInclusion p))

instance isogenyKernelScheme_group : GrpObj (isogenyKernelScheme p) :=
  GrpObj.ofRepresentableBy (isogenyKernelScheme p) (isogenyKernelFunctor p) (isogenyKernelRepresentable p)

def isogenyKernelYonedaIso : yonedaGrpObj (isogenyKernelScheme p) ≅ isogenyKernelFunctor p :=
  yonedaGrpObjIsoOfRepresentableBy (isogenyKernelScheme p) (isogenyKernelFunctor p)
    (isogenyKernelRepresentable p)

instance isogenyKernelScheme_finite : IsFinite (isogenyKernelScheme p).hom :=
  inferInstanceAs (IsFinite (pullback.snd p.hom.left η[B.scheme].left))

instance isogenyKernelScheme_etale [Etale p.hom.left] : Etale (isogenyKernelScheme p).hom :=
  inferInstanceAs (Etale (pullback.snd p.hom.left η[B.scheme].left))

end

end OAI.RepresentationTheory.Theta.Geometric.IsogenyKernelScheme
