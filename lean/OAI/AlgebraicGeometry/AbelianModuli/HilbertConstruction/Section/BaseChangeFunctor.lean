import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Over

/-! # Base Change Functor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.BaseChangeFunctor

noncomputable section

/-! A section induces a natural section on every base change of its family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (p : X ⟶ S) (x : S ⟶ X) (hx : x ≫ p = 𝟙 S)

def baseChangedSectionMap (T : Over S) : T.left ⟶ Limits.pullback T.hom p :=
  Limits.pullback.lift (𝟙 T.left) (T.hom ≫ x)
    ((Category.id_comp T.hom).trans
      ((Category.assoc T.hom x p).trans
        ((congrArg (fun f => T.hom ≫ f) hx).trans (Category.comp_id T.hom))).symm)

def familyBaseChangeSection : Over.map x ⟶ Over.pullback p where
  app T := Over.homMk (baseChangedSectionMap p x hx T)
    (Limits.pullback.lift_snd _ _ _)
  naturality U V a := by
    apply Over.OverMorphism.ext
    apply Limits.pullback.hom_ext
    · simp only [Over.comp_left, Over.map_map_left, Over.pullback_map_left, Over.homMk_left,
        baseChangedSectionMap, Category.assoc, Limits.pullback.lift_fst, Limits.pullback.lift_fst_assoc]
      exact (Category.comp_id a.left).trans (Category.id_comp a.left).symm
    · simp only [Over.comp_left, Over.map_map_left, Over.pullback_map_left, Over.homMk_left,
        baseChangedSectionMap, Category.assoc, Limits.pullback.lift_snd]
      exact (Category.assoc a.left V.hom x).symm.trans (congrArg (fun f => f ≫ x) a.w)

theorem familyBaseChangeSection_fst (T : Over S) :
    ((familyBaseChangeSection p x hx).app T).left ≫ Limits.pullback.fst T.hom p = 𝟙 T.left :=
  Limits.pullback.lift_fst _ _ _

theorem familyBaseChangeSection_snd (T : Over S) :
    ((familyBaseChangeSection p x hx).app T).left ≫ Limits.pullback.snd T.hom p = T.hom ≫ x :=
  Limits.pullback.lift_snd _ _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.BaseChangeFunctor
