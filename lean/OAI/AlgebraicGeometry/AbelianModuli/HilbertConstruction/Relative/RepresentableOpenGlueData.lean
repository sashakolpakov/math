import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.RepresentableTripleCycle
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-! # Representable Open Glue Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.RepresentableOpenGlueData

noncomputable section

/-! Representable open charts of a presheaf on schemes over a fixed base give actual gluing data in that over-category. This specializes the generic pullback construction used by Scheme.LocalRepresentability. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

def relativeOpenImmersions (S : Scheme.{u}) : MorphismProperty (Over S) :=
  (IsOpenImmersion : MorphismProperty Scheme.{u}).inverseImage (Over.forget S)

theorem relativeOpenImmersions_le_monomorphisms (S : Scheme.{u}) :
    relativeOpenImmersions S ≤ MorphismProperty.monomorphisms (Over S) := by
  intro A B f hf
  have : IsOpenImmersion f.left := hf
  change Mono f
  exact Over.mono_of_mono_left f

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
variable {ι : Type u} {X : ι → Over S}
variable {f : ∀ i, yoneda.obj (X i) ⟶ F}
variable (hf : ∀ i, (relativeOpenImmersions S).presheaf (f i))

open Functor.relativelyRepresentable in
def relativeRepresentableOpenGlueData : CategoryTheory.GlueData (Over S) where
  J := ι
  U := X
  V := fun (i, j) => (hf i).rep.pullback (f j)
  f i j := (hf i).rep.fst' (f j)
  f_mono i j := relativeOpenImmersions_le_monomorphisms S _
    ((hf j).property _ _ _ ((hf i).rep.isPullback' (f j)).flip)
  f_id i := (relativeOpenImmersions S).isIso_fst'_self
    (relativeOpenImmersions_le_monomorphisms S) (hf i)
  t i j := (hf i).rep.symmetry (hf j).rep
  t_id i := by
    apply (hf i).rep.hom_ext' <;>
      simp [(relativeOpenImmersions S).fst'_self_eq_snd
        (relativeOpenImmersions_le_monomorphisms S) (hf i)]
  t' i j k := RepresentableTripleCycle.relativeRepresentableTripleCycle (fun a => (hf a).rep) i j k
  t_fac i j k := by
    let h := fun a => (hf a).rep
    let c := RepresentableTripleCycle.relativeRepresentableTripleCycle h i j k
    apply (hf j).rep.hom_ext'
    · exact (Category.assoc c (pullback.snd _ _) ((hf j).rep.fst' (f i))).trans
        ((congrArg (fun z => c ≫ z) (pullback₃.snd_fst'_eq_p₁ (hf j).rep (f k) (f i))).trans
          ((RepresentableTripleCycle.relativeRepresentableTripleCycle_p₁ h i j k).trans
            ((Category.assoc (pullback.fst _ _) ((hf i).rep.symmetry (hf j).rep)
              ((hf j).rep.fst' (f i))).trans
              (congrArg (fun z => pullback.fst _ _ ≫ z)
                (symmetry_fst (hf i).rep (hf j).rep))).symm))
    · exact (Category.assoc c (pullback.snd _ _) ((hf j).rep.snd (f i))).trans
        ((congrArg (fun z => c ≫ z) (pullback₃.snd_snd_eq_p₃ (hf j).rep (f k) (f i))).trans
          ((RepresentableTripleCycle.relativeRepresentableTripleCycle_p₃ h i j k).trans
            ((Category.assoc (pullback.fst _ _) ((hf i).rep.symmetry (hf j).rep)
              ((hf j).rep.snd (f i))).trans
              (congrArg (fun z => pullback.fst _ _ ≫ z)
                (symmetry_snd (hf i).rep (hf j).rep))).symm))
  cocycle i j k := RepresentableTripleCycle.relativeRepresentableTripleCycle_cocycle (fun a => (hf a).rep) i j k

theorem relativeRepresentableOpenGlueData_open (i j : ι) :
    IsOpenImmersion ((relativeRepresentableOpenGlueData hf).f i j).left :=
  (hf j).property _ _ _ ((hf i).rep.isPullback' (f j)).flip

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.RepresentableOpenGlueData
