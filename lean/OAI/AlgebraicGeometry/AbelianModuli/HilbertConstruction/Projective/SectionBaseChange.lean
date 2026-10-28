import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.PointSectionNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.BaseChangeIsoProjections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.BaseFunctoriality

/-! # Section Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SectionBaseChange

noncomputable section

/-! Native base change of a section of relative projective space.
The section is characterized by its projection to the original space;
this gives exact composition and equality after a common parameter map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

private theorem triple_projection
    {C : Type*} [Category* C] {A B D E F G : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (j : E ⟶ F)
    (k : D ⟶ F) (p : B ⟶ G) (r : G ⟶ F) (f : A ⟶ G)
    (hc : c ≫ j = k) (hb : b ≫ k = p ≫ r) (ha : a ≫ p = f) :
    (a ≫ b ≫ c) ≫ j = f ≫ r := by
  calc
    (a ≫ b ≫ c) ≫ j = a ≫ (b ≫ (c ≫ j)) := by simp only [Category.assoc]
    _ = a ≫ (b ≫ k) := congrArg (fun z => a ≫ (b ≫ z)) hc
    _ = a ≫ (p ≫ r) := congrArg (fun z => a ≫ z) hb
    _ = (a ≫ p) ≫ r := (Category.assoc _ _ _).symm
    _ = f ≫ r := congrArg (fun z => z ≫ r) ha

def projectiveSectionBaseChange {S T : Scheme.{u}} {n : ℕ}
    (s : Over.mk (𝟙 S) ⟶ ProjectivePresentations.projectiveSpaceOver S n) (f : T ⟶ S) :
    Over.mk (𝟙 T) ⟶ ProjectivePresentations.projectiveSpaceOver T n :=
  Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map s ≫
    (SpaceBaseChange.projectiveSpaceOverBaseChangeIso f n).inv

theorem projectiveSectionBaseChange_baseMap {S T : Scheme.{u}} {n : ℕ}
    (s : Over.mk (𝟙 S) ⟶ ProjectivePresentations.projectiveSpaceOver S n) (f : T ⟶ S) :
    (projectiveSectionBaseChange s f).left ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n = f ≫ s.left := by
  exact triple_projection (Functor.LaxMonoidal.ε (Over.pullback f)).left
    ((Over.pullback f).map s).left (SpaceBaseChange.projectiveSpaceOverBaseChangeIso f n).inv.left
    (RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n) (pullback.fst (ProjectivePresentations.projectiveSpaceOver S n).hom f)
    (pullback.fst (𝟙 S) f) s.left f
    (BaseChangeIsoProjections.projectiveSpaceOverBaseChangeIso_inv_baseMap f n)
    (Pullback.Comparisons.overPullback_map_left_fst s f) (Family.PointSectionNaturality.pullbackUnitComparison_fst f)

theorem projectiveSections_eq_of_baseMap {S T : Scheme.{u}} {n : ℕ} (f : T ⟶ S)
    (s t : Over.mk (𝟙 T) ⟶ ProjectivePresentations.projectiveSpaceOver T n)
    (h : s.left ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n = t.left ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n) : s = t := by
  apply Over.OverMorphism.ext
  exact (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback f n).hom_ext h (s.w.trans t.w.symm)

theorem projectiveSectionBaseChange_comp {S T U : Scheme.{u}} {n : ℕ}
    (s : Over.mk (𝟙 S) ⟶ ProjectivePresentations.projectiveSpaceOver S n) (f : T ⟶ S) (g : U ⟶ T) :
    projectiveSectionBaseChange (projectiveSectionBaseChange s f) g =
      projectiveSectionBaseChange s (g ≫ f) := by
  apply projectiveSections_eq_of_baseMap (g ≫ f)
  let q := projectiveSectionBaseChange (projectiveSectionBaseChange s f) g
  have hq : q.left ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap (g ≫ f) n = (g ≫ f) ≫ s.left :=
    (congrArg (fun a => q.left ≫ a) (RelativeProjective.BaseFunctoriality.relativeProjectiveBaseMap_comp f g n)).trans
      ((Category.assoc q.left (RelativeProjective.BaseMaps.relativeProjectiveBaseMap g n) (RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n)).symm.trans
        ((congrArg (fun a => a ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n)
          (projectiveSectionBaseChange_baseMap (projectiveSectionBaseChange s f) g)).trans
          ((Category.assoc g (projectiveSectionBaseChange s f).left (RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n)).trans
            ((congrArg (fun a => g ≫ a) (projectiveSectionBaseChange_baseMap s f)).trans
              (Category.assoc g f s.left).symm))))
  exact hq.trans (projectiveSectionBaseChange_baseMap s (g ≫ f)).symm

theorem projectiveSectionBaseChange_eq_of_comp_eq {S T U : Scheme.{u}} {n : ℕ}
    (s : Over.mk (𝟙 S) ⟶ ProjectivePresentations.projectiveSpaceOver S n) (f : T ⟶ S)
    (a b : U ⟶ T) (h : a ≫ f = b ≫ f) :
    projectiveSectionBaseChange (projectiveSectionBaseChange s f) a =
      projectiveSectionBaseChange (projectiveSectionBaseChange s f) b :=
  (projectiveSectionBaseChange_comp s f a).trans
    ((congrArg (projectiveSectionBaseChange s) h).trans (projectiveSectionBaseChange_comp s f b).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SectionBaseChange
