import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SectionBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.LevelFrameParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.EmbeddingPullbackComposition

/-! # Section Equations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SectionEquations

noncomputable section

/-! Equations on the native pullback sections give equations on
the corresponding sections of relative projective space. Full-level
marks satisfy this comparison over every test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

private theorem eq_after_factored_precomposition
    {C : Type*} [Category* C] {W X Y Z : C}
    (a : W ⟶ X) (p : X ⟶ Y) (f : W ⟶ Y) (s t : Y ⟶ Z)
    (ha : a ≫ p = f) (hst : p ≫ s = p ≫ t) : f ≫ s = f ≫ t := by
  rw [← ha, Category.assoc, hst, ← Category.assoc]

theorem projectiveSections_baseChange_eq_of_pullback_eq {S T : Scheme.{u}} {n : ℕ}
    (f : T ⟶ S) (s t : Over.mk (𝟙 S) ⟶ ProjectivePresentations.projectiveSpaceOver S n) :
    (Over.pullback f).map s = (Over.pullback f).map t →
      SectionBaseChange.projectiveSectionBaseChange s f = SectionBaseChange.projectiveSectionBaseChange t f := by
  intro h
  let p := pullback.fst (𝟙 S) f
  let k := pullback.fst (ProjectivePresentations.projectiveSpaceOver S n).hom f
  let a : T ⟶ pullback (𝟙 S) f := pullback.lift f (𝟙 T) (by simp)
  have ha : a ≫ p = f := pullback.lift_fst _ _ _
  have hs : ((Over.pullback f).map s).left ≫ k = p ≫ s.left :=
    Pullback.Comparisons.overPullback_map_left_fst s f
  have ht : ((Over.pullback f).map t).left ≫ k = p ≫ t.left :=
    Pullback.Comparisons.overPullback_map_left_fst t f
  have hst : p ≫ s.left = p ≫ t.left := hs.symm.trans
    ((congrArg (fun m : (Over.pullback f).obj (Over.mk (𝟙 S)) ⟶
      (Over.pullback f).obj (ProjectivePresentations.projectiveSpaceOver S n) => m.left ≫ k) h).trans ht)
  have hbase : f ≫ s.left = f ≫ t.left :=
    eq_after_factored_precomposition a p f s.left t.left ha hst
  exact SectionBaseChange.projectiveSections_eq_of_baseMap f _ _
    ((SectionBaseChange.projectiveSectionBaseChange_baseMap s f).trans
      (hbase.trans (SectionBaseChange.projectiveSectionBaseChange_baseMap t f).symm))

theorem fullLevelMarkedProjectivePoint_baseChange
    {S : Scheme.{u}} (Z : Over S) {g N : ℕ}
    (A : Abelian.Schemes.AbelianScheme g Z.left) (level : A.FullLevel N)
    (P : ProjectivePresentations.ProjectivePresentation A.scheme) {T : Scheme.{u}} (f : T ⟶ Z.left)
    (c : Multiplicative (Fin (2 * g) → ZMod N)) :
    SectionBaseChange.projectiveSectionBaseChange (Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint Z A level P c) f =
      Over.homMk ((A.pullback f).fullLevelGlobalSection (level.pullback f) c)
        ((A.pullback f).fullLevelGlobalSection_comp (level.pullback f) c) ≫
          (P.baseChange f).embedding := by
  let x := A.fullLevelGlobalSection level c
  let y := (A.pullback f).fullLevelGlobalSection (level.pullback f) c
  have hy : y ≫ pullback.fst A.scheme.hom f = f ≫ x :=
    A.fullLevelGlobalSection_pullback level f c
  have hi : (P.baseChange f).embedding.left ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap f P.dimension =
      pullback.fst A.scheme.hom f ≫ P.embedding.left :=
    EmbeddingPullbackComposition.ProjectivePullback.embedding_baseMap P.embedding f
  apply SectionBaseChange.projectiveSections_eq_of_baseMap f
  have h : (y ≫ (P.baseChange f).embedding.left) ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap f P.dimension =
      f ≫ (x ≫ P.embedding.left) :=
    (Category.assoc _ _ _).trans ((congrArg (fun z => y ≫ z) hi).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ P.embedding.left) hy).trans (Category.assoc _ _ _))))
  exact (SectionBaseChange.projectiveSectionBaseChange_baseMap (Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint Z A level P c) f).trans h.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SectionEquations
