import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.PrescribedUniqueness

/-! # Prescribed Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.PrescribedCriterion

noncomputable section

/-! Prescribed native pullback-section equations are equivalent to
literal equalities of the original projective marked sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem projectiveSections_pullback_eq_of_baseChange_eq
    {S T : Scheme.{u}} {n : ℕ} (f : T ⟶ S)
    (s t : Over.mk (𝟙 S) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n)
    (h : Projective.SectionBaseChange.projectiveSectionBaseChange s f = Projective.SectionBaseChange.projectiveSectionBaseChange t f) :
    (Over.pullback f).map s = (Over.pullback f).map t := by
  have he : (Projective.SectionBaseChange.projectiveSectionBaseChange s f).left ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n =
      (Projective.SectionBaseChange.projectiveSectionBaseChange t f).left ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n :=
    congrArg (fun a : Over.mk (𝟙 T) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver T n =>
      a.left ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n) h
  have hf : f ≫ s.left = f ≫ t.left :=
    (Projective.SectionBaseChange.projectiveSectionBaseChange_baseMap s f).symm.trans
      (he.trans (Projective.SectionBaseChange.projectiveSectionBaseChange_baseMap t f))
  have hp : pullback.fst (𝟙 S) f = pullback.snd (𝟙 S) f ≫ f :=
    (Category.comp_id _).symm.trans pullback.condition
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [Pullback.Comparisons.overPullback_map_left_fst, Pullback.Comparisons.overPullback_map_left_fst]
    change pullback.fst (𝟙 S) f ≫ s.left = pullback.fst (𝟙 S) f ≫ t.left
    rw [hp, Category.assoc, Category.assoc, hf]
  · exact ((Over.pullback f).map s).w.trans ((Over.pullback f).map t).w.symm

namespace HilbertFullLevelPullback
variable (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (H : Polynomial ℚ)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (Z : Over S) (c : Z ⟶ Hilbert.ParameterScheme.hilbertParameterScheme S n H)
    {m : ℕ} (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (q : Fin m → (Over.mk (𝟙 (PullbackParameter.HilbertLevelPullback.parameter S n H g Hm Hi N Z c).left) ⟶
      Projective.ProjectivePresentations.projectiveSpaceOver (PullbackParameter.HilbertLevelPullback.parameter S n H g Hm Hi N Z c).left n))

theorem prescribed_iff_markedPoint {T : Over S}
    (a : T ⟶ PullbackParameter.HilbertLevelPullback.parameter S n H g Hm Hi N Z c) :
    PrescribedLevelAmbientParameter.PrescribedFullLevelAmbientAt (PullbackParameter.HilbertLevelPullback.parameter S n H g Hm Hi N Z c)
      (PullbackParameter.HilbertLevelPullback.family S n H g Hm Hi N Z c).abelian (PullbackParameter.HilbertLevelPullback.family S n H g Hm Hi N Z c).level
      (PullbackParameter.HilbertLevelPullback.projective S n H g Hm Hi N Z c) labels q a.left ↔
    ∀ k, MarkedUniqueness.HilbertLevelPullback.markedPoint S n H g Hm Hi N (a ≫ PullbackParameter.HilbertLevelPullback.toFullLevel S n H g Hm Hi N Z c) (labels k) =
      Projective.SectionBaseChange.projectiveSectionBaseChange (q k) a.left := by
  constructor
  · intro h k
    exact PrescribedUniqueness.HilbertLevelPullback.markedPoint_of_prescribed S n H g Hm Hi N Z c labels q a h k
  · intro h k
    let t : Over.mk (𝟙 (PullbackParameter.HilbertLevelPullback.parameter S n H g Hm Hi N Z c).left) ⟶
        Projective.ProjectivePresentations.projectiveSpaceOver (PullbackParameter.HilbertLevelPullback.parameter S n H g Hm Hi N Z c).left n :=
      Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (PullbackParameter.HilbertLevelPullback.parameter S n H g Hm Hi N Z c)
        (PullbackParameter.HilbertLevelPullback.family S n H g Hm Hi N Z c).abelian (PullbackParameter.HilbertLevelPullback.family S n H g Hm Hi N Z c).level
        (PullbackParameter.HilbertLevelPullback.projective S n H g Hm Hi N Z c) (labels k)
    have hm : Projective.SectionBaseChange.projectiveSectionBaseChange t a.left = Projective.SectionBaseChange.projectiveSectionBaseChange (q k) a.left :=
      (PrescribedUniqueness.HilbertLevelPullback.parameterMarkedPoint_pullback S n H g Hm Hi N Z c a (labels k)).trans (h k)
    exact projectiveSections_pullback_eq_of_baseChange_eq a.left t (q k) hm

end HilbertFullLevelPullback

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.PrescribedCriterion
