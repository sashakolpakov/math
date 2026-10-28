import OAI.AlgebraicGeometry.FormalGeometry.Completion.FppfSheafSectionDescent
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Fppf Pair Lift -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FppfPairLift

noncomputable section

/-! Two maps into the target of an fppf cover lift simultaneously
after two actual pullbacks. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Construction

universe u
variable {S : Scheme.{u}} {X Y T : Over S} (q : X ⟶ Y)
  [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]

theorem overPullbackFst_fppf (a : T ⟶ Y) :
    Flat (pullback.fst a q).left ∧ Surjective (pullback.fst a q).left ∧
      LocallyOfFinitePresentation (pullback.fst a q).left := by
  have h := (IsPullback.of_hasPullback a q).map (Over.forget S)
  change IsPullback (pullback.fst a q).left (pullback.snd a q).left a.left q.left at h
  exact ⟨MorphismProperty.of_isPullback (P := @Flat) h.flip inferInstance,
    MorphismProperty.of_isPullback (P := @Surjective) h.flip inferInstance,
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) h.flip inferInstance⟩

theorem fppf_lift_pair (a b : T ⟶ Y) :
    ∃ (U : Over S) (p : U ⟶ T) (x y : U ⟶ X),
      Flat p.left ∧ Surjective p.left ∧ LocallyOfFinitePresentation p.left ∧
        p ≫ a = x ≫ q ∧ p ≫ b = y ≫ q := by
  let v := pullback.fst a q
  let w := pullback.fst (v ≫ b) q
  obtain ⟨hvf, hvs, hvp⟩ := overPullbackFst_fppf q a
  obtain ⟨hwf, hws, hwp⟩ := overPullbackFst_fppf q (v ≫ b)
  have : Flat v.left := hvf
  have : Surjective v.left := hvs
  have : LocallyOfFinitePresentation v.left := hvp
  have : Flat w.left := hwf
  have : Surjective w.left := hws
  have : LocallyOfFinitePresentation w.left := hwp
  refine ⟨_, w ≫ v, w ≫ pullback.snd a q, pullback.snd (v ≫ b) q,
    inferInstanceAs (Flat (w.left ≫ v.left)), inferInstanceAs (Surjective (w.left ≫ v.left)),
    inferInstanceAs (LocallyOfFinitePresentation (w.left ≫ v.left)), ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, Category.assoc]
  · exact (Category.assoc _ _ _).trans pullback.condition

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FppfPairLift
