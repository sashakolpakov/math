import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.SourceIsomorphismTransport
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IteratedPullbackIsomorphism

/-! # Target Base Change Isomorphism -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.TargetBaseChangeIsomorphism

noncomputable section

/-! An isomorphism of a family after base change stays an isomorphism
after any compatible change of its target and coefficient base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X Y B Y' B' T : Scheme.{u}}

theorem relativeMorphismBaseChange_target_square
    (f : X ⟶ Y) (q : Y ⟶ B) (a : Y' ⟶ Y) (q' : Y' ⟶ B') (b : B' ⟶ B)
    (hab : a ≫ q = q' ≫ b) (c : T ⟶ B')
    (h : IsIso (MorphismIsomorphismLocus.relativeMorphismBaseChange f q (c ≫ b))) :
    IsIso (MorphismIsomorphismLocus.relativeMorphismBaseChange (pullback.fst a f) q' c) := by
  have hI : IsIso (pullback.fst (pullback.fst q (c ≫ b)) f) := by
    rw [← SourceIsomorphismTransport.isIso_pullback_snd_iff_fst, ← MorphismIsomorphismLocus.relativeMorphismBaseChange_isIso_iff]
    exact h
  let k : pullback q' c ⟶ pullback q (c ≫ b) :=
    pullback.lift (pullback.fst q' c ≫ a) (pullback.snd q' c) (by
      rw [Category.assoc, hab, ← Category.assoc, pullback.condition, Category.assoc])
  have hk : k ≫ pullback.fst q (c ≫ b) = pullback.fst q' c ≫ a := pullback.lift_fst _ _ _
  have hi : IsIso (pullback.fst (pullback.fst q' c ≫ a) f) := by
    rw [← hk, ← IteratedPullbackIsomorphism.isIso_pullback_fst_iterated_iff]
    infer_instance
  rw [MorphismIsomorphismLocus.relativeMorphismBaseChange_isIso_iff, SourceIsomorphismTransport.isIso_pullback_snd_iff_fst,
    IteratedPullbackIsomorphism.isIso_pullback_fst_iterated_iff]
  exact hi

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.TargetBaseChangeIsomorphism
