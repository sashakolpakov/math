import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.TargetBaseChangeIsomorphism
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.OpenPullbackIsomorphismTransport

/-! # Target Restriction Isomorphism -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.TargetRestrictionIsomorphism

noncomputable section

/-! Isomorphism after parameter base change persists after restricting
the target of the original family morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X Y B T : Scheme.{u}}

theorem relativeMorphismBaseChange_restrict_target
    (f : X ⟶ Y) (q : Y ⟶ B) (U : Y.Opens) (g : T ⟶ B)
    (h : IsIso (MorphismIsomorphismLocus.relativeMorphismBaseChange f q g)) :
    IsIso (MorphismIsomorphismLocus.relativeMorphismBaseChange (f ∣_ U) (U.ι ≫ q) g) := by
  have hi : IsIso (MorphismIsomorphismLocus.relativeMorphismBaseChange (pullback.fst U.ι f) (U.ι ≫ q) g) := by
    apply TargetBaseChangeIsomorphism.relativeMorphismBaseChange_target_square f q U.ι (U.ι ≫ q) (𝟙 B)
      (by simp) g
    exact (congrArg (fun a : T ⟶ B => IsIso (MorphismIsomorphismLocus.relativeMorphismBaseChange f q a))
      (Category.comp_id g)).mpr h
  let e := (isPullback_morphismRestrict f U).isoPullback
  have he : e.hom ≫ pullback.fst U.ι f = f ∣_ U :=
    (isPullback_morphismRestrict f U).isoPullback_hom_fst
  rw [← he, SourceIsomorphismTransport.relativeMorphismBaseChange_sourceIso_iff]
  exact hi

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.TargetRestrictionIsomorphism
