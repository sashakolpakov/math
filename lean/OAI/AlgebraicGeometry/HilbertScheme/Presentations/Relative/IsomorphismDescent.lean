import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.SourceIsomorphismTransport
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IteratedPullbackIsomorphism
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Isomorphism Descent -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.IsomorphismDescent

noncomputable section

/-! Stability and faithfully flat descent of the actual relative
base-change isomorphism condition. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X Y B B' T : Scheme.{u}}

theorem relativeMorphismBaseChange_isIso_comp_iff
    (f : X ⟶ Y) (q : Y ⟶ B) (b : B' ⟶ B) (c : T ⟶ B') :
    IsIso (MorphismIsomorphismLocus.relativeMorphismBaseChange f q (c ≫ b)) ↔
      IsIso (pullback.fst (pullback.fst (pullback.snd q b) c)
        (pullback.fst (pullback.fst q b) f)) := by
  rw [MorphismIsomorphismLocus.relativeMorphismBaseChange_isIso_iff, SourceIsomorphismTransport.isIso_pullback_snd_iff_fst,
    IteratedPullbackIsomorphism.isIso_pullback_fst_iterated_iff]
  have he := pullbackLeftPullbackSndIso_hom_fst q b c
  rw [← he, OpenPullbackIsomorphismTransport.isIso_pullback_fst_comp_left_iff]

theorem relativeMorphismBaseChange_isIso_comp
    (f : X ⟶ Y) (q : Y ⟶ B) (b : B' ⟶ B) (c : T ⟶ B')
    (h : IsIso (MorphismIsomorphismLocus.relativeMorphismBaseChange f q b)) :
    IsIso (MorphismIsomorphismLocus.relativeMorphismBaseChange f q (c ≫ b)) := by
  have hi : IsIso (pullback.fst (pullback.fst q b) f) := by
    rw [← SourceIsomorphismTransport.isIso_pullback_snd_iff_fst, ← MorphismIsomorphismLocus.relativeMorphismBaseChange_isIso_iff]
    exact h
  rw [relativeMorphismBaseChange_isIso_comp_iff]
  infer_instance

theorem relativeMorphismBaseChange_isIso_of_faithfullyFlat
    (f : X ⟶ Y) (q : Y ⟶ B) (b : B' ⟶ B) (c : T ⟶ B')
    [Surjective c] [Flat c] [QuasiCompact c]
    (h : IsIso (MorphismIsomorphismLocus.relativeMorphismBaseChange f q (c ≫ b))) :
    IsIso (MorphismIsomorphismLocus.relativeMorphismBaseChange f q b) := by
  rw [MorphismIsomorphismLocus.relativeMorphismBaseChange_isIso_iff, SourceIsomorphismTransport.isIso_pullback_snd_iff_fst]
  have hi := (relativeMorphismBaseChange_isIso_comp_iff f q b c).mp h
  exact MorphismProperty.of_pullback_fst_of_descendsAlong
    (P := MorphismProperty.isomorphisms Scheme)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := pullback.fst (pullback.snd q b) c)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hi

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.IsomorphismDescent
