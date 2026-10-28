import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.PullbackIsomorphismTransport

/-! # Source Isomorphism Transport -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.SourceIsomorphismTransport

noncomputable section

/-! Relative base-change isomorphism conditions are unchanged by
replacing the source total space by an isomorphic scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {W X Y B T : Scheme.{u}}

theorem isIso_pullback_snd_iff_fst (f : X ⟶ B) (g : Y ⟶ B) :
    IsIso (pullback.snd f g) ↔ IsIso (pullback.fst g f) := by
  rw [← isIso_comp_left_iff (pullbackSymmetry g f).hom, pullbackSymmetry_hom_comp_snd]

theorem relativeMorphismBaseChange_sourceIso_iff
    (f : X ⟶ Y) (q : Y ⟶ B) (g : T ⟶ B) (e : W ⟶ X) [IsIso e] :
    IsIso (MorphismIsomorphismLocus.relativeMorphismBaseChange (e ≫ f) q g) ↔
      IsIso (MorphismIsomorphismLocus.relativeMorphismBaseChange f q g) := by
  rw [MorphismIsomorphismLocus.relativeMorphismBaseChange_isIso_iff, MorphismIsomorphismLocus.relativeMorphismBaseChange_isIso_iff,
    isIso_pullback_snd_iff_fst, isIso_pullback_snd_iff_fst, PullbackIsomorphismTransport.isIso_pullback_fst_comp_right_iff]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.SourceIsomorphismTransport
