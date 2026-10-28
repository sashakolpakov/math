import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Unramified Pullback Refinements -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedPullbackRefinements

noncomputable section

/-! Formal unramifiedness of a base change is preserved by open source restriction and transported across iterated pullbacks. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem unramified_pullback_precomp_open {X Y S T : Scheme.{u}}
    (f : X ⟶ S) (j : Y ⟶ X) [IsOpenImmersion j] (b : T ⟶ S)
    [FormallyUnramified (pullback.snd f b)] : FormallyUnramified (pullback.snd (j ≫ f) b) := by
  have hj : FormallyUnramified j := inferInstance
  have hp : FormallyUnramified (pullback.snd j (pullback.fst f b)) :=
    MorphismProperty.of_isPullback (P := @FormallyUnramified)
      (IsPullback.of_hasPullback j (pullback.fst f b)) hj
  have hc : FormallyUnramified (pullback.snd j (pullback.fst f b) ≫ pullback.snd f b) :=
    MorphismProperty.comp_mem (@FormallyUnramified) _ _ hp inferInstance
  have H : FormallyUnramified ((pullbackRightPullbackFstIso f b j).inv ≫
      pullback.snd j (pullback.fst f b) ≫ pullback.snd f b) :=
    MorphismProperty.comp_mem (@FormallyUnramified) _ _ inferInstance hc
  exact (congrArg FormallyUnramified (pullbackRightPullbackFstIso_inv_snd_snd f b j)).mp H

theorem unramified_iterated_pullback {X S T U : Scheme.{u}}
    (f : X ⟶ S) (b : T ⟶ S) (c : U ⟶ T)
    [FormallyUnramified (pullback.snd f (c ≫ b))] :
    FormallyUnramified (pullback.snd (pullback.snd f b) c) := by
  have H : FormallyUnramified ((pullbackLeftPullbackSndIso f b c).hom ≫ pullback.snd f (c ≫ b)) :=
    MorphismProperty.comp_mem (@FormallyUnramified) _ _ inferInstance inferInstance
  exact (congrArg FormallyUnramified (pullbackLeftPullbackSndIso_hom_snd f b c)).mp H

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedPullbackRefinements
