import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Pullback Composition Map -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PullbackCompositionMap.Construction

noncomputable section

/-! The literal pullback map of a morphism to the source of a family is a base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y Z B : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ X) (b : B ⟶ Y)

def pullbackCompositionMap : pullback (g ≫ f) b ⟶ pullback f b :=
  pullback.map _ _ _ _ g (𝟙 B) (𝟙 Y) (by simp) (by simp)

@[reassoc (attr := simp)]
theorem pullbackCompositionMap_snd :
    pullbackCompositionMap f g b ≫ pullback.snd f b = pullback.snd (g ≫ f) b := by
  simp [pullbackCompositionMap]

theorem pullbackCompositionMap_isPullback :
    IsPullback (pullbackCompositionMap f g b) (pullback.fst (g ≫ f) b) (pullback.fst f b) g := by
  refine .of_right (t := (IsPullback.of_hasPullback f b).flip) ?_ ?_
  · simpa [pullbackCompositionMap] using (IsPullback.of_hasPullback (g ≫ f) b).flip
  · simp [pullbackCompositionMap]

instance pullbackCompositionMap_isClosedImmersion [IsClosedImmersion g] :
    IsClosedImmersion (pullbackCompositionMap f g b) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (pullbackCompositionMap_isPullback f g b).flip inferInstance

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PullbackCompositionMap.Construction
