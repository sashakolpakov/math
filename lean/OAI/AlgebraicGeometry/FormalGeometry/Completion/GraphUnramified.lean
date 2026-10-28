import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-! # Graph Unramified -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.GraphUnramified.Construction

noncomputable section

/-!
# Completion: an open graph detects an unramified factor

The graph is a base change of the factor's diagonal. Its openness descends
along a faithfully flat quasi-compact cover of the diagonal target.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- Openness of this graph descends to openness of the second map's diagonal. -/
theorem diagonal_isOpenImmersion_of_open_graph {X N Y : Scheme.{u}}
    (h : X ⟶ N) [Surjective h] [Flat h] [QuasiCompact h] (g : N ⟶ Y)
    [IsOpenImmersion (pullback.lift (𝟙 X) h (by simp) : X ⟶ pullback (h ≫ g) g)] :
    IsOpenImmersion (pullback.diagonal g) := by
  let b := pullback.map (h ≫ g) g g g h (𝟙 N) (𝟙 Y) (by simp) (by simp)
  have hb : b = (pullbackRightPullbackFstIso g g h).inv ≫ pullback.snd h (pullback.fst g g) := by
    apply pullback.hom_ext <;> simp [b]
  have : Surjective b := by rw [hb]; infer_instance
  have : Flat b := by rw [hb]; infer_instance
  have : QuasiCompact b := by rw [hb]; infer_instance
  exact MorphismProperty.of_isPullback_of_descendsAlong
      (P := @IsOpenImmersion) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      (pullback_lift_diagonal_isPullback h g).flip
      ⟨⟨‹Surjective b›, ‹Flat b›⟩, ‹QuasiCompact b›⟩ inferInstance

/-- Openness of this graph forces the second map to be formally unramified. -/
theorem formallyUnramified_of_open_graph {X N Y : Scheme.{u}}
    (h : X ⟶ N) [Surjective h] [Flat h] [QuasiCompact h] (g : N ⟶ Y)
    [IsOpenImmersion (pullback.lift (𝟙 X) h (by simp) : X ⟶ pullback (h ≫ g) g)] :
    FormallyUnramified g := by
  have := diagonal_isOpenImmersion_of_open_graph h g
  infer_instance

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.GraphUnramified.Construction
