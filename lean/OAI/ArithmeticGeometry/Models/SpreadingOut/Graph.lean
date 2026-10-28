import OAI.ArithmeticGeometry.Models.SpreadingOut.Image
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Graph -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.Graph.Construction

noncomputable section

/-! Closed graph embeddings into products with separated schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

/-- A morphism whose composite is a preimmersion is itself a preimmersion. -/
theorem preimmersion_of_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsPreimmersion (f ≫ g)] :
    IsPreimmersion f where
  isEmbedding := Topology.IsEmbedding.of_comp f.continuous g.continuous (f ≫ g).isEmbedding
  stalkMap_surjective x := by
    have h := (f ≫ g).stalkMap_surjective x
    rw [Scheme.Hom.stalkMap_comp] at h
    exact Function.Surjective.of_comp h

/-- Closed immersions cancel a separated postcomposition. -/
theorem closed_immersion_of_comp_of_separated
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated g] [IsClosedImmersion (f ≫ g)] : IsClosedImmersion f := by
  have : IsPreimmersion f := preimmersion_of_comp f g
  have : IsProper f := IsProper.of_comp f g
  exact IsClosedImmersion.of_isPreimmersion f f.isClosedMap.isClosed_range

/-- A closed embedding in one factor remains closed when its graph in a
separated second factor is added. -/
theorem pullback_lift_closedImmersion_of_right
    {W X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [IsSeparated f]
    (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) [IsClosedImmersion b] :
    IsClosedImmersion (pullback.lift a b h) := by
  have : IsClosedImmersion (pullback.lift a b h ≫ pullback.snd f g) := by
    rw [pullback.lift_snd]
    infer_instance
  exact closed_immersion_of_comp_of_separated _ (pullback.snd f g)

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.Graph.Construction
