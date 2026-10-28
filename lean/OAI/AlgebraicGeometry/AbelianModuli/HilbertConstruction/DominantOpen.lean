import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Dominant Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DominantOpen.DominantOpenLift

noncomputable section

/-! Dominance is preserved when a morphism factors through an open subscheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem dominant_lift {X Y Z : Scheme.{u}} (i : X ⟶ Z) [IsOpenImmersion i]
    (g : Y ⟶ Z) [IsDominant g] (h : Set.range g ⊆ Set.range i) :
    IsDominant (IsOpenImmersion.lift i g h) := by
  constructor
  apply i.isOpenEmbedding.isEmbedding.isInducing.dense_iff.mpr
  intro x
  rw [← Set.range_comp]
  have he : i ∘ IsOpenImmersion.lift i g h = g :=
    funext (fun y => congrArg (fun a : Y ⟶ Z => a y) (IsOpenImmersion.lift_fac i g h))
  rw [he]
  exact g.denseRange (i x)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DominantOpen.DominantOpenLift
