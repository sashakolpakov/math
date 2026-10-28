import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Open Immersion Over Lift -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.OpenImmersionOverLift.Construction

noncomputable section

/-! Open-immersion lifts with the map to the base retained. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

theorem overOpenImmersion_hasLift {S : Scheme.{u}} {X Y T : Over S}
    (f : X ⟶ Y) [IsOpenImmersion f.left] (a : T ⟶ Y)
    (h : Set.range a.left ⊆ Set.range f.left) : ∃ b : T ⟶ X, b ≫ f = a := by
  let b := IsOpenImmersion.lift f.left a.left h
  have hb : b ≫ f.left = a.left := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Over.homMk b ?_, Over.OverMorphism.ext hb⟩
  rw [← f.w, ← Category.assoc, hb]
  exact a.w

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.OpenImmersionOverLift.Construction
