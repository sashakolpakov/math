import Mathlib.CategoryTheory.Iso

/-! # Frame Transition Transport -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.FrameTransitionTransport

/-! Transport a frame transition through two proved frame identifications. -/

open _root_.CategoryTheory
universe u v

theorem frameTransition_of_iso_eq {C : Type u} [Category.{v} C] {A B : C}
    {e f e' f' : A ≅ B} (s : B ⟶ B)
    (he : e = e') (hf : f = f') (h : e'.hom = f'.hom ≫ s) :
    e.hom = f.hom ≫ s := by
  rw [he, hf]
  exact h

end OAI.AlgebraicGeometry.SheafCohomology.Projective.FrameTransitionTransport
