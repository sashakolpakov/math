import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Morphism Fiber Equality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.MorphismFiberEquality

noncomputable section

/-! Equality after actual base change gives equality on every
actual scheme map whose base coordinate factors through that change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem pullbackMorphism_eq_on_lift {S T W : Scheme.{0}} (s : T ⟶ S)
    {X Y : Over S} (f g : X ⟶ Y)
    (he : (Over.pullback s).map f = (Over.pullback s).map g)
    (q : W ⟶ X.left) (t : W ⟶ T) (hq : q ≫ X.hom = t ≫ s) : q ≫ f.left = q ≫ g.left := by
  have h := congrArg (fun v => v.left ≫ pullback.fst Y.hom s) he
  change pullback.lift (pullback.fst X.hom s ≫ f.left) (pullback.snd X.hom s) _ ≫ pullback.fst Y.hom s =
    pullback.lift (pullback.fst X.hom s ≫ g.left) (pullback.snd X.hom s) _ ≫ pullback.fst Y.hom s at h
  rw [pullback.lift_fst, pullback.lift_fst] at h
  have h' := congrArg (fun v => pullback.lift q t hq ≫ v) h
  simpa only [← Category.assoc, pullback.lift_fst] using h'

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.MorphismFiberEquality
