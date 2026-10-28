import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.MapOverBase

/-! # Over Pullback Reflection -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.OverPullbackReflection

noncomputable section

/-! A scheme pullback square can be reflected to its over category. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
theorem overPullbackOfLeft {S : Scheme.{u}} {W X Y Z : Over S}
    (f : W ⟶ X) (g : W ⟶ Y) (i : X ⟶ Z) (j : Y ⟶ Z)
    (h : IsPullback f.left g.left i.left j.left) : IsPullback f g i j := by
  exact IsPullback.of_map_of_faithful (Over.forget S) (f := f) (g := g) (h := i) (i := j) h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.OverPullbackReflection
