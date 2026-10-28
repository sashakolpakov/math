import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberPullbackComposition
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.FixedRestriction

/-! # Fixed Fiber Symmetry -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FixedFiberSymmetry

noncomputable section

/-! A fiber comparison for an invariant map is normalized on every fixed restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberPullbackComposition OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.FixedRestriction

theorem normalized {S : Scheme.{u}} {T U E : Over S} (L : Line.Bundles.LineBundle E.left)
    (g : T ⟶ T) (p : U ⟶ T) (hp : p ≫ g = p) (x : T ⟶ E) (hx : g ≫ x = x) :
    (Scheme.Modules.pullback p.left).mapIso (Line.Fibers.fiberPullbackIso L g x x hx) =
      Tensor.FixedRestriction.comparison p.left g.left (congrArg Over.Hom.left hp) (Line.Fibers.fiber L x) := by
  let e := Line.Fibers.fiberPullbackIso L p x (p ≫ x) rfl
  have h := FiberPullbackComposition.fiberIso_comp L g p p hp x x (p ≫ x) hx rfl rfl
  apply Iso.ext
  apply (cancel_mono e.hom).mp
  exact congrArg Iso.hom h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FixedFiberSymmetry
