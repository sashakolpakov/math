import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

/-! # Pull Section Equality -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.PullSectionEquality

/-! Normalized section pullback retains exactly the same equality as ordinary sheaf-map pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ContractionPullback

variable {S : Scheme.{u}} {A T U : Over S} (L : Line.Bundles.LineBundle A.left)
  (g : U ⟶ T) (a : T ⟶ A) (b : U ⟶ A) (h : g ≫ a = b)
  (s t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ⟶ Line.Fibers.fiber L a)

/-- The actual unit and fiber comparison isomorphisms may be canceled from normalized pullback. -/
theorem pullback_map_eq (he : Line.Fibers.pullSection L g a b h s = Line.Fibers.pullSection L g a b h t) :
    (Scheme.Modules.pullback g.left).map s = (Scheme.Modules.pullback g.left).map t := by
  apply (cancel_epi (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g.left).inv).mp
  apply (cancel_mono (Line.Fibers.fiberPullbackIso L g a b h).hom).mp
  exact he

end OAI.AlgebraicGeometry.Picard.PoincareBundle.PullSectionEquality
