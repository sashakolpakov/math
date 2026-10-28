import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FrameRatioPullback

/-! # Fiber Frame Ratios -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberFrameRatios

noncomputable section

/-!
# Unit ratios of normalized fiber frames commute with actual geometric pullback
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits OAI.AlgebraicGeometry.Picard.PoincareBundle.FrameRatioPullback

variable {S : Scheme.{u}} {E : Over S} (L : Line.Bundles.LineBundle E.left)

/-- Equality of the normalized pulled sections identifies the whole pulled frame isomorphism. -/
theorem pullFrame_eq {T T' : Over S} (g : T' ⟶ T) (x : T ⟶ E) (x' : T' ⟶ E) (hx : g ≫ x = x')
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber L x) (s' : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T'.left ≅ Line.Fibers.fiber L x')
    (hs : Line.Fibers.pullSection L g x x' hx s.hom = s'.hom) :
    FrameRatioPullback.pullFrame g.left s ≪≫ Line.Fibers.fiberPullbackIso L g x x' hx = s' := by
  apply Iso.ext
  exact hs

/-- The obstruction of two compatible normalized fiber frames pulls back as a genuine global unit. -/
theorem frameRatio_naturality {T T' : Over S} (g : T' ⟶ T)
    (x : T ⟶ E) (x' : T' ⟶ E) (hx : g ≫ x = x')
    (s t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber L x) (s' t' : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T'.left ≅ Line.Fibers.fiber L x')
    (hs : Line.Fibers.pullSection L g x x' hx s.hom = s'.hom)
    (ht : Line.Fibers.pullSection L g x x' hx t.hom = t'.hom) :
    Line.FrameUnits.frameRatio s' t' = Units.map g.left.appTop.hom (Line.FrameUnits.frameRatio s t) := by
  calc
    Line.FrameUnits.frameRatio s' t' = Line.FrameUnits.frameRatio (FrameRatioPullback.pullFrame g.left s ≪≫ Line.Fibers.fiberPullbackIso L g x x' hx)
        (FrameRatioPullback.pullFrame g.left t ≪≫ Line.Fibers.fiberPullbackIso L g x x' hx) :=
      congrArg₂ Line.FrameUnits.frameRatio (pullFrame_eq L g x x' hx s s' hs).symm
        (pullFrame_eq L g x x' hx t t' ht).symm
    _ = Line.FrameUnits.frameRatio (FrameRatioPullback.pullFrame g.left s) (FrameRatioPullback.pullFrame g.left t) := FrameRatioPullback.frameRatio_postcomp _ _ _
    _ = Units.map g.left.appTop.hom (Line.FrameUnits.frameRatio s t) := FrameRatioPullback.frameRatio_pullFrame g.left s t

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberFrameRatios
