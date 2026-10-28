import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.FrameProducts
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

/-! # Fiber Frame Products -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberFrameProducts

noncomputable section

/-!
# Multiplication equations for genuine fiber frames persist under geometric change of test scheme
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.FrameProducts

variable {S : Scheme.{u}} {E : Over S} (L : Line.Bundles.LineBundle E.left)

/-- Pulling back an actual fiber multiplication and all normalized frames preserves their multiplication equation. -/
theorem product_pullback {T T' : Over S} (g : T' ⟶ T) (x y z : T ⟶ E)
    (x' y' z' : T' ⟶ E) (hx : g ≫ x = x') (hy : g ≫ y = y') (hz : g ≫ z = z')
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber L x) (Line.Fibers.fiber L y) (Line.Fibers.fiber L z))
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ⟶ Line.Fibers.fiber L x) (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ⟶ Line.Fibers.fiber L y)
    (u : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ⟶ Line.Fibers.fiber L z)
    (h : ∀ U : T.left.Opens, β.app U (s.app U (1 : Γ(T.left, U))) (t.app U (1 : Γ(T.left, U))) =
      u.app U (1 : Γ(T.left, U))) :
    ∀ U : T'.left.Opens, (Line.Fibers.pullBilinear L g x y z x' y' z' hx hy hz β).app U
      ((Line.Fibers.pullSection L g x x' hx s).app U (1 : Γ(T'.left, U)))
      ((Line.Fibers.pullSection L g y y' hy t).app U (1 : Γ(T'.left, U))) =
      (Line.Fibers.pullSection L g z z' hz u).app U (1 : Γ(T'.left, U)) :=
  Bilinear.FrameProducts.product_transport (Bilinear.BilinearPullback.pullback g.left (Line.Fibers.fiber_isLine L x) (Line.Fibers.fiber_isLine L y) β)
    (Line.Fibers.fiberPullbackIso L g x x' hx) (Line.Fibers.fiberPullbackIso L g y y' hy) (Line.Fibers.fiberPullbackIso L g z z' hz)
    (Bilinear.ContractionPullback.pulledSection g.left s)
    (Bilinear.ContractionPullback.pulledSection g.left t)
    (Bilinear.ContractionPullback.pulledSection g.left u)
    (Bilinear.FrameProducts.product_pullback g.left (Line.Fibers.fiber_isLine L x) (Line.Fibers.fiber_isLine L y) β s t u h)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberFrameProducts
