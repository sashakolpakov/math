import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberPullbackComposition
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.PullbackComposition
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.TransportComposition

/-! # Fiber Bilinear Composition -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberBilinearComposition

noncomputable section

/-!
# Composition of actual geometric pullback of line-fiber bilinear operations
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.TransportComposition OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberPullbackComposition

variable {S : Scheme.{u}} {E : Over S} (L : Line.Bundles.LineBundle E.left)

/-- Pulling a genuine fiber-bilinear operation through two test-scheme maps equals pullback through their composite. -/
theorem pullBilinear_comp {T T' T'' : Over S} (g : T' ⟶ T) (h : T'' ⟶ T')
    (x y z : T ⟶ E) (x' y' z' : T' ⟶ E) (x'' y'' z'' : T'' ⟶ E)
    (hx : g ≫ x = x') (hy : g ≫ y = y') (hz : g ≫ z = z')
    (hx' : h ≫ x' = x'') (hy' : h ≫ y' = y'') (hz' : h ≫ z' = z'')
    (hx'' : (h ≫ g) ≫ x = x'') (hy'' : (h ≫ g) ≫ y = y'') (hz'' : (h ≫ g) ≫ z = z'')
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber L x) (Line.Fibers.fiber L y) (Line.Fibers.fiber L z)) :
    Line.Fibers.pullBilinear L h x' y' z' x'' y'' z'' hx' hy' hz'
      (Line.Fibers.pullBilinear L g x y z x' y' z' hx hy hz β) =
        Line.Fibers.pullBilinear L (h ≫ g) x y z x'' y'' z'' hx'' hy'' hz'' β := by
  unfold Line.Fibers.pullBilinear
  rw [Bilinear.TransportComposition.pullback_transport h.left ((Line.Fibers.fiber_isLine L x).pullback g.left) ((Line.Fibers.fiber_isLine L y).pullback g.left)
    (Line.Fibers.fiber_isLine L x') (Line.Fibers.fiber_isLine L y')
    (Bilinear.BilinearPullback.pullback g.left (Line.Fibers.fiber_isLine L x) (Line.Fibers.fiber_isLine L y) β)
    (Line.Fibers.fiberPullbackIso L g x x' hx) (Line.Fibers.fiberPullbackIso L g y y' hy) (Line.Fibers.fiberPullbackIso L g z z' hz),
    Bilinear.TransportComposition.transport_trans,
    FiberPullbackComposition.fiberIso_comp_exact L g h x x' x'' hx hx' hx'',
    FiberPullbackComposition.fiberIso_comp_exact L g h y y' y'' hy hy' hy'',
    FiberPullbackComposition.fiberIso_comp_exact L g h z z' z'' hz hz' hz'',
    ← Bilinear.TransportComposition.transport_trans]
  exact congrArg (fun γ => Bilinear.Transport.transport γ
    (Line.Fibers.fiberPullbackIso L (h ≫ g) x x'' hx'') (Line.Fibers.fiberPullbackIso L (h ≫ g) y y'' hy'')
    (Line.Fibers.fiberPullbackIso L (h ≫ g) z z'' hz''))
    (Bilinear.PullbackComposition.pullback_comp h.left g.left (Line.Fibers.fiber_isLine L x) (Line.Fibers.fiber_isLine L y) β)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberBilinearComposition
