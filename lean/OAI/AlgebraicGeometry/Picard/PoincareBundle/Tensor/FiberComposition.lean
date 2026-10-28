import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.CompositionForward
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberPullbackComposition

/-! # Fiber Composition -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.FiberComposition

noncomputable section

/-! Tensor products of actual line-fiber comparisons respect composition of test maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LinePullback

theorem rectangle_path {C : Type*} [Category C] {A B D E F G H I : C}
    (d : A ≅ B) (z : B ≅ D) (r : D ≅ E) (u : B ≅ F) (t : F ≅ E)
    (w : E ≅ G) (v : F ≅ H) (w' : H ≅ G) (c : A ≅ I) (r' : I ≅ H)
    (hn : z ≪≫ r = u ≪≫ t) (ht : t ≪≫ w = v ≪≫ w') (hc : d ≪≫ u ≪≫ v = c ≪≫ r') :
    (d ≪≫ z) ≪≫ r ≪≫ w = c ≪≫ r' ≪≫ w' := by
  calc
    (d ≪≫ z) ≪≫ r ≪≫ w = d ≪≫ (z ≪≫ r) ≪≫ w := by simp only [Iso.trans_assoc]
    _ = d ≪≫ (u ≪≫ t) ≪≫ w := congrArg (fun v => d ≪≫ v ≪≫ w) hn
    _ = (d ≪≫ u ≪≫ v) ≪≫ w' := by
      rw [Iso.trans_assoc, ht]
      simp only [Iso.trans_assoc]
    _ = c ≪≫ r' ≪≫ w' := (congrArg (fun v => v ≪≫ w') hc).trans (Iso.trans_assoc _ _ _)

variable {S : Scheme.{u}} {E A : Over S} (L : Line.Bundles.LineBundle A.left)
  (p r : E ⟶ A)

/-- Evaluate an external tensor of two line fibers with prescribed coordinate identifications. -/
def comparison {T : Over S} (q : T ⟶ E) (x y : T ⟶ A) (hx : q ≫ p = x) (hy : q ≫ r = y) :
    (Scheme.Modules.pullback q.left).obj (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (Line.Fibers.fiber L p) (Line.Fibers.fiber L r)) ≅
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (Line.Fibers.fiber L x) (Line.Fibers.fiber L y) :=
  LinePullback.pullbackIso q.left (Line.Fibers.fiber L p) (Line.Fibers.fiber L r) (Line.Fibers.fiber_isLine L p) (Line.Fibers.fiber_isLine L r) ≪≫
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (Line.Fibers.fiberPullbackIso L q p x hx) (Line.Fibers.fiberPullbackIso L q r y hy)

/-- The comparison is coherent through an additional arbitrary change of test scheme. -/
theorem composition {T U : Over S} (q : T ⟶ E) (a : U ⟶ T)
    (x y : T ⟶ A) (hx : q ≫ p = x) (hy : q ≫ r = y)
    (x' y' : U ⟶ A) (hx' : a ≫ x = x') (hy' : a ≫ y = y')
    (hqx : (a ≫ q) ≫ p = x') (hqy : (a ≫ q) ≫ r = y') :
    (Scheme.Modules.pullback a.left).mapIso (comparison L p r q x y hx hy) ≪≫
      LinePullback.pullbackIso a.left (Line.Fibers.fiber L x) (Line.Fibers.fiber L y) (Line.Fibers.fiber_isLine L x) (Line.Fibers.fiber_isLine L y) ≪≫
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (Line.Fibers.fiberPullbackIso L a x x' hx') (Line.Fibers.fiberPullbackIso L a y y' hy') =
    (Scheme.Modules.pullbackComp a.left q.left).app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (Line.Fibers.fiber L p) (Line.Fibers.fiber L r)) ≪≫
      comparison L p r (a ≫ q) x' y' hqx hqy := by
  let cp := (Scheme.Modules.pullbackComp a.left q.left).app (Line.Fibers.fiber L p)
  let cr := (Scheme.Modules.pullbackComp a.left q.left).app (Line.Fibers.fiber L r)
  let ct := (Scheme.Modules.pullbackComp a.left q.left).app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (Line.Fibers.fiber L p) (Line.Fibers.fiber L r))
  let d := (Scheme.Modules.pullback a.left).mapIso
    (LinePullback.pullbackIso q.left (Line.Fibers.fiber L p) (Line.Fibers.fiber L r) (Line.Fibers.fiber_isLine L p) (Line.Fibers.fiber_isLine L r))
  let u := LinePullback.pullbackIso a.left ((Scheme.Modules.pullback q.left).obj (Line.Fibers.fiber L p))
    ((Scheme.Modules.pullback q.left).obj (Line.Fibers.fiber L r)) ((Line.Fibers.fiber_isLine L p).pullback q.left)
    ((Line.Fibers.fiber_isLine L r).pullback q.left)
  have hn := LineIsoCoherence.naturality a.left ((Line.Fibers.fiber_isLine L p).pullback q.left)
    (Line.Fibers.fiber_isLine L x) ((Line.Fibers.fiber_isLine L r).pullback q.left) (Line.Fibers.fiber_isLine L y)
    (Line.Fibers.fiberPullbackIso L q p x hx) (Line.Fibers.fiberPullbackIso L q r y hy)
  have hc : d ≪≫ u ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr cp cr = ct ≪≫
      LinePullback.pullbackIso (a.left ≫ q.left) (Line.Fibers.fiber L p) (Line.Fibers.fiber L r) (Line.Fibers.fiber_isLine L p) (Line.Fibers.fiber_isLine L r) :=
    CompositionForward.composition a.left q.left (Line.Fibers.fiber L p) (Line.Fibers.fiber L r)
      (Line.Fibers.fiber_isLine L p) (Line.Fibers.fiber_isLine L r)
  have hp := FiberPullbackComposition.fiberIso_comp_exact L q a p x x' hx hx' hqx
  have hr := FiberPullbackComposition.fiberIso_comp_exact L q a r y y' hy hy' hqy
  let z := (Scheme.Modules.pullback a.left).mapIso
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (Line.Fibers.fiberPullbackIso L q p x hx) (Line.Fibers.fiberPullbackIso L q r y hy))
  let b := LinePullback.pullbackIso a.left (Line.Fibers.fiber L x) (Line.Fibers.fiber L y) (Line.Fibers.fiber_isLine L x) (Line.Fibers.fiber_isLine L y)
  let t := AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr ((Scheme.Modules.pullback a.left).mapIso (Line.Fibers.fiberPullbackIso L q p x hx))
    ((Scheme.Modules.pullback a.left).mapIso (Line.Fibers.fiberPullbackIso L q r y hy))
  let w := AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (Line.Fibers.fiberPullbackIso L a x x' hx') (Line.Fibers.fiberPullbackIso L a y y' hy')
  let w' := AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (Line.Fibers.fiberPullbackIso L (a ≫ q) p x' hqx) (Line.Fibers.fiberPullbackIso L (a ≫ q) r y' hqy)
  have ht : t ≪≫ w = AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr cp cr ≪≫ w' :=
    (CongrComposition.trans _ _ _ _).trans
      ((congrArg₂ (fun ep er => AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr ep er) hp hr).trans
        (CongrComposition.trans _ _ _ _).symm)
  have he : (Scheme.Modules.pullback a.left).mapIso (comparison L p r q x y hx hy) = d ≪≫ z :=
    Functor.mapIso_trans (Scheme.Modules.pullback a.left) _ _
  exact (congrArg (fun v => v ≪≫ b ≪≫ w) he).trans
    (rectangle_path d z b u t w (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr cp cr) w' ct
      (LinePullback.pullbackIso (a.left ≫ q.left) (Line.Fibers.fiber L p) (Line.Fibers.fiber L r) (Line.Fibers.fiber_isLine L p) (Line.Fibers.fiber_isLine L r)) hn ht hc)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.FiberComposition
