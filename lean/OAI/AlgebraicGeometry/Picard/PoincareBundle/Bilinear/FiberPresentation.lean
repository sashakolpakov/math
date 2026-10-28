import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.FiberComposition
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.CongrMapComparison
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Transport

/-! # Fiber Presentation -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.FiberPresentation

noncomputable section

/-! The actual isomorphism presenting a bilinear operation on specified scheme-valued line fibers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Transport OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LinePullback

theorem transported_formula {X Y : Scheme.{u}} (q : X ⟶ Y)
    {M N P : Y.Modules} {M' N' P' : X.Modules}
    (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N)
    (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N ≅ P)
    (a : (Scheme.Modules.pullback q).obj M ≅ M') (b : (Scheme.Modules.pullback q).obj N ≅ N')
    (c : (Scheme.Modules.pullback q).obj P ≅ P') :
    BilinearPullback.toHom (Transport.transport (BilinearPullback.pullback q hM hN (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P e.hom)) a b c) =
      ((Tensor.LinePullback.pullbackIso q M N hM hN ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b).symm ≪≫
        (Scheme.Modules.pullback q).mapIso e ≪≫ c).hom := by
  rw [Transport.toHom_transport, BilinearPullback.toHom_pullback]
  dsimp only [BilinearPullback.pulledHom, BilinearPullback.toHom]
  rw [Equiv.symm_apply_apply]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_hom,
    Tensor.CongrMapComparison.congr_inv, Category.assoc]

variable {S : Scheme.{u}} {E A : Over S} (L : Line.Bundles.LineBundle A.left)
  (p r t : E ⟶ A) (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (Line.Fibers.fiber L p) (Line.Fibers.fiber L r) ≅ Line.Fibers.fiber L t)

/-- Present a product on specified actual fibers by its tensor comparison and target comparison. -/
def atPointIso {T : Over S} (q : T ⟶ E) (x y z : T ⟶ A)
    (hx : q ≫ p = x) (hy : q ≫ r = y) (hz : q ≫ t = z) :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (Line.Fibers.fiber L x) (Line.Fibers.fiber L y) ≅ Line.Fibers.fiber L z :=
  (Tensor.FiberComposition.comparison L p r q x y hx hy).symm ≪≫
    (Scheme.Modules.pullback q.left).mapIso e ≪≫ Line.Fibers.fiberPullbackIso L q t z hz

/-- The presented isomorphism is exactly the native pulled-back bilinear map. -/
theorem atPoint_toHom {T : Over S} (q : T ⟶ E) (x y z : T ⟶ A)
    (hx : q ≫ p = x) (hy : q ≫ r = y) (hz : q ≫ t = z) :
    BilinearPullback.toHom (Line.Fibers.pullBilinear L q p r t x y z hx hy hz (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _ e.hom)) =
      (atPointIso L p r t e q x y z hx hy hz).hom :=
  transported_formula q.left (Line.Fibers.fiber_isLine L p) (Line.Fibers.fiber_isLine L r) e
    (Line.Fibers.fiberPullbackIso L q p x hx) (Line.Fibers.fiberPullbackIso L q r y hy) (Line.Fibers.fiberPullbackIso L q t z hz)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.FiberPresentation
