import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AssociativityOrigin
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AssociativityTransport
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AssociativityPullback
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberBilinearRigidity

/-! # Fiber Associativity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberAssociativity.Construction

noncomputable section

/-! Associativity of actual fiber products is detected at the origin
of a proper group parameter and survives every change of test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback

universe u

theorem fiberBilinear_associative_of_origin {k : Type u} [Field k]
    (T : Over (Spec (.of k))) [GrpObj T] [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]
    {E : Over (Spec (.of k))} (L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left)
    (x y z xy yz w : T ⟶ E) (x' y' z' xy' yz' w' : 𝟙_ (Over (Spec (.of k))) ⟶ E)
    (hx : η[T] ≫ x = x') (hy : η[T] ≫ y = y') (hz : η[T] ≫ z = z')
    (hxy : η[T] ≫ xy = xy') (hyz : η[T] ≫ yz = yz') (hw : η[T] ≫ w = w')
    (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L y) (Picard.PoincareBundle.Line.Fibers.fiber L z) (Picard.PoincareBundle.Line.Fibers.fiber L yz))
    (c : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L x) (Picard.PoincareBundle.Line.Fibers.fiber L yz) (Picard.PoincareBundle.Line.Fibers.fiber L w))
    (d : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L x) (Picard.PoincareBundle.Line.Fibers.fiber L y) (Picard.PoincareBundle.Line.Fibers.fiber L xy))
    (e : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L xy) (Picard.PoincareBundle.Line.Fibers.fiber L z) (Picard.PoincareBundle.Line.Fibers.fiber L w))
    [hdIso : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom d)] [heIso : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom e)]
    (h : ∀ (U : (𝟙_ (Over (Spec (.of k)))).left.Opens)
      (m : Γ(Picard.PoincareBundle.Line.Fibers.fiber L x', U)) (n : Γ(Picard.PoincareBundle.Line.Fibers.fiber L y', U)) (p : Γ(Picard.PoincareBundle.Line.Fibers.fiber L z', U)),
      (Picard.PoincareBundle.Line.Fibers.pullBilinear L η[T] x yz w x' yz' w' hx hyz hw c).app U m
        ((Picard.PoincareBundle.Line.Fibers.pullBilinear L η[T] y z yz y' z' yz' hy hz hyz b).app U n p) =
      (Picard.PoincareBundle.Line.Fibers.pullBilinear L η[T] xy z w xy' z' w' hxy hz hw e).app U
        ((Picard.PoincareBundle.Line.Fibers.pullBilinear L η[T] x y xy x' y' xy' hx hy hxy d).app U m n) p)
    (U : T.left.Opens) (m : Γ(Picard.PoincareBundle.Line.Fibers.fiber L x, U)) (n : Γ(Picard.PoincareBundle.Line.Fibers.fiber L y, U)) (p : Γ(Picard.PoincareBundle.Line.Fibers.fiber L z, U)) :
    c.app U m (b.app U n p) = e.app U (d.app U m n) p := by
  have hp := AssociativityTransport.Construction.lineBilinear_associative_of_transport
    (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback η[T].left (Picard.PoincareBundle.Line.Fibers.fiber_isLine L y) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L z) b)
    (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback η[T].left (Picard.PoincareBundle.Line.Fibers.fiber_isLine L x) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L yz) c)
    (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback η[T].left (Picard.PoincareBundle.Line.Fibers.fiber_isLine L x) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L y) d)
    (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback η[T].left (Picard.PoincareBundle.Line.Fibers.fiber_isLine L xy) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L z) e)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L η[T] x x' hx) (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L η[T] y y' hy)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L η[T] z z' hz) (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L η[T] xy xy' hxy)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L η[T] yz yz' hyz) (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L η[T] w w' hw) h
  exact @AssociativityOrigin.Construction.lineBilinear_associative_of_origin k inferInstance T inferInstance inferInstance inferInstance inferInstance
    (FiberBilinearRigidity.Construction.nativeFiberLine L x) (FiberBilinearRigidity.Construction.nativeFiberLine L y) (FiberBilinearRigidity.Construction.nativeFiberLine L z)
    (FiberBilinearRigidity.Construction.nativeFiberLine L xy) (FiberBilinearRigidity.Construction.nativeFiberLine L yz) (Picard.PoincareBundle.Line.Fibers.fiber L w) b c d e hdIso heIso hp U m n p

theorem fiberBilinear_associative_pullback {S : Scheme.{u}} {E T T' : Over S}
    (L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left) (r : T' ⟶ T)
    (x y z xy yz w : T ⟶ E) (x' y' z' xy' yz' w' : T' ⟶ E)
    (hx : r ≫ x = x') (hy : r ≫ y = y') (hz : r ≫ z = z')
    (hxy : r ≫ xy = xy') (hyz : r ≫ yz = yz') (hw : r ≫ w = w')
    (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L y) (Picard.PoincareBundle.Line.Fibers.fiber L z) (Picard.PoincareBundle.Line.Fibers.fiber L yz))
    (c : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L x) (Picard.PoincareBundle.Line.Fibers.fiber L yz) (Picard.PoincareBundle.Line.Fibers.fiber L w))
    (d : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L x) (Picard.PoincareBundle.Line.Fibers.fiber L y) (Picard.PoincareBundle.Line.Fibers.fiber L xy))
    (e : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L xy) (Picard.PoincareBundle.Line.Fibers.fiber L z) (Picard.PoincareBundle.Line.Fibers.fiber L w))
    (h : ∀ (U : T.left.Opens) (m : Γ(Picard.PoincareBundle.Line.Fibers.fiber L x, U)) (n : Γ(Picard.PoincareBundle.Line.Fibers.fiber L y, U)) (p : Γ(Picard.PoincareBundle.Line.Fibers.fiber L z, U)),
      c.app U m (b.app U n p) = e.app U (d.app U m n) p)
    (U : T'.left.Opens) (m : Γ(Picard.PoincareBundle.Line.Fibers.fiber L x', U)) (n : Γ(Picard.PoincareBundle.Line.Fibers.fiber L y', U)) (p : Γ(Picard.PoincareBundle.Line.Fibers.fiber L z', U)) :
    (Picard.PoincareBundle.Line.Fibers.pullBilinear L r x yz w x' yz' w' hx hyz hw c).app U m
      ((Picard.PoincareBundle.Line.Fibers.pullBilinear L r y z yz y' z' yz' hy hz hyz b).app U n p) =
    (Picard.PoincareBundle.Line.Fibers.pullBilinear L r xy z w xy' z' w' hxy hz hw e).app U
      ((Picard.PoincareBundle.Line.Fibers.pullBilinear L r x y xy x' y' xy' hx hy hxy d).app U m n) p :=
  Picard.PoincareBundle.Bilinear.AlgebraTransport.associative
    (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback r.left (Picard.PoincareBundle.Line.Fibers.fiber_isLine L y) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L z) b)
    (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback r.left (Picard.PoincareBundle.Line.Fibers.fiber_isLine L x) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L yz) c)
    (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback r.left (Picard.PoincareBundle.Line.Fibers.fiber_isLine L x) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L y) d)
    (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback r.left (Picard.PoincareBundle.Line.Fibers.fiber_isLine L xy) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L z) e)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L r x x' hx) (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L r y y' hy)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L r z z' hz) (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L r xy xy' hxy)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L r yz yz' hyz) (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L r w w' hw)
    (AssociativityPullback.Construction.lineBilinear_associative_pullback r.left (Picard.PoincareBundle.Line.Fibers.fiber_isLine L x) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L y) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L z)
      (Picard.PoincareBundle.Line.Fibers.fiber_isLine L xy) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L yz) b c d e h) U m n p

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberAssociativity.Construction
