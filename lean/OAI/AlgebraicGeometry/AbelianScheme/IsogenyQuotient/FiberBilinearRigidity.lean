import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BilinearRigidity
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberBilinearComposition

/-! # Fiber Bilinear Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberBilinearRigidity.Construction

noncomputable section

/-! Equality of actual invertible fiber-bilinear operations is
detected at the origin of a proper smooth connected group parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

universe u

theorem bilinearTransport_injective {S : Scheme.{u}} {M N P M' N' P' : S.Modules}
    (a : M ≅ M') (b : N ≅ N') (c : P ≅ P') :
    Function.Injective (fun β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P => Picard.PoincareBundle.Bilinear.Transport.transport β a b c) := by
  intro f g h
  have hr := congrArg (fun δ => Picard.PoincareBundle.Bilinear.Transport.transport δ a.symm b.symm c.symm) h
  simpa only [Picard.PoincareBundle.Bilinear.TransportComposition.transport_trans, Iso.self_symm_id,
    Picard.PoincareBundle.Bilinear.TransportComposition.transport_refl] using hr

def nativeFiberLine {S : Scheme.{u}} {T E : Over S} (L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left) (x : T ⟶ E) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle T.left := ⟨Picard.PoincareBundle.Line.Fibers.fiber L x, Picard.PoincareBundle.Line.Fibers.fiber_isLine L x⟩

theorem fiberBilinear_eq_of_origin {k : Type u} [Field k]
    (T : Over (Spec (.of k))) [GrpObj T] [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]
    {E : Over (Spec (.of k))} (L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left) (x y z : T ⟶ E)
    (x' y' z' : 𝟙_ (Over (Spec (.of k))) ⟶ E)
    (hx : η[T] ≫ x = x') (hy : η[T] ≫ y = y') (hz : η[T] ≫ z = z')
    (b c : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L x) (Picard.PoincareBundle.Line.Fibers.fiber L y) (Picard.PoincareBundle.Line.Fibers.fiber L z))
    [hbIso : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom b)] [hcIso : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom c)]
    (h : Picard.PoincareBundle.Line.Fibers.pullBilinear L η[T] x y z x' y' z' hx hy hz b = Picard.PoincareBundle.Line.Fibers.pullBilinear L η[T] x y z x' y' z' hx hy hz c) :
    b = c := by
  have hp := bilinearTransport_injective (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L η[T] x x' hx)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L η[T] y y' hy) (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L η[T] z z' hz) h
  exact @BilinearRigidity.Construction.lineBilinear_eq_of_origin k inferInstance T inferInstance inferInstance inferInstance inferInstance
    (nativeFiberLine L x) (nativeFiberLine L y) (nativeFiberLine L z) b c hbIso hcIso hp

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberBilinearRigidity.Construction
