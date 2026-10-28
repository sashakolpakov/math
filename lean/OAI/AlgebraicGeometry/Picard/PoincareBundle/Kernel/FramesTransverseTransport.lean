import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplicationIso
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesPullback

/-! # Frames Transverse Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport

noncomputable section

/-!
# Transport of the transverse law for actual multiplicative kernel frames
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplicationPullback
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.LineBilinear OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FiberIsomorphisms OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplicationIso

variable {S : Scheme.{u}} {E A B X K : Over S} [GrpObj A] [GrpObj B] [GrpObj X]
  {p : E ⟶ A} {r : E ⟶ X} (f : A ⟶ B) [IsMonHom f]
  {L : Line.Bundles.LineBundle E.left} {Dh : FiberwiseMultiplication.Multiplication p r L}

/-- A kernel frame respects the actual bilinear multiplication in the other coordinate. -/
def Transverse (F : FiberwiseMultiplication.KernelFrames p r L f Dh) (Dv : FiberwiseMultiplication.Multiplication r p L) : Prop :=
  ∀ (T : Over S) (k : T ⟶ Kernel.Scheme.kernelObject f) (a b c : T ⟶ E)
    (ha : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ p) (hb : k ≫ Kernel.Scheme.kernelInclusion f = b ≫ p)
    (hc : k ≫ Kernel.Scheme.kernelInclusion f = c ≫ p) (h : FiberwiseMultiplication.ProductRel r p a b c) (U : T.left.Opens),
    (Dv.product a b c h).app U ((F.frame k a ha).hom.app U (1 : Γ(T.left, U)))
      ((F.frame k b hb).hom.app U (1 : Γ(T.left, U))) = (F.frame k c hc).hom.app U (1 : Γ(T.left, U))

/-- Equality of coordinate maps preserves the full transverse law of the actual kernel frames. -/
theorem congrCoordinates (F : FiberwiseMultiplication.KernelFrames p r L f Dh) (Dv : FiberwiseMultiplication.Multiplication r p L)
    {p' : E ⟶ A} {r' : E ⟶ X} (hp : p = p') (hr : r = r') (ht : Transverse f F Dv) :
    Transverse f (FramesPullback.congrCoordinates f L Dh F hp hr)
      (MultiplicationCoordinates.congrCoordinates Dv hr hp) := by
  cases hp
  cases hr
  exact ht

/-- Actual geometric pullback preserves transverse multiplication of the complete frame system. -/
theorem pullback (q : K ⟶ E) (F : FiberwiseMultiplication.KernelFrames p r L f Dh) (Dv : FiberwiseMultiplication.Multiplication r p L)
    (ht : Transverse f F Dv) :
    Transverse f (FramesPullback.pullbackFrames p r q f L Dh F)
      (FiberwiseMultiplicationPullback.pullbackMultiplication r p q L Dv) := by
  intro T k a b c ha hb hc h U
  exact Bilinear.FrameProducts.product_transport (Dv.product _ _ _ (FiberwiseMultiplicationPullback.imageRel r p q a b c h))
    (Pulled.LineBilinear.fiberComparison q L a (a ≫ q) rfl).symm (Pulled.LineBilinear.fiberComparison q L b (b ≫ q) rfl).symm
    (Pulled.LineBilinear.fiberComparison q L c (c ≫ q) rfl).symm
    (F.frame k (a ≫ q) (FramesPullback.imageKernel p q f k a ha)).hom
    (F.frame k (b ≫ q) (FramesPullback.imageKernel p q f k b hb)).hom
    (F.frame k (c ≫ q) (FramesPullback.imageKernel p q f k c hc)).hom
    (ht T k _ _ _ (FramesPullback.imageKernel p q f k a ha)
      (FramesPullback.imageKernel p q f k b hb)
      (FramesPullback.imageKernel p q f k c hc) (FiberwiseMultiplicationPullback.imageRel r p q a b c h)) U

/-- A genuine isomorphism of line sheaves preserves the full transverse frame law. -/
theorem iso (M : Line.Bundles.LineBundle E.left) (e : L.sheaf ≅ M.sheaf)
    (F : FiberwiseMultiplication.KernelFrames p r L f Dh) (Dv : FiberwiseMultiplication.Multiplication r p L) (ht : Transverse f F Dv) :
    Transverse f (FiberwiseMultiplicationIso.transportKernelFrames p r L M e Dh f F) (FiberwiseMultiplicationIso.transportMultiplication r p L M e Dv) := by
  intro T k a b c ha hb hc h U
  exact Bilinear.FrameProducts.product_transport (Dv.product a b c h)
    (Line.FiberIsomorphisms.fiberIso L M e a) (Line.FiberIsomorphisms.fiberIso L M e b) (Line.FiberIsomorphisms.fiberIso L M e c)
    (F.frame k a ha).hom (F.frame k b hb).hom (F.frame k c hc).hom
    (ht T k a b c ha hb hc h) U

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport
