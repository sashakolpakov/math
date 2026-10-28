import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseQuotientTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplicationIso

/-! # Isomorphic Coordinate Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.IsomorphicCoordinateTransport

noncomputable section

/-! The actual coordinate quotient action commutes with isomorphisms of the line and its product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseKernelCoordinates
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplicationIso OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FiberIsomorphisms

variable {S : Scheme.{u}} {E A B X : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B]
  (p : E ⟶ A) (r : E ⟶ X) (f : A ⟶ B) [IsMonHom f]
  (replace : A ⊗ E ⟶ E) (hp : replace ≫ p = fst A E) (hr : replace ≫ r = snd A E ≫ r)
  (L M : Line.Bundles.LineBundle E.left) (e : L.sheaf ≅ M.sheaf)
  (D : FiberwiseMultiplication.Multiplication p r L) (K : FiberwiseMultiplication.KernelFrames p r L f D)

/-- Changing the actual line and its kernel frames conjugates the explicit kernel action. -/
theorem kernel_transport {T : Over S} (x y : T ⟶ E) (k : T ⟶ Kernel.Scheme.kernelObject f)
    (hxy : (x ≫ p) * (k ≫ Kernel.Scheme.kernelInclusion f) = y ≫ p) (hb : x ≫ r = y ≫ r) :
    FiberwiseKernelTransport.transport p r f replace hp hr M (FiberwiseMultiplicationIso.transportMultiplication p r L M e D)
      (FiberwiseMultiplicationIso.transportKernelFrames p r L M e D f K) x y k hxy hb =
    (Line.FiberIsomorphisms.fiberIso L M e x).inv ≫ FiberwiseKernelTransport.transport p r f replace hp hr L D K x y k hxy hb ≫
      (Line.FiberIsomorphisms.fiberIso L M e y).hom := by
  exact Bilinear.Transport.contractLeft_transport
    (D.product (FiberwiseKernelCoordinates.kernelPoint f replace k x) x y (FiberwiseKernelCoordinates.translation_product p r f replace hp hr x y k hxy hb))
    (Line.FiberIsomorphisms.fiberIso L M e (FiberwiseKernelCoordinates.kernelPoint f replace k x)) (Line.FiberIsomorphisms.fiberIso L M e x) (Line.FiberIsomorphisms.fiberIso L M e y)
    (K.frame k (FiberwiseKernelCoordinates.kernelPoint f replace k x) (FiberwiseKernelCoordinates.kernelPoint_group p f replace hp k x).symm).hom

/-- The kernel-difference construction gives the same conjugation for every actual quotient relation. -/
theorem quotient_transport {T : Over S} (x y : T ⟶ E) (h : FiberwiseQuotientTransport.Relation p r f x y) :
    FiberwiseQuotientTransport.transport p r f replace hp hr M (FiberwiseMultiplicationIso.transportMultiplication p r L M e D)
      (FiberwiseMultiplicationIso.transportKernelFrames p r L M e D f K) x y h =
    (Line.FiberIsomorphisms.fiberIso L M e x).inv ≫ FiberwiseQuotientTransport.transport p r f replace hp hr L D K x y h ≫
      (Line.FiberIsomorphisms.fiberIso L M e y).hom :=
  kernel_transport p r f replace hp hr L M e D K x y
    (Kernel.Pair.pointDifference f (x ≫ p) (y ≫ p) h.1)
    (Kernel.Linearization.difference_translates f (x ≫ p) (y ≫ p) h.1) h.2

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.IsomorphicCoordinateTransport
