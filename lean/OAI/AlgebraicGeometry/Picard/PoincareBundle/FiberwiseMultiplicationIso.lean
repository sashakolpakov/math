import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FiberIsomorphisms
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.AlgebraTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

/-! # Fiberwise Multiplication Iso -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplicationIso

noncomputable section

/-!
# Transport the actual fiberwise multiplication and its kernel frames through a line-bundle isomorphism
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FiberIsomorphisms

variable {S : Scheme.{u}} {E A X : Over S} [GrpObj A] (p : E ⟶ A) (r : E ⟶ X)
  (L M : Line.Bundles.LineBundle E.left) (e : L.sheaf ≅ M.sheaf) (D : FiberwiseMultiplication.Multiplication p r L)

/-- The genuine bilinear product remains an isomorphism under an actual line-bundle isomorphism. -/
theorem product_isIso {T : Over S} (a b c : T ⟶ E) (h : FiberwiseMultiplication.ProductRel p r a b c) :
    IsIso (Bilinear.BilinearPullback.toHom (Line.FiberIsomorphisms.transportBilinear L M e a b c (D.product a b c h))) := by
  have hi : IsIso (Bilinear.BilinearPullback.toHom (D.product a b c h)) := D.product_isIso a b c h
  unfold Line.FiberIsomorphisms.transportBilinear
  rw [Bilinear.Transport.toHom_transport]
  infer_instance

/-- The actual transported product has the full geometric pullback law. -/
theorem product_natural {T T' : Over S} (g : T' ⟶ T) (a b c : T ⟶ E) (h : FiberwiseMultiplication.ProductRel p r a b c)
    (a' b' c' : T' ⟶ E) (h' : FiberwiseMultiplication.ProductRel p r a' b' c')
    (ha : g ≫ a = a') (hb : g ≫ b = b') (hc : g ≫ c = c') :
    Line.Fibers.pullBilinear M g a b c a' b' c' ha hb hc (Line.FiberIsomorphisms.transportBilinear L M e a b c (D.product a b c h)) =
      Line.FiberIsomorphisms.transportBilinear L M e a' b' c' (D.product a' b' c' h') := by
  rw [Line.FiberIsomorphisms.transportBilinear_pullback, D.product_natural g a b c h a' b' c' h' ha hb hc]

/-- The complete genuine multiplication is transported, with all unit and associativity laws proved. -/
def transportMultiplication : FiberwiseMultiplication.Multiplication p r M where
  product := fun {_T} a b c h => Line.FiberIsomorphisms.transportBilinear L M e a b c (D.product a b c h)
  product_isIso := fun {_T} a b c h => FiberwiseMultiplicationIso.product_isIso p r L M e D a b c h
  unitFrame := fun {_T} a ha => Line.FiberIsomorphisms.transportFrame L M e a (D.unitFrame a ha)
  unit_left := fun {_T} a x ha h U m =>
    Bilinear.AlgebraTransport.unit_left (D.product a x x h) (Line.FiberIsomorphisms.fiberIso L M e a) (Line.FiberIsomorphisms.fiberIso L M e x)
      (D.unitFrame a ha).hom (D.unit_left a x ha h) U m
  unit_right := fun {_T} x a ha h U m =>
    Bilinear.AlgebraTransport.unit_right (D.product x a x h) (Line.FiberIsomorphisms.fiberIso L M e x) (Line.FiberIsomorphisms.fiberIso L M e a)
      (D.unitFrame a ha).hom (D.unit_right x a ha h) U m
  associative := fun {_T} a b c ab bc d hab hbc had hcd U s t m =>
    Bilinear.AlgebraTransport.associative (D.product b c bc hbc) (D.product a bc d had)
      (D.product a b ab hab) (D.product ab c d hcd)
      (Line.FiberIsomorphisms.fiberIso L M e a) (Line.FiberIsomorphisms.fiberIso L M e b) (Line.FiberIsomorphisms.fiberIso L M e c)
      (Line.FiberIsomorphisms.fiberIso L M e ab) (Line.FiberIsomorphisms.fiberIso L M e bc) (Line.FiberIsomorphisms.fiberIso L M e d)
      (D.associative a b c ab bc d hab hbc had hcd) U s t m
  product_natural := fun {_T _T'} g a b c h a' b' c' h' ha hb hc =>
    FiberwiseMultiplicationIso.product_natural p r L M e D g a b c h a' b' c' h' ha hb hc
  unit_natural := fun {_T _T'} g a a' ha ha' hga =>
    Line.FiberIsomorphisms.transportFrame_natural L M e g a a' hga (D.unitFrame a ha) (D.unitFrame a' ha')
      (D.unit_natural g a a' ha ha' hga)

variable {B : Over S} [GrpObj B] (f : A ⟶ B) [IsMonHom f] (F : FiberwiseMultiplication.KernelFrames p r L f D)

attribute [local instance] Kernel.Scheme.kernelGroup

/-- The complete multiplicative kernel-frame system is transported through the actual line-bundle isomorphism. -/
def transportKernelFrames : FiberwiseMultiplication.KernelFrames p r M f (transportMultiplication p r L M e D) where
  frame := fun {_T} k a ha => Line.FiberIsomorphisms.transportFrame L M e a (F.frame k a ha)
  unit := fun {_T} a ha hk => congrArg (Line.FiberIsomorphisms.transportFrame L M e a) (F.unit a ha hk)
  multiplicative := fun {_T} k l m hm a b c ha hb hc hab U =>
    Bilinear.FrameProducts.product_transport (D.product a b c hab)
      (Line.FiberIsomorphisms.fiberIso L M e a) (Line.FiberIsomorphisms.fiberIso L M e b) (Line.FiberIsomorphisms.fiberIso L M e c)
      (F.frame k a ha).hom (F.frame l b hb).hom (F.frame m c hc).hom
      (F.multiplicative k l m hm a b c ha hb hc hab) U
  natural := fun {_T _T'} g k k' hgk a a' ha ha' hga =>
    Line.FiberIsomorphisms.transportFrame_natural L M e g a a' hga (F.frame k a ha) (F.frame k' a' ha')
      (F.natural g k k' hgk a a' ha ha' hga)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplicationIso
