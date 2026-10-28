import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplicationPullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationCoordinates

/-! # Frames Pullback -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesPullback

noncomputable section

/-!
# Pullback of the complete actual multiplicative kernel-frame system
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplicationPullback
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.LineBilinear OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.LineSection

variable {S : Scheme.{u}} {K E A B X : Over S} [GrpObj A] [GrpObj B]
  (p : E ⟶ A) (r : E ⟶ X) (q : K ⟶ E) (f : A ⟶ B) [IsMonHom f]
  (L : Line.Bundles.LineBundle E.left) (D : FiberwiseMultiplication.Multiplication p r L) (F : FiberwiseMultiplication.KernelFrames p r L f D)

attribute [local instance] Kernel.Scheme.kernelGroup

omit [GrpObj A] [IsMonHom f] in
/-- The included kernel coordinate is unchanged when a source point is mapped to its original point. -/
theorem imageKernel {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (a : T ⟶ K)
    (ha : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ (q ≫ p)) : k ≫ Kernel.Scheme.kernelInclusion f = (a ≫ q) ≫ p := by
  simpa only [Category.assoc] using ha

/-- Pull back the actual frame on the represented kernel point through the canonical fiber comparison. -/
def frame {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (a : T ⟶ K)
    (ha : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ (q ≫ p)) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber (L.pullback q.left) a :=
  Pulled.LineSection.transportFrame q L a (a ≫ q) rfl (F.frame k (a ≫ q) (imageKernel p q f k a ha))

/-- The complete multiplicative kernel-frame system pulls back with its actual multiplication. -/
def pullbackFrames : FiberwiseMultiplication.KernelFrames (q ≫ p) (q ≫ r) (L.pullback q.left) f (FiberwiseMultiplicationPullback.pullbackMultiplication p r q L D) where
  frame := fun {_T} k a ha => FramesPullback.frame p r q f L D F k a ha
  unit := fun {_T} a ha hk => by
    change Pulled.LineSection.transportFrame q L a (a ≫ q) rfl (F.frame 1 (a ≫ q) (imageKernel p q f 1 a hk)) =
      Pulled.LineSection.transportFrame q L a (a ≫ q) rfl (D.unitFrame (a ≫ q) (FiberwiseMultiplicationPullback.imageUnit p q a ha))
    rw [F.unit _ (FiberwiseMultiplicationPullback.imageUnit p q a ha)]
  multiplicative := fun {_T} k l m hm a b c ha hb hc hab U =>
    Bilinear.FrameProducts.product_transport
      (D.product _ _ _ (FiberwiseMultiplicationPullback.imageRel p r q a b c hab))
      (Pulled.LineBilinear.fiberComparison q L a (a ≫ q) rfl).symm (Pulled.LineBilinear.fiberComparison q L b (b ≫ q) rfl).symm
      (Pulled.LineBilinear.fiberComparison q L c (c ≫ q) rfl).symm
      (F.frame k (a ≫ q) (imageKernel p q f k a ha)).hom
      (F.frame l (b ≫ q) (imageKernel p q f l b hb)).hom
      (F.frame m (c ≫ q) (imageKernel p q f m c hc)).hom
      (F.multiplicative k l m hm _ _ _ _ _ _ (FiberwiseMultiplicationPullback.imageRel p r q a b c hab)) U
  natural := fun {_T _T'} g k k' hgk a a' ha ha' hga =>
    Pulled.LineSection.transportFrame_natural q L g a (a ≫ q) rfl a' (a' ≫ q) rfl hga (FiberwiseMultiplicationPullback.image_natural q g a a' hga)
      _ _ (F.natural g k k' hgk (a ≫ q) (a' ≫ q) (imageKernel p q f k a ha)
        (imageKernel p q f k' a' ha') (FiberwiseMultiplicationPullback.image_natural q g a a' hga))

variable {p r}

/-- Equal actual coordinate morphisms also identify the full kernel-frame data. -/
def congrCoordinates {p' : E ⟶ A} {r' : E ⟶ X} (hp : p = p') (hr : r = r') :
    FiberwiseMultiplication.KernelFrames p' r' L f (MultiplicationCoordinates.congrCoordinates D hp hr) := by
  cases hp
  cases hr
  exact F

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesPullback
