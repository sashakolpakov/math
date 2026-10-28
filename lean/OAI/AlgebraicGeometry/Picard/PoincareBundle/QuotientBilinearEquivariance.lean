import OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientProductComposition
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.PointNormalForm

/-! # Quotient Bilinear Equivariance -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientBilinearEquivariance

noncomputable section

/-!
# Full actual quotient-transport equivariance of the horizontal bilinear product

This is stated on arbitrary scheme-valued product points, not just the canonical coordinate
presentation. It is the native geometric equation needed for the global product gluing.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.AxisData OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
open OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientProductComposition OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.PointNormalForm

variable {S : Scheme.{u}} {A B X Y : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom f] [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)
  (hi : Biextension.Compatibility.Interchange L Dh Dv)
  (hc : KernelFrame.Centrality.Central f Kh) (ht : Kernel.FramesTransverseTransport.Transverse g Kv Dh)

include hi hc ht in
/-- The genuine horizontal product respects the complete quotient transport on every scheme-valued product pair. -/
theorem horizontal_bilinear {T : Over S} (a b c a' b' c' : T ⟶ A ⊗ X)
    (h : FiberwiseMultiplication.ProductRel (fst A X) (snd A X) a b c) (h' : FiberwiseMultiplication.ProductRel (fst A X) (snd A X) a' b' c')
    (ha : a ≫ (f ⊗ₘ g) = a' ≫ (f ⊗ₘ g)) (hb : b ≫ (f ⊗ₘ g) = b' ≫ (f ⊗ₘ g))
    (hc' : c ≫ (f ⊗ₘ g) = c' ≫ (f ⊗ₘ g)) :
    (Dh.product a' b' c' h').precomp
      (RectangularTransport.total f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf (Biextension.AxisData.toAxisData f g L Dh Dv Kh Kv) a a' ha)
      (RectangularTransport.total f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf (Biextension.AxisData.toAxisData f g L Dh Dv Kh Kv) b b' hb) =
    (Dh.product a b c h).postcomp
      (RectangularTransport.total f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf (Biextension.AxisData.toAxisData f g L Dh Dv Kh Kv) c c' hc') := by
  obtain ⟨x, y, z, rfl, rfl, rfl⟩ := Product.PointNormalForm.product_normalForm a b c h
  obtain ⟨u, v, w, rfl, rfl, rfl⟩ := Product.PointNormalForm.product_normalForm a' b' c' h'
  have hx := Product.PointNormalForm.images_fst f g x u z w ha
  have hy := Product.PointNormalForm.images_fst f g y v z w hb
  have hz := Product.PointNormalForm.images_snd f g x u z w ha
  rw [QuotientProductComposition.native_total f g L Dh Dv Kh Kv x u z w hx hz,
    QuotientProductComposition.native_total f g L Dh Dv Kh Kv y v z w hy hz,
    QuotientProductComposition.native_total f g L Dh Dv Kh Kv (x * y) (u * v) z w
      (Kernel.DifferenceProduct.product_images f x u y v hx hy) hz]
  change (CoordinateProductTranslations.productTo L Dh u v (u * v) w rfl).precomp
    (QuotientProductComposition.coordinateTotal f g L Dh Dv Kh Kv x u z w hx hz) (QuotientProductComposition.coordinateTotal f g L Dh Dv Kh Kv y v z w hy hz) =
    (CoordinateProductTranslations.productTo L Dh x y (x * y) z rfl).postcomp
      (QuotientProductComposition.coordinateTotal f g L Dh Dv Kh Kv (x * y) (u * v) z w
        (Kernel.DifferenceProduct.product_images f x u y v hx hy) hz)
  apply AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.ext
  intro U
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro n
  exact QuotientProductComposition.horizontal_product f g L Dh Dv Kh Kv hi hc ht x y u v z w hx hy hz U m n

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientBilinearEquivariance
