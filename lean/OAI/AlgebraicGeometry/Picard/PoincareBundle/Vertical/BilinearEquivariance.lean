import OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.QuotientComposition
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.PointNormalForm

/-! # Bilinear Equivariance -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.BilinearEquivariance

noncomputable section

/-!
# Full actual quotient-transport equivariance of the vertical bilinear product
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.AxisData OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
open OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateTransverseTranslations OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientProductComposition OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.PointNormalForm

section NormalForm

variable {S : Scheme.{u}} {A X : Over S} [GrpObj X]

/-- Actual vertical product points share a first coordinate and multiply their second coordinates. -/
theorem product_normalForm {T : Over S} (a b c : T ⟶ A ⊗ X)
    (h : FiberwiseMultiplication.ProductRel (snd A X) (fst A X) a b c) :
    ∃ (x : T ⟶ A) (z w : T ⟶ X), a = lift x z ∧ b = lift x w ∧ c = lift x (z * w) := by
  refine ⟨a ≫ fst A X, a ≫ snd A X, b ≫ snd A X, (lift_comp_fst_snd a).symm, ?_, ?_⟩
  · apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]
      exact h.2.1.symm
    · rw [lift_snd]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]
      exact h.2.2.symm
    · rw [lift_snd]
      exact h.1.symm

end NormalForm

variable {S : Scheme.{u}} {A B X Y : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom f] [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)
  (hi : Biextension.Compatibility.Interchange L Dh Dv)
  (hc : KernelFrame.Centrality.Central g Kv)
  (ht : Kernel.FramesTransverseTransport.Transverse f Kh Dv)

include hi hc ht in
/-- The genuine vertical product respects complete quotient transport on every scheme-valued product triple. -/
theorem vertical_bilinear {T : Over S} (a b c a' b' c' : T ⟶ A ⊗ X)
    (h : FiberwiseMultiplication.ProductRel (snd A X) (fst A X) a b c) (h' : FiberwiseMultiplication.ProductRel (snd A X) (fst A X) a' b' c')
    (ha : a ≫ (f ⊗ₘ g) = a' ≫ (f ⊗ₘ g)) (hb : b ≫ (f ⊗ₘ g) = b' ≫ (f ⊗ₘ g))
    (hc' : c ≫ (f ⊗ₘ g) = c' ≫ (f ⊗ₘ g)) :
    (Dv.product a' b' c' h').precomp
      (RectangularTransport.total f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf (Biextension.AxisData.toAxisData f g L Dh Dv Kh Kv) a a' ha)
      (RectangularTransport.total f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf (Biextension.AxisData.toAxisData f g L Dh Dv Kh Kv) b b' hb) =
    (Dv.product a b c h).postcomp
      (RectangularTransport.total f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf (Biextension.AxisData.toAxisData f g L Dh Dv Kh Kv) c c' hc') := by
  obtain ⟨x, z, w, rfl, rfl, rfl⟩ := product_normalForm a b c h
  obtain ⟨y, u, v, rfl, rfl, rfl⟩ := product_normalForm a' b' c' h'
  have hx := Product.PointNormalForm.images_fst f g x y z u ha
  have hz := Product.PointNormalForm.images_snd f g x y z u ha
  have hw := Product.PointNormalForm.images_snd f g x y w v hb
  rw [QuotientProductComposition.native_total f g L Dh Dv Kh Kv x y z u hx hz,
    QuotientProductComposition.native_total f g L Dh Dv Kh Kv x y w v hx hw,
    QuotientProductComposition.native_total f g L Dh Dv Kh Kv x y (z * w) (u * v) hx
      (Kernel.DifferenceProduct.product_images g z u w v hz hw)]
  change (CoordinateTransverseTranslations.verticalProductTo L Dv u v (u * v) y rfl).precomp
    (QuotientProductComposition.coordinateTotal f g L Dh Dv Kh Kv x y z u hx hz) (QuotientProductComposition.coordinateTotal f g L Dh Dv Kh Kv x y w v hx hw) =
    (CoordinateTransverseTranslations.verticalProductTo L Dv z w (z * w) x rfl).postcomp
      (QuotientProductComposition.coordinateTotal f g L Dh Dv Kh Kv x y (z * w) (u * v) hx
        (Kernel.DifferenceProduct.product_images g z u w v hz hw))
  apply AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.ext
  intro U
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro n
  exact QuotientComposition.vertical_product f g L Dh Dv Kh Kv hi hc ht x y z w u v hx hz hw U m n

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.BilinearEquivariance
