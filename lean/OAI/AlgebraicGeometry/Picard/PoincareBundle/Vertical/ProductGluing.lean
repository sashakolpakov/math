import OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.BilinearEquivariance
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.TransportGluing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductParameters
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberBilinearGluing

/-! # Product Gluing -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductGluing

noncomputable section

/-!
# The universal vertical sheaf product respects its genuine quotient transports
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductParameters
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.TransportGluing (square_images)
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.AxisData OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberBilinearGluing

variable {S : Scheme.{u}} {A B X Y : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom f] [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)

omit [IsCommMonObj A] [IsCommMonObj X] in
/-- The actual quotient transport, expressed between the two pulled-back universal input or output sheaves. -/
def productTransport {T : Over S} (p q : T ⟶ A ⊗ (X ⊗ X)) (i : A ⊗ (X ⊗ X) ⟶ A ⊗ X)
    (h : (p ≫ i) ≫ (f ⊗ₘ g) = (q ≫ i) ≫ (f ⊗ₘ g)) :
    (Scheme.Modules.pullback p.left).obj (Line.Fibers.fiber L i) ⟶ (Scheme.Modules.pullback q.left).obj (Line.Fibers.fiber L i) :=
  FiberBilinearGluing.fiberTransport L p q i
    (RectangularTransport.total f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf
      (Biextension.AxisData.toAxisData f g L Dh Dv Kh Kv) (p ≫ i) (q ≫ i) h)

variable (hi : Biextension.Compatibility.Interchange L Dh Dv)
  (hc : KernelFrame.Centrality.Central g Kv) (ht : Kernel.FramesTransverseTransport.Transverse f Kh Dv)

include hi hc ht in
/-- The universal product satisfies its full geometric bilinear gluing equation on every test scheme. -/
theorem vertical_equivariance {T : Over S} (p q : T ⟶ A ⊗ (X ⊗ X))
    (h : p ≫ (f ⊗ₘ (g ⊗ₘ g)) = q ≫ (f ⊗ₘ (g ⊗ₘ g))) :
    (Bilinear.BilinearPullback.pullback q.left (Line.Fibers.fiber_isLine L (ProductParameters.inputLeft A X))
      (Line.Fibers.fiber_isLine L (ProductParameters.inputRight A X)) (ProductParameters.globalProduct A X L Dv)).precomp
        (productTransport f g L Dh Dv Kh Kv p q (ProductParameters.inputLeft A X)
          (Product.TransportGluing.square_images _ _ _ _ (ProductParameters.inputLeft_naturality f g) p q h))
        (productTransport f g L Dh Dv Kh Kv p q (ProductParameters.inputRight A X)
          (Product.TransportGluing.square_images _ _ _ _ (ProductParameters.inputRight_naturality f g) p q h)) =
    (Bilinear.BilinearPullback.pullback p.left (Line.Fibers.fiber_isLine L (ProductParameters.inputLeft A X))
      (Line.Fibers.fiber_isLine L (ProductParameters.inputRight A X)) (ProductParameters.globalProduct A X L Dv)).postcomp
        (productTransport f g L Dh Dv Kh Kv p q (ProductParameters.outputPoint A X)
          (Product.TransportGluing.square_images _ _ _ _ (ProductParameters.outputPoint_naturality f g) p q h)) := by
  apply FiberBilinearGluing.equivariance_of_fibers
  rw [ProductParameters.globalProduct_pullback, ProductParameters.globalProduct_pullback]
  exact BilinearEquivariance.vertical_bilinear f g L Dh Dv Kh Kv hi hc ht
    _ _ _ _ _ _ (ProductParameters.parameterRelation A X p) (ProductParameters.parameterRelation A X q) _ _ _

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductGluing
