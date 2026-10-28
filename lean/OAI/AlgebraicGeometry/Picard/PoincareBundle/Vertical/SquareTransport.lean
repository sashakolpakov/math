import OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductGluing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.SquareTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.OverSquare

/-! # Square Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.SquareTransport

noncomputable section

/-!
# Native vertical product-square descent has exactly the genuine product transports
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductParameters
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.AxisData OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductGluing
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.TransportGluing (square_images)
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.SquareTransport (testBase firstPoint secondPoint point_images originalDatum)

variable {S : Scheme.{u}} {A B X Y : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom f] [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)
  (hc : RectangularTransport.Commutes f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf (Biextension.AxisData.toAxisData f g L Dh Dv Kh Kv))

variable (i : A ⊗ (X ⊗ X) ⟶ A ⊗ X) (j : B ⊗ (Y ⊗ Y) ⟶ B ⊗ Y)
  (hij : (f ⊗ₘ (g ⊗ₘ g)) ≫ j = i ≫ (f ⊗ₘ g))

/-- Pulling the original datum through an input or output square produces its actual transported sheaf maps. -/
theorem pulledHom_transport {T : Over S} (base : T ⟶ B ⊗ (Y ⊗ Y)) (p q : T ⟶ A ⊗ (X ⊗ X))
    (hp : p ≫ (f ⊗ₘ (g ⊗ₘ g)) = base) (hq : q ≫ (f ⊗ₘ (g ⊗ₘ g)) = base) :
    (Recovered.OverSquare.pulledDatum (f ⊗ₘ g) (f ⊗ₘ (g ⊗ₘ g)) i j hij.symm
      (Product.SquareTransport.originalDatum f g L Dh Dv Kh Kv hc)).hom base (i₁ := PUnit.unit) (i₂ := PUnit.unit) p q hp hq =
    ProductGluing.productTransport f g L Dh Dv Kh Kv p q i
      (Product.TransportGluing.square_images _ _ _ _ hij p q (hp.trans hq.symm)) := by
  rw [Recovered.OverSquare.pulledHom]
  unfold ProductGluing.productTransport
  exact (FiberBilinearGluing.fiberTransport_eq_comp L p q i
    (RectangularTransport.total f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf (Biextension.AxisData.toAxisData f g L Dh Dv Kh Kv)
      (p ≫ i) (q ≫ i) (Product.TransportGluing.square_images _ _ _ _ hij p q (hp.trans hq.symm)))).symm

/-- The underlying kernel-pair gluing equals that same genuine transport on the common test object. -/
theorem relationGluing_transport :
    (Geometric.CechInvariant.relationGluing (f ⊗ₘ (g ⊗ₘ g)).left
      (Recovered.OverSquare.underlyingDatum (f ⊗ₘ g) (f ⊗ₘ (g ⊗ₘ g)) i j hij.symm
        (Product.SquareTransport.originalDatum f g L Dh Dv Kh Kv hc))).hom =
      ProductGluing.productTransport f g L Dh Dv Kh Kv (Product.SquareTransport.firstPoint (f ⊗ₘ (g ⊗ₘ g))) (Product.SquareTransport.secondPoint (f ⊗ₘ (g ⊗ₘ g))) i
        (Product.TransportGluing.square_images _ _ _ _ hij _ _ (Product.SquareTransport.point_images (f ⊗ₘ (g ⊗ₘ g)))) :=
  pulledHom_transport f g L Dh Dv Kh Kv hc i j hij
    (UnderlyingDescent.baseMap (Product.SquareTransport.testBase (f ⊗ₘ (g ⊗ₘ g)))) _ _
    (UnderlyingDescent.coverMap_base (fun (_ : PUnit.{1}) => (f ⊗ₘ (g ⊗ₘ g))) (i := PUnit.unit)
      (Product.SquareTransport.testBase (f ⊗ₘ (g ⊗ₘ g))) (pullback.fst _ _) pullback.condition)
    (UnderlyingDescent.coverMap_base (fun (_ : PUnit.{1}) => (f ⊗ₘ (g ⊗ₘ g))) (i := PUnit.unit)
      (Product.SquareTransport.testBase (f ⊗ₘ (g ⊗ₘ g))) (pullback.snd _ _) rfl)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.SquareTransport
