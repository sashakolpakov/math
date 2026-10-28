import OAI.AlgebraicGeometry.Picard.PoincareBundle.EquivariantVerticalProduct
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.BiextensionLineDescent

/-! # Vertical Product -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.VerticalProduct

noncomputable section

/-!
# The genuine vertical product descends to the line constructed from isotropy
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductParameters
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.BiextensionLineDescent OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.QuotientCommutation

variable {S : Scheme.{u}} {A B X Y : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom f] [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)
  (hi : Biextension.Compatibility.Interchange L Dh Dv) (ht : Biextension.Compatibility.TransverseFrames L Dh Dv f g Kh Kv)
  (he : Biextension.Compatibility.Isotropic L Dh Dv f g Kh Kv) (hc : KernelFrame.Centrality.Central g Kv)
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  [IsAffineHom g.left] [Flat g.left] [Surjective g.left]
  [IsLocallyNoetherian (B ⊗ Y).left] [IsLocallyNoetherian (B ⊗ (Y ⊗ Y)).left]

/-- Isotropy constructs both the quotient line and its genuine descended vertical product. -/
def product :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
      ((BiextensionLineDescent.descendedLine f g L Dh Dv Kh Kv hi ht he).pullback (Vertical.ProductParameters.inputLeft B Y).left).sheaf
      ((BiextensionLineDescent.descendedLine f g L Dh Dv Kh Kv hi ht he).pullback (Vertical.ProductParameters.inputRight B Y).left).sheaf
      ((BiextensionLineDescent.descendedLine f g L Dh Dv Kh Kv hi ht he).pullback (Vertical.ProductParameters.outputPoint B Y).left).sheaf :=
  EquivariantVerticalProduct.product f g L Dh Dv Kh Kv
    (Biextension.QuotientCommutation.axisData_commutes f g L Dh Dv Kh Kv hi ht he)
    (BiextensionLineDescent.descendedLine f g L Dh Dv Kh Kv hi ht he) (BiextensionLineDescent.pullbackIso f g L Dh Dv Kh Kv hi ht he)
    (BiextensionLineDescent.pullbackIso_compatible f g L Dh Dv Kh Kv hi ht he) hi hc ht.2

/-- The product on the constructed quotient line is an actual line-bundle isomorphism. -/
theorem product_isIso : IsIso (Bilinear.BilinearPullback.toHom (product f g L Dh Dv Kh Kv hi ht he hc)) :=
  EquivariantVerticalProduct.product_isIso f g L Dh Dv Kh Kv
    (Biextension.QuotientCommutation.axisData_commutes f g L Dh Dv Kh Kv hi ht he)
    (BiextensionLineDescent.descendedLine f g L Dh Dv Kh Kv hi ht he) (BiextensionLineDescent.pullbackIso f g L Dh Dv Kh Kv hi ht he)
    (BiextensionLineDescent.pullbackIso_compatible f g L Dh Dv Kh Kv hi ht he) hi hc ht.2

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.VerticalProduct
