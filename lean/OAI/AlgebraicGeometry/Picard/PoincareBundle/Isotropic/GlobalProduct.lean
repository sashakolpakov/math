import OAI.AlgebraicGeometry.Picard.PoincareBundle.EquivariantGlobalProduct
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.BiextensionLineDescent

/-! # Global Product -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.GlobalProduct

noncomputable section

/-!
# The genuine horizontal product descends to the line constructed from isotropy
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.ParameterSchemes
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.BiextensionLineDescent OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.QuotientCommutation

variable {S : Scheme.{u}} {A B X Y : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom f] [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)
  (hi : Biextension.Compatibility.Interchange L Dh Dv) (ht : Biextension.Compatibility.TransverseFrames L Dh Dv f g Kh Kv)
  (he : Biextension.Compatibility.Isotropic L Dh Dv f g Kh Kv) (hc : KernelFrame.Centrality.Central f Kh)
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  [IsAffineHom g.left] [Flat g.left] [Surjective g.left]
  [IsLocallyNoetherian (B ⊗ Y).left] [IsLocallyNoetherian ((B ⊗ B) ⊗ Y).left]

/-- Isotropy constructs both the quotient line and its genuine descended horizontal product. -/
def product :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
      ((BiextensionLineDescent.descendedLine f g L Dh Dv Kh Kv hi ht he).pullback (Product.ParameterSchemes.inputLeft B Y).left).sheaf
      ((BiextensionLineDescent.descendedLine f g L Dh Dv Kh Kv hi ht he).pullback (Product.ParameterSchemes.inputRight B Y).left).sheaf
      ((BiextensionLineDescent.descendedLine f g L Dh Dv Kh Kv hi ht he).pullback (Product.ParameterSchemes.outputPoint B Y).left).sheaf :=
  EquivariantGlobalProduct.product f g L Dh Dv Kh Kv
    (Biextension.QuotientCommutation.axisData_commutes f g L Dh Dv Kh Kv hi ht he)
    (BiextensionLineDescent.descendedLine f g L Dh Dv Kh Kv hi ht he) (BiextensionLineDescent.pullbackIso f g L Dh Dv Kh Kv hi ht he)
    (BiextensionLineDescent.pullbackIso_compatible f g L Dh Dv Kh Kv hi ht he) hi hc ht.1

/-- The product on the constructed quotient line is an actual line-bundle isomorphism. -/
theorem product_isIso : IsIso (Bilinear.BilinearPullback.toHom (product f g L Dh Dv Kh Kv hi ht he hc)) :=
  EquivariantGlobalProduct.product_isIso f g L Dh Dv Kh Kv
    (Biextension.QuotientCommutation.axisData_commutes f g L Dh Dv Kh Kv hi ht he)
    (BiextensionLineDescent.descendedLine f g L Dh Dv Kh Kv hi ht he) (BiextensionLineDescent.pullbackIso f g L Dh Dv Kh Kv hi ht he)
    (BiextensionLineDescent.pullbackIso_compatible f g L Dh Dv Kh Kv hi ht he) hi hc ht.1

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.GlobalProduct
