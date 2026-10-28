import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.RecoveryCompatibility

/-! # Equivariant Global Product -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.EquivariantGlobalProduct

noncomputable section

/-!
# Effective descent of the genuine horizontal product

All product compatibility is proved from the original multiplication, interchange, and kernel
frame laws. No equivariance or product-descent square is an input to this construction.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.ParameterSchemes
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.SquareTransport OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.RecoveryCompatibility

variable {S : Scheme.{u}} {A B X Y : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom f] [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)
  (hcomm : RectangularTransport.Commutes f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf
    (Biextension.AxisData.toAxisData f g L Dh Dv Kh Kv))
  (R : Line.Bundles.LineBundle (B ⊗ Y).left)
  (e : (Scheme.Modules.pullback (f ⊗ₘ g).left).obj R.sheaf ≅ L.sheaf)
  (he : (Scheme.Modules.pullback (pullback.fst (f ⊗ₘ g).left (f ⊗ₘ g).left)).map e.hom ≫
      (Geometric.CechInvariant.relationGluing (f ⊗ₘ g).left (UnderlyingDescent.underlyingDatum Geometric.KernelLinearization.modulePullbacks
        (fun (_ : PUnit.{1}) => f ⊗ₘ g) (Product.SquareTransport.originalDatum f g L Dh Dv Kh Kv hcomm))).hom =
    (Cech.MateNormalization.standardGluing (f ⊗ₘ g).left (pullback.fst (f ⊗ₘ g).left (f ⊗ₘ g).left)
      (pullback.snd (f ⊗ₘ g).left (f ⊗ₘ g).left) pullback.condition).hom.app R.sheaf ≫
        (Scheme.Modules.pullback (pullback.snd (f ⊗ₘ g).left (f ⊗ₘ g).left)).map e.hom)
  (hi : Biextension.Compatibility.Interchange L Dh Dv)
  (hc : KernelFrame.Centrality.Central f Kh)
  (ht : Kernel.FramesTransverseTransport.Transverse g Kv Dh)
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  [IsAffineHom g.left] [Flat g.left] [Surjective g.left] [IsLocallyNoetherian ((B ⊗ B) ⊗ Y).left]

attribute [local instance] Product.Covers.tensorAffine Product.Covers.tensorFlat Product.Covers.tensorSurjective

/-- The actual source sheaf map represented by the original product and its two input recoveries. -/
def coverMap :
    (Scheme.Modules.pullback ((f ⊗ₘ f) ⊗ₘ g).left).obj
      (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (R.pullback (Product.ParameterSchemes.inputLeft B Y).left).sheaf (R.pullback (Product.ParameterSchemes.inputRight B Y).left).sheaf) ⟶
    Line.Fibers.fiber L (Product.ParameterSchemes.outputPoint A X) :=
  (Tensor.LinePullback.pullbackIso ((f ⊗ₘ f) ⊗ₘ g).left
    (R.pullback (Product.ParameterSchemes.inputLeft B Y).left).sheaf (R.pullback (Product.ParameterSchemes.inputRight B Y).left).sheaf
    (R.pullback (Product.ParameterSchemes.inputLeft B Y).left).isLine (R.pullback (Product.ParameterSchemes.inputRight B Y).left).isLine).hom ≫
  Tensor.SheafMaps.tensorMap
    (Product.RecoveryCompatibility.squareRecovery f g L Dh Dv Kh Kv hcomm R e he _ _ (Product.ParameterSchemes.inputLeft_naturality f g)).hom
    (Product.RecoveryCompatibility.squareRecovery f g L Dh Dv Kh Kv hcomm R e he _ _ (Product.ParameterSchemes.inputRight_naturality f g)).hom ≫
  Bilinear.BilinearPullback.toHom (Product.ParameterSchemes.globalProduct A X L Dh)

/-- The actual source product descends to a bilinear map between the three pulled-back quotient lines. -/
def product : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (R.pullback (Product.ParameterSchemes.inputLeft B Y).left).sheaf
    (R.pullback (Product.ParameterSchemes.inputRight B Y).left).sheaf (R.pullback (Product.ParameterSchemes.outputPoint B Y).left).sheaf :=
  Bilinear.DescentRecovery.descendedBilinear ((f ⊗ₘ f) ⊗ₘ g).left
    (Product.RecoveryCompatibility.squareDatum f g L Dh Dv Kh Kv hcomm _ _ (Product.ParameterSchemes.outputPoint_naturality f g))
    (Line.Fibers.fiber_isLine L (Product.ParameterSchemes.outputPoint A X))
    (R.pullback (Product.ParameterSchemes.inputLeft B Y).left) (R.pullback (Product.ParameterSchemes.inputRight B Y).left) (R.pullback (Product.ParameterSchemes.outputPoint B Y).left)
    (Product.RecoveryCompatibility.squareRecovery f g L Dh Dv Kh Kv hcomm R e he _ _ (Product.ParameterSchemes.inputLeft_naturality f g))
    (Product.RecoveryCompatibility.squareRecovery f g L Dh Dv Kh Kv hcomm R e he _ _ (Product.ParameterSchemes.inputRight_naturality f g))
    (Product.ParameterSchemes.globalProduct A X L Dh) (Product.RecoveryCompatibility.horizontal_compatible f g L Dh Dv Kh Kv hcomm R e he hi hc ht)
    (Product.RecoveryCompatibility.squareRecovery f g L Dh Dv Kh Kv hcomm R e he _ _ (Product.ParameterSchemes.outputPoint_naturality f g))
    (Product.RecoveryCompatibility.squareRecovery_compatible f g L Dh Dv Kh Kv hcomm R e he _ _ (Product.ParameterSchemes.outputPoint_naturality f g))

/-- The descended genuine product is an isomorphism of line sheaves. -/
theorem product_isIso : IsIso (Bilinear.BilinearPullback.toHom (product f g L Dh Dv Kh Kv hcomm R e he hi hc ht)) :=
  Bilinear.DescentRecovery.descendedBilinear_isIso ((f ⊗ₘ f) ⊗ₘ g).left
    (Product.RecoveryCompatibility.squareDatum f g L Dh Dv Kh Kv hcomm _ _ (Product.ParameterSchemes.outputPoint_naturality f g))
    (Line.Fibers.fiber_isLine L (Product.ParameterSchemes.outputPoint A X))
    (R.pullback (Product.ParameterSchemes.inputLeft B Y).left) (R.pullback (Product.ParameterSchemes.inputRight B Y).left) (R.pullback (Product.ParameterSchemes.outputPoint B Y).left)
    (Product.RecoveryCompatibility.squareRecovery f g L Dh Dv Kh Kv hcomm R e he _ _ (Product.ParameterSchemes.inputLeft_naturality f g))
    (Product.RecoveryCompatibility.squareRecovery f g L Dh Dv Kh Kv hcomm R e he _ _ (Product.ParameterSchemes.inputRight_naturality f g))
    (Product.ParameterSchemes.globalProduct A X L Dh) (Product.RecoveryCompatibility.horizontal_compatible f g L Dh Dv Kh Kv hcomm R e he hi hc ht)
    (Product.RecoveryCompatibility.squareRecovery f g L Dh Dv Kh Kv hcomm R e he _ _ (Product.ParameterSchemes.outputPoint_naturality f g))
    (Product.RecoveryCompatibility.squareRecovery_compatible f g L Dh Dv Kh Kv hcomm R e he _ _ (Product.ParameterSchemes.outputPoint_naturality f g))
    (Product.ParameterSchemes.globalProduct_isIso A X L Dh)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.EquivariantGlobalProduct
