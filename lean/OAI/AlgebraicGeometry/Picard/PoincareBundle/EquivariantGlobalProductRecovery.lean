import OAI.AlgebraicGeometry.Picard.PoincareBundle.EquivariantGlobalProduct
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.ProductObject

/-! # Equivariant Global Product Recovery -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.EquivariantGlobalProductRecovery

noncomputable section

/-!
# Recovery and uniqueness of the genuine descended global product
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

omit [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
    [IsAffineHom g.left] [Flat g.left] [Surjective g.left] [IsLocallyNoetherian ((B ⊗ B) ⊗ Y).left] in
/-- The represented descent map is the explicitly typed original product recovery map. -/
theorem coverMap_native :
    Bilinear.GlobalDescent.coverMap ((f ⊗ₘ f) ⊗ₘ g).left
      (Product.RecoveryCompatibility.squareDatum f g L Dh Dv Kh Kv hcomm _ _ (Product.ParameterSchemes.outputPoint_naturality f g))
      (R.pullback (Product.ParameterSchemes.inputLeft B Y).left) (R.pullback (Product.ParameterSchemes.inputRight B Y).left)
      (Product.RecoveryCompatibility.squareRecovery f g L Dh Dv Kh Kv hcomm R e he _ _ (Product.ParameterSchemes.inputLeft_naturality f g))
      (Product.RecoveryCompatibility.squareRecovery f g L Dh Dv Kh Kv hcomm R e he _ _ (Product.ParameterSchemes.inputRight_naturality f g)) (Product.ParameterSchemes.globalProduct A X L Dh) =
    EquivariantGlobalProduct.coverMap f g L Dh Dv Kh Kv hcomm R e he := rfl

/-- The actual constructed quotient product, together with its proven recovery equation and uniqueness. -/
def recoveredProduct :=
  Recovered.ProductObject.recoveredProduct ((f ⊗ₘ f) ⊗ₘ g).left
      (Product.RecoveryCompatibility.squareDatum f g L Dh Dv Kh Kv hcomm _ _ (Product.ParameterSchemes.outputPoint_naturality f g))
      (Line.Fibers.fiber_isLine L (Product.ParameterSchemes.outputPoint A X))
      (R.pullback (Product.ParameterSchemes.inputLeft B Y).left) (R.pullback (Product.ParameterSchemes.inputRight B Y).left) (R.pullback (Product.ParameterSchemes.outputPoint B Y).left)
      (Product.RecoveryCompatibility.squareRecovery f g L Dh Dv Kh Kv hcomm R e he _ _ (Product.ParameterSchemes.inputLeft_naturality f g))
      (Product.RecoveryCompatibility.squareRecovery f g L Dh Dv Kh Kv hcomm R e he _ _ (Product.ParameterSchemes.inputRight_naturality f g))
      (Product.ParameterSchemes.globalProduct A X L Dh) (Product.RecoveryCompatibility.horizontal_compatible f g L Dh Dv Kh Kv hcomm R e he hi hc ht)
      (Product.RecoveryCompatibility.squareRecovery f g L Dh Dv Kh Kv hcomm R e he _ _ (Product.ParameterSchemes.outputPoint_naturality f g))
      (Product.RecoveryCompatibility.squareRecovery_compatible f g L Dh Dv Kh Kv hcomm R e he _ _ (Product.ParameterSchemes.outputPoint_naturality f g))

/-- Retaining the proofs leaves the constructed actual quotient product exactly unchanged. -/
theorem recoveredProduct_val : (recoveredProduct f g L Dh Dv Kh Kv hcomm R e he hi hc ht).val =
    EquivariantGlobalProduct.product f g L Dh Dv Kh Kv hcomm R e he hi hc ht := rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.EquivariantGlobalProductRecovery
