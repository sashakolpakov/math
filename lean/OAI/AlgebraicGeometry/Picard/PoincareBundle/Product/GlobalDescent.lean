import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.RecoverySquares
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.OrdinaryDatum
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.DescentRecovery

/-! # Global Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.GlobalDescent

noncomputable section

/-!
# Effective descent of the global product on its actual triple parameter scheme

The ordinary datum and all three line recoveries are constructed. The remaining input to this
geometric step is the explicit bilinear gluing equation, to be supplied by kernel equivariance.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.ParameterSchemes OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.RecoverySquares OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

variable {S : Scheme.{u}} {A B X Y : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom f]
  (L : Line.Bundles.LineBundle (A ⊗ X).left) (R : Line.Bundles.LineBundle (B ⊗ Y).left)
  (e : (Scheme.Modules.pullback (f ⊗ₘ g).left).obj R.sheaf ≅ L.sheaf)
  (D : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L)

/-- The actual output recovery constructs the ordinary datum on the product parameter cover. -/
def outputDatum : Geometric.KernelLinearization.modulePullbacks.DescentData
    (fun (_ : PUnit.{1}) => ((f ⊗ₘ f) ⊗ₘ g).left) :=
  Recovered.OrdinaryDatum.Ordinary.ofRecovery ((f ⊗ₘ f) ⊗ₘ g).left (R.pullback (ParameterSchemes.outputPoint B Y).left).sheaf
    (Line.Fibers.fiber L (ParameterSchemes.outputPoint A X)) (RecoverySquares.outputIso f g L R e)

/-- The exact ordinary geometric gluing equation for the given genuine global product. -/
def Compatible : Prop := Bilinear.GlobalDescent.Compatible ((f ⊗ₘ f) ⊗ₘ g).left
  (outputDatum f g L R e) (R.pullback (ParameterSchemes.inputLeft B Y).left) (R.pullback (ParameterSchemes.inputRight B Y).left)
  (RecoverySquares.inputLeftIso f g L R e) (RecoverySquares.inputRightIso f g L R e) (ParameterSchemes.globalProduct A X L D)

variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  [IsAffineHom g.left] [Flat g.left] [Surjective g.left] [IsLocallyNoetherian ((B ⊗ B) ⊗ Y).left]
  (hc : Compatible f g L R e D)

attribute [local instance] Covers.tensorAffine Covers.tensorFlat Covers.tensorSurjective

/-- The genuine source product descends to an actual bilinear map of the three quotient line bundles. -/
def product : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (R.pullback (ParameterSchemes.inputLeft B Y).left).sheaf
    (R.pullback (ParameterSchemes.inputRight B Y).left).sheaf (R.pullback (ParameterSchemes.outputPoint B Y).left).sheaf :=
  Bilinear.DescentRecovery.descendedBilinear ((f ⊗ₘ f) ⊗ₘ g).left (outputDatum f g L R e)
    (Line.Fibers.fiber_isLine L (ParameterSchemes.outputPoint A X))
    (R.pullback (ParameterSchemes.inputLeft B Y).left) (R.pullback (ParameterSchemes.inputRight B Y).left) (R.pullback (ParameterSchemes.outputPoint B Y).left)
    (RecoverySquares.inputLeftIso f g L R e) (RecoverySquares.inputRightIso f g L R e) (ParameterSchemes.globalProduct A X L D) hc (RecoverySquares.outputIso f g L R e)
    (Recovered.OrdinaryDatum.Ordinary.recovery_compatible _ _ _ _)

/-- The descended product is an actual bilinear isomorphism. -/
theorem product_isIso : IsIso (Bilinear.BilinearPullback.toHom (product f g L R e D hc)) :=
  Bilinear.DescentRecovery.descendedBilinear_isIso ((f ⊗ₘ f) ⊗ₘ g).left (outputDatum f g L R e)
    (Line.Fibers.fiber_isLine L (ParameterSchemes.outputPoint A X))
    (R.pullback (ParameterSchemes.inputLeft B Y).left) (R.pullback (ParameterSchemes.inputRight B Y).left) (R.pullback (ParameterSchemes.outputPoint B Y).left)
    (RecoverySquares.inputLeftIso f g L R e) (RecoverySquares.inputRightIso f g L R e) (ParameterSchemes.globalProduct A X L D) hc (RecoverySquares.outputIso f g L R e)
    (Recovered.OrdinaryDatum.Ordinary.recovery_compatible _ _ _ _) (ParameterSchemes.globalProduct_isIso A X L D)

/-- Pullback of the actual quotient product recovers the original global product through the three canonical recovery squares. -/
theorem product_fac :
    (Scheme.Modules.pullback ((f ⊗ₘ f) ⊗ₘ g).left).map (Bilinear.BilinearPullback.toHom (product f g L R e D hc)) ≫
      (RecoverySquares.outputIso f g L R e).hom =
    Bilinear.GlobalDescent.coverMap ((f ⊗ₘ f) ⊗ₘ g).left (outputDatum f g L R e)
      (R.pullback (ParameterSchemes.inputLeft B Y).left) (R.pullback (ParameterSchemes.inputRight B Y).left)
      (RecoverySquares.inputLeftIso f g L R e) (RecoverySquares.inputRightIso f g L R e) (ParameterSchemes.globalProduct A X L D) :=
  Bilinear.DescentRecovery.descendedBilinear_fac ((f ⊗ₘ f) ⊗ₘ g).left (outputDatum f g L R e)
    (Line.Fibers.fiber_isLine L (ParameterSchemes.outputPoint A X))
    (R.pullback (ParameterSchemes.inputLeft B Y).left) (R.pullback (ParameterSchemes.inputRight B Y).left) (R.pullback (ParameterSchemes.outputPoint B Y).left)
    (RecoverySquares.inputLeftIso f g L R e) (RecoverySquares.inputRightIso f g L R e) (ParameterSchemes.globalProduct A X L D) hc (RecoverySquares.outputIso f g L R e)
    (Recovered.OrdinaryDatum.Ordinary.recovery_compatible _ _ _ _)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.GlobalDescent
