import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.RecoveryCompatibility
import OAI.AlgebraicGeometry.Picard.PoincareBundle.SquareRecoveryFormula

/-! # Square Recovery Formula -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.SquareRecoveryFormula

noncomputable section

/-!
# Explicit geometric formulas for the three compatible product-square recoveries
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.ParameterSchemes OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.SquareTransport
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization

variable {S : Scheme.{u}} {A B X Y : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom f] [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)
  (hcomm : RectangularTransport.Commutes f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf
    (Biextension.AxisData.toAxisData f g L Dh Dv Kh Kv))

variable (R : Line.Bundles.LineBundle (B ⊗ Y).left)
  (e : (Scheme.Modules.pullback (f ⊗ₘ g).left).obj R.sheaf ≅ L.sheaf)
  (he : (Scheme.Modules.pullback (pullback.fst (f ⊗ₘ g).left (f ⊗ₘ g).left)).map e.hom ≫
      (Geometric.CechInvariant.relationGluing (f ⊗ₘ g).left (UnderlyingDescent.underlyingDatum Geometric.KernelLinearization.modulePullbacks
        (fun (_ : PUnit.{1}) => f ⊗ₘ g) (SquareTransport.originalDatum f g L Dh Dv Kh Kv hcomm))).hom =
    (Cech.MateNormalization.standardGluing (f ⊗ₘ g).left (pullback.fst (f ⊗ₘ g).left (f ⊗ₘ g).left)
      (pullback.snd (f ⊗ₘ g).left (f ⊗ₘ g).left) pullback.condition).hom.app R.sheaf ≫
        (Scheme.Modules.pullback (pullback.snd (f ⊗ₘ g).left (f ⊗ₘ g).left)).map e.hom)

/-- The constructed compatible product-square recovery is precisely the explicit geometric recovery path. -/
theorem squareRecovery_eq (i : (A ⊗ A) ⊗ X ⟶ A ⊗ X) (j : (B ⊗ B) ⊗ Y ⟶ B ⊗ Y)
    (hij : ((f ⊗ₘ f) ⊗ₘ g) ≫ j = i ≫ (f ⊗ₘ g)) :
    RecoveryCompatibility.squareRecovery f g L Dh Dv Kh Kv hcomm R e he i j hij =
    RecoverySquares.recoveryIso (f ⊗ₘ g).left ((f ⊗ₘ f) ⊗ₘ g).left i.left j.left
      (congrArg Over.Hom.left hij) L R e :=
  (Geometric.SquareComponents.recovery_eq (f ⊗ₘ g) ((f ⊗ₘ f) ⊗ₘ g) i j hij.symm R.sheaf
    (SquareTransport.originalDatum f g L Dh Dv Kh Kv hcomm) e he).trans
    (SquareRecoveryFormula.composition_path (f ⊗ₘ g) ((f ⊗ₘ f) ⊗ₘ g) i j hij L R e)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.SquareRecoveryFormula
