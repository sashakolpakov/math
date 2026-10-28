import OAI.AlgebraicGeometry.Picard.PoincareBundle.SecondNeutralUnitDescent

/-! # Second Unit Recovery -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SecondUnitRecovery

noncomputable section

/-!
# Exact recovery of the constructed second-coordinate quotient unit
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.SecondNeutralParameterScheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.SquareTransport
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
        (fun (_ : PUnit.{1}) => f ⊗ₘ g) (Product.SquareTransport.originalDatum f g L Dh Dv Kh Kv hcomm))).hom =
    (Cech.MateNormalization.standardGluing (f ⊗ₘ g).left (pullback.fst (f ⊗ₘ g).left (f ⊗ₘ g).left)
      (pullback.snd (f ⊗ₘ g).left (f ⊗ₘ g).left) pullback.condition).hom.app R.sheaf ≫
        (Scheme.Modules.pullback (pullback.snd (f ⊗ₘ g).left (f ⊗ₘ g).left)).map e.hom)

variable (hi : Biextension.Compatibility.Interchange L Dh Dv)
  (ht : Kernel.FramesTransverseTransport.Transverse f Kh Dv)
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [IsLocallyNoetherian B.left]

/-- Pullback of the actual descended unit has exactly the original source unit and recovery map. -/
theorem unitFrame_fac :
    (Scheme.Modules.pullback f.left).map
        (SecondNeutralUnitDescent.unitFrame f g L Dh Dv Kh Kv hcomm R e he hi ht).hom ≫
      (SecondNeutralUnitDescent.recovery f g L Dh Dv Kh Kv hcomm R e he).hom =
        SecondNeutralUnitCompatibility.coverUnit f L Dv :=
  Recovered.MorphismDescent.descendedHom_fac f.left
    (SecondNeutralUnitCompatibility.ordinaryDatum f g L Dh Dv Kh Kv hcomm)
    (Line.Fibers.fiber_isLine L (SecondNeutralParameterScheme.point A X)) (R.pullback (SecondNeutralParameterScheme.point B Y).left)
    (SecondNeutralUnitDescent.recovery f g L Dh Dv Kh Kv hcomm R e he)
    (SecondNeutralUnitDescent.recovery_compatible f g L Dh Dv Kh Kv hcomm R e he)
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.left) (SecondNeutralUnitCompatibility.coverUnit f L Dv)
    (SecondNeutralUnitCompatibility.coverUnit_compatible f g L Dh Dv Kh Kv hcomm hi ht)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SecondUnitRecovery
