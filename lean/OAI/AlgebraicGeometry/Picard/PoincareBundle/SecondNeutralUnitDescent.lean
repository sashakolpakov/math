import OAI.AlgebraicGeometry.Picard.PoincareBundle.SecondNeutralUnitCompatibility
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.MorphismDescent

/-! # Second Neutral Unit Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SecondNeutralUnitDescent

noncomputable section

/-!
# Constructing the actual normalized quotient unit by geometric descent
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

/-- The original compatible quotient line supplies its actual recovery on the neutral-axis square. -/
def recovery : (Scheme.Modules.pullback f.left).obj (R.pullback (SecondNeutralParameterScheme.point B Y).left).sheaf ≅ Line.Fibers.fiber L (SecondNeutralParameterScheme.point A X) :=
  Recovered.OverSquare.recovery (f ⊗ₘ g) f (SecondNeutralParameterScheme.point A X) (SecondNeutralParameterScheme.point B Y) (SecondNeutralParameterScheme.point_naturality f g).symm
    (Product.SquareTransport.originalDatum f g L Dh Dv Kh Kv hcomm) R.sheaf e he

/-- The constructed neutral-axis recovery has its exact full geometric gluing compatibility. -/
theorem recovery_compatible :
    (Scheme.Modules.pullback (pullback.fst f.left f.left)).map (recovery f g L Dh Dv Kh Kv hcomm R e he).hom ≫
      (Geometric.CechInvariant.relationGluing f.left (SecondNeutralUnitCompatibility.ordinaryDatum f g L Dh Dv Kh Kv hcomm)).hom =
    (Cech.MateNormalization.standardGluing f.left (pullback.fst f.left f.left) (pullback.snd f.left f.left) pullback.condition).hom.app
      (R.pullback (SecondNeutralParameterScheme.point B Y).left).sheaf ≫
        (Scheme.Modules.pullback (pullback.snd f.left f.left)).map (recovery f g L Dh Dv Kh Kv hcomm R e he).hom :=
  Recovered.OverSquare.recovery_compatible (f ⊗ₘ g) f (SecondNeutralParameterScheme.point A X) (SecondNeutralParameterScheme.point B Y) (SecondNeutralParameterScheme.point_naturality f g).symm
    (Product.SquareTransport.originalDatum f g L Dh Dv Kh Kv hcomm) R.sheaf e he

variable (hi : Biextension.Compatibility.Interchange L Dh Dv)
  (ht : Kernel.FramesTransverseTransport.Transverse f Kh Dv)
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [IsLocallyNoetherian B.left]

/-- The genuine source neutral unit descends to an actual unit-frame isomorphism on the quotient line. -/
def unitFrame : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.left ≅ (R.pullback (SecondNeutralParameterScheme.point B Y).left).sheaf :=
  Recovered.MorphismDescent.descendedIso f.left
    (SecondNeutralUnitCompatibility.ordinaryDatum f g L Dh Dv Kh Kv hcomm) (Line.Fibers.fiber_isLine L (SecondNeutralParameterScheme.point A X))
    (R.pullback (SecondNeutralParameterScheme.point B Y).left) (recovery f g L Dh Dv Kh Kv hcomm R e he)
    (recovery_compatible f g L Dh Dv Kh Kv hcomm R e he)
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.left) (SecondNeutralUnitCompatibility.coverUnit f L Dv)
    (SecondNeutralUnitCompatibility.coverUnit_compatible f g L Dh Dv Kh Kv hcomm hi ht)
    (Line.Bundles.isLine_unit B.left)
    ((AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f.left ≪≫ SecondNeutralParameterScheme.unitFrame A X L Dv).isIso_hom)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SecondNeutralUnitDescent
