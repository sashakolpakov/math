import OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.UnitDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.BiextensionLineDescent

/-! # Unit Frame -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.UnitFrame

noncomputable section

/-!
# Constructing the unit frame on the quotient line obtained from isotropy
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.ParameterScheme
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.BiextensionLineDescent OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.QuotientCommutation

variable {S : Scheme.{u}} {A B X Y : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom f] [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)
  (hi : Biextension.Compatibility.Interchange L Dh Dv) (ht : Biextension.Compatibility.TransverseFrames L Dh Dv f g Kh Kv)
  (he : Biextension.Compatibility.Isotropic L Dh Dv f g Kh Kv)
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  [IsAffineHom g.left] [Flat g.left] [Surjective g.left]
  [IsLocallyNoetherian (B ⊗ Y).left] [IsLocallyNoetherian Y.left]

/-- Isotropy constructs both the actual quotient line and its normalized neutral-axis unit frame. -/
def unitFrame : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y.left ≅
    ((BiextensionLineDescent.descendedLine f g L Dh Dv Kh Kv hi ht he).pullback (Neutral.ParameterScheme.point B Y).left).sheaf :=
  Neutral.UnitDescent.unitFrame f g L Dh Dv Kh Kv
    (Biextension.QuotientCommutation.axisData_commutes f g L Dh Dv Kh Kv hi ht he)
    (BiextensionLineDescent.descendedLine f g L Dh Dv Kh Kv hi ht he) (BiextensionLineDescent.pullbackIso f g L Dh Dv Kh Kv hi ht he)
    (BiextensionLineDescent.pullbackIso_compatible f g L Dh Dv Kh Kv hi ht he) hi ht.1

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.UnitFrame
