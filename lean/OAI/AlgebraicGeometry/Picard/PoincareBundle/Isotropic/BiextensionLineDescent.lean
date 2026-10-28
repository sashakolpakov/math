import OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.QuotientCommutation
import OAI.AlgebraicGeometry.Picard.PoincareBundle.RectangularLineDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Covers
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.LineDescentUniqueness

/-! # Biextension Line Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.BiextensionLineDescent

noncomputable section

/-!
# Constructing a quotient line bundle from isotropic biextension kernel frames

The inputs are actual fiberwise products, normalized multiplicative kernel frames, the standard
biextension interchange law, and triviality of their actual unit-valued kernel obstruction.
The commuting actions, full cocycle, invariant line sheaf, and quotient pullback isomorphism are
all constructed. The canonical Poincare origin of the kernel frames is a separate remaining step.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.AxisData OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.QuotientCommutation OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {S : Scheme.{u}} {A B X Y : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom f] [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)
  (hi : Biextension.Compatibility.Interchange L Dh Dv) (ht : Biextension.Compatibility.TransverseFrames L Dh Dv f g Kh Kv)
  (he : Biextension.Compatibility.Isotropic L Dh Dv f g Kh Kv)

/-- Isotropy constructs a genuine ordinary descent datum on the actual quotient product cover. -/
def ordinaryDatum : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => (f ⊗ₘ g).left) :=
  RectangularLineDescent.ordinaryDatum f g L (Biextension.AxisData.toAxisData f g L Dh Dv Kh Kv)
    (Biextension.QuotientCommutation.axisData_commutes f g L Dh Dv Kh Kv hi ht he)

variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  [IsAffineHom g.left] [Flat g.left] [Surjective g.left] [IsLocallyNoetherian (B ⊗ Y).left]

attribute [local instance] Product.Covers.tensorAffine Product.Covers.tensorFlat
  Product.Covers.tensorSurjective

/-- The descended bundle is the actual invariant sheaf of the actions derived from the isotropic frames. -/
def descendedLine : Line.Bundles.LineBundle (B ⊗ Y).left :=
  Ordinary.GlobalLineDescent.descendedLine (f ⊗ₘ g).left
    (ordinaryDatum f g L Dh Dv Kh Kv hi ht he) L.isLine

/-- Pullback of the constructed line bundle canonically recovers the original biextension line sheaf. -/
def pullbackIso :
    (Scheme.Modules.pullback (f ⊗ₘ g).left).obj (descendedLine f g L Dh Dv Kh Kv hi ht he).sheaf ≅ L.sheaf :=
  Ordinary.GlobalLineDescent.descendedLinePullbackIso (f ⊗ₘ g).left
    (ordinaryDatum f g L Dh Dv Kh Kv hi ht he) L.isLine

/-- The canonical recovery respects the original full geometric gluing on the scheme kernel pair. -/
theorem pullbackIso_compatible :
    (Scheme.Modules.pullback (pullback.fst (f ⊗ₘ g).left (f ⊗ₘ g).left)).map
        (pullbackIso f g L Dh Dv Kh Kv hi ht he).hom ≫
      (Geometric.CechInvariant.relationGluing (f ⊗ₘ g).left
        (ordinaryDatum f g L Dh Dv Kh Kv hi ht he)).hom =
    (Cech.MateNormalization.standardGluing (f ⊗ₘ g).left
      (pullback.fst (f ⊗ₘ g).left (f ⊗ₘ g).left) (pullback.snd (f ⊗ₘ g).left (f ⊗ₘ g).left)
      pullback.condition).hom.app (descendedLine f g L Dh Dv Kh Kv hi ht he).sheaf ≫
      (Scheme.Modules.pullback (pullback.snd (f ⊗ₘ g).left (f ⊗ₘ g).left)).map
        (pullbackIso f g L Dh Dv Kh Kv hi ht he).hom :=
  Ordinary.GlobalLineDescent.descendedLinePullbackIso_compatible (f ⊗ₘ g).left
    (ordinaryDatum f g L Dh Dv Kh Kv hi ht he) L.isLine

/-- Every other line recovery with the constructed gluing is uniquely isomorphic to this invariant line. -/
theorem existsUnique_iso (N : Line.Bundles.LineBundle (B ⊗ Y).left)
    (e : (Scheme.Modules.pullback (f ⊗ₘ g).left).obj N.sheaf ≅ L.sheaf)
    (heq : (Scheme.Modules.pullback (pullback.fst (f ⊗ₘ g).left (f ⊗ₘ g).left)).map e.hom ≫
      (Geometric.CechInvariant.relationGluing (f ⊗ₘ g).left
        (ordinaryDatum f g L Dh Dv Kh Kv hi ht he)).hom =
      (Cech.MateNormalization.standardGluing (f ⊗ₘ g).left
        (pullback.fst (f ⊗ₘ g).left (f ⊗ₘ g).left) (pullback.snd (f ⊗ₘ g).left (f ⊗ₘ g).left)
        pullback.condition).hom.app N.sheaf ≫
        (Scheme.Modules.pullback (pullback.snd (f ⊗ₘ g).left (f ⊗ₘ g).left)).map e.hom) :
    ∃! a : N.sheaf ≅ (descendedLine f g L Dh Dv Kh Kv hi ht he).sheaf,
      (Scheme.Modules.pullback (f ⊗ₘ g).left).map a.hom ≫
        (pullbackIso f g L Dh Dv Kh Kv hi ht he).hom = e.hom :=
  Ordinary.LineDescentUniqueness.existsUnique_iso (f ⊗ₘ g).left
    (ordinaryDatum f g L Dh Dv Kh Kv hi ht he) L.isLine N e heq

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.BiextensionLineDescent
