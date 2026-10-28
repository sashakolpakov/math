import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.ParameterSchemes
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles

/-! # Recovery Squares -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.RecoverySquares

noncomputable section

/-!
# The three actual line recoveries on the product parameter scheme
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

/-- A commuting square transports a specified actual line recovery to its base change. -/
def recoveryIso {X Y T U : Scheme.{u}} (f : X ⟶ Y) (q : T ⟶ U) (a : T ⟶ X) (b : U ⟶ Y)
    (h : q ≫ b = a ≫ f) (L : Line.Bundles.LineBundle X) (R : Line.Bundles.LineBundle Y)
    (e : (Scheme.Modules.pullback f).obj R.sheaf ≅ L.sheaf) :
    (Scheme.Modules.pullback q).obj (R.pullback b).sheaf ≅ (L.pullback a).sheaf :=
  (Scheme.Modules.pullbackComp q b).app R.sheaf ≪≫
    (Scheme.Modules.pullbackCongr h).app R.sheaf ≪≫
    (Scheme.Modules.pullbackComp a f).symm.app R.sheaf ≪≫
    (Scheme.Modules.pullback a).mapIso e

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.ParameterSchemes OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

variable {S : Scheme.{u}} {A B X Y : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom f]
  (L : Line.Bundles.LineBundle (A ⊗ X).left) (R : Line.Bundles.LineBundle (B ⊗ Y).left)
  (e : (Scheme.Modules.pullback (f ⊗ₘ g).left).obj R.sheaf ≅ L.sheaf)

/-- The canonical recovery for the first line input on the actual triple quotient cover. -/
def inputLeftIso :
    (Scheme.Modules.pullback ((f ⊗ₘ f) ⊗ₘ g).left).obj (R.pullback (ParameterSchemes.inputLeft B Y).left).sheaf ≅
      Line.Fibers.fiber L (ParameterSchemes.inputLeft A X) :=
  recoveryIso (f ⊗ₘ g).left ((f ⊗ₘ f) ⊗ₘ g).left (ParameterSchemes.inputLeft A X).left (ParameterSchemes.inputLeft B Y).left
    (congrArg Over.Hom.left (ParameterSchemes.inputLeft_naturality f g)) L R e

/-- The canonical recovery for the second line input on the actual triple quotient cover. -/
def inputRightIso :
    (Scheme.Modules.pullback ((f ⊗ₘ f) ⊗ₘ g).left).obj (R.pullback (ParameterSchemes.inputRight B Y).left).sheaf ≅
      Line.Fibers.fiber L (ParameterSchemes.inputRight A X) :=
  recoveryIso (f ⊗ₘ g).left ((f ⊗ₘ f) ⊗ₘ g).left (ParameterSchemes.inputRight A X).left (ParameterSchemes.inputRight B Y).left
    (congrArg Over.Hom.left (ParameterSchemes.inputRight_naturality f g)) L R e

/-- The group-homomorphism property gives the actual recovery of the product output line. -/
def outputIso :
    (Scheme.Modules.pullback ((f ⊗ₘ f) ⊗ₘ g).left).obj (R.pullback (ParameterSchemes.outputPoint B Y).left).sheaf ≅
      Line.Fibers.fiber L (ParameterSchemes.outputPoint A X) :=
  recoveryIso (f ⊗ₘ g).left ((f ⊗ₘ f) ⊗ₘ g).left (ParameterSchemes.outputPoint A X).left (ParameterSchemes.outputPoint B Y).left
    (congrArg Over.Hom.left (ParameterSchemes.outputPoint_naturality f g)) L R e

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.RecoverySquares
