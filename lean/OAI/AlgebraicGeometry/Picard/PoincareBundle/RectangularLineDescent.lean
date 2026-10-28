import OAI.AlgebraicGeometry.Picard.PoincareBundle.RectangularTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.UnderlyingDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.GlobalLineDescent

/-! # Rectangular Line Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.RectangularLineDescent

noncomputable section

/-!
# Effective line-bundle descent under two commuting coordinate actions
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.RectangularTransport

variable {S : Scheme.{u}} {A B X Y : Over S} (f : A ⟶ B) (g : X ⟶ Y)
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (D : RectangularTransport.AxisData f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf)
  (hc : RectangularTransport.Commutes f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf D)

/-- The constructed product cocycle is ordinary geometric descent data on all underlying schemes. -/
def ordinaryDatum : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => (f ⊗ₘ g).left) :=
  UnderlyingDescent.underlyingDatum Geometric.KernelLinearization.modulePullbacks (fun (_ : PUnit.{1}) => f ⊗ₘ g)
    (RectangularTransport.toDescentData f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf D hc)

variable [IsAffineHom (f ⊗ₘ g).left] [Flat (f ⊗ₘ g).left] [Surjective (f ⊗ₘ g).left]
  [IsLocallyNoetherian (B ⊗ Y).left]

/-- The actual invariant sheaf for the two coordinate actions is a line on the quotient product. -/
def descendedLine : Line.Bundles.LineBundle (B ⊗ Y).left :=
  Ordinary.GlobalLineDescent.descendedLine (f ⊗ₘ g).left (ordinaryDatum f g L D hc) L.isLine

/-- The canonical quotient pullback recovers the original line sheaf. -/
def pullbackIso :
    (Scheme.Modules.pullback (f ⊗ₘ g).left).obj (descendedLine f g L D hc).sheaf ≅ L.sheaf :=
  Ordinary.GlobalLineDescent.descendedLinePullbackIso (f ⊗ₘ g).left
    (ordinaryDatum f g L D hc) L.isLine

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.RectangularLineDescent
