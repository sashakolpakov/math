import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.UnderlyingDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.GlobalLineDescent

/-! # Global Line Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.GlobalLineDescent

noncomputable section

/-!
# Global effective descent of an actual scheme-kernel linearization
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.UnderlyingDescent

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f] [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  [IsLocallyNoetherian B.left] (L : Line.Bundles.LineBundle A.left) (D : Geometric.KernelLinearization.LineLinearization f L)

/-- The geometric kernel action descends the line bundle to the quotient scheme. -/
def descendedLine : Line.Bundles.LineBundle B.left :=
  Ordinary.GlobalLineDescent.descendedLine f.left (UnderlyingDescent.underlyingLineDatum f L D)
    (UnderlyingDescent.underlyingLineDatum_isLine f L D)

/-- The actual quotient pullback recovers the original line bundle with its kernel descent datum. -/
def pullbackIso : (Scheme.Modules.pullback f.left).obj (descendedLine f L D).sheaf ≅ L.sheaf :=
  Ordinary.GlobalLineDescent.descendedLinePullbackIso f.left (UnderlyingDescent.underlyingLineDatum f L D)
    (UnderlyingDescent.underlyingLineDatum_isLine f L D)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.GlobalLineDescent
