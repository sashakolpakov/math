import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeKernelAction
import OAI.AlgebraicGeometry.Picard.PoincareBundle.UnderlyingDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.GlobalLineDescent

/-! # Split Multiplicative Line Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SplitMultiplicativeLineDescent

noncomputable section

/-!
# Effective descent from a multiplicative trivialization on the scheme-theoretic kernel
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeLineData OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeKernelAction

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f] (L : Line.Bundles.LineBundle A.left)
  (D : MultiplicativeLineData.MultiplicativeData L) (K : MultiplicativeLineData.KernelSplitting L f D)

/-- The derived kernel action supplies genuine ordinary descent data on all underlying test schemes. -/
def ordinaryDatum : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f.left) :=
  UnderlyingDescent.underlyingDatum Geometric.KernelLinearization.modulePullbacks (fun (_ : PUnit.{1}) => f)
    (MultiplicativeKernelAction.toKernelLinearization f L D K).toDescentData

variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [IsLocallyNoetherian B.left]

/-- The line bundle with multiplicatively trivial kernel restriction descends to the quotient scheme. -/
def descendedLine : Line.Bundles.LineBundle B.left :=
  Ordinary.GlobalLineDescent.descendedLine f.left (ordinaryDatum f L D K) L.isLine

/-- The actual canonical quotient pullback recovers the original multiplicative line bundle. -/
def pullbackIso : (Scheme.Modules.pullback f.left).obj (descendedLine f L D K).sheaf ≅ L.sheaf :=
  Ordinary.GlobalLineDescent.descendedLinePullbackIso f.left (ordinaryDatum f L D K) L.isLine

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SplitMultiplicativeLineDescent
