import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.UnderlyingDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.GlobalLineDescent

/-! # Transport Line Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.TransportLineDescent

noncomputable section

/-! Effective line descent directly from natural kernel transport on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f] (L : Line.Bundles.LineBundle A.left)
  (D : Linearization.KernelLinearization f (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf)

/-- The actual kernel transport gives ordinary geometric descent data on underlying schemes. -/
def datum : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f.left) :=
  UnderlyingDescent.underlyingDatum Geometric.KernelLinearization.modulePullbacks (fun (_ : PUnit.{1}) => f) D.toDescentData

theorem datum_isLine : Line.Bundles.IsLine ((datum f L D).obj PUnit.unit) := L.isLine

variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [IsLocallyNoetherian B.left]

/-- The descended object is an actual line bundle, constructed as the invariant sheaf. -/
def descendedLine : Line.Bundles.LineBundle B.left :=
  Ordinary.GlobalLineDescent.descendedLine f.left (datum f L D) (datum_isLine f L D)

/-- The quotient pullback recovers the original line bundle. -/
def pullbackIso : (Scheme.Modules.pullback f.left).obj (descendedLine f L D).sheaf ≅ L.sheaf :=
  Ordinary.GlobalLineDescent.descendedLinePullbackIso f.left (datum f L D) (datum_isLine f L D)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.TransportLineDescent
