import OAI.AlgebraicGeometry.Picard.PoincareBundle.UnderlyingDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

/-! # Underlying Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.UnderlyingDescent

noncomputable section

/-!
# Kernel linearizations give ordinary descent data on underlying schemes
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f] (L : Line.Bundles.LineBundle A.left)
  (D : Geometric.KernelLinearization.LineLinearization f L)

/-- The actual global kernel action produces ordinary descent data on all test schemes. -/
def underlyingLineDatum : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f.left) :=
  UnderlyingDescent.underlyingDatum Geometric.KernelLinearization.modulePullbacks (fun (_ : PUnit.{1}) => f)
    (Geometric.KernelLinearization.lineDescentData f L D)

/-- The object in the underlying descent datum is the original geometric line bundle. -/
theorem underlyingLineDatum_obj : (underlyingLineDatum f L D).obj PUnit.unit = L.sheaf := rfl

/-- The underlying descent object retains its actual local line-bundle trivializations. -/
theorem underlyingLineDatum_isLine :
    Line.Bundles.IsLine ((underlyingLineDatum f L D).obj PUnit.unit) := L.isLine

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.UnderlyingDescent
