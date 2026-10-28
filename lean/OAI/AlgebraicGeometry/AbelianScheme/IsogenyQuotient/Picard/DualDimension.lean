import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Dimension
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualData

/-! # Dual Dimension -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.DualDimension.Construction

noncomputable section

/-! A finite surjective map to the constructed Picard dual proves
its fixed dimension and supplies the original bundled dual API. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard

universe u
variable {S : Scheme.{u}} {g : ℕ} (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B.scheme) (m : B.scheme ⟶ D.abelian)
  [IsFinite m.left] [Surjective m.left]

def picardDualWithDimension : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B :=
  D.toBundled B (Dimension.Construction.quotient_smooth_dimension B
    { toOver := D.abelian
      group := D.group
      commutative := D.commutative
      smooth := D.smooth
      proper := D.proper
      geometricallyConnected := D.connected } m)

theorem picardDualWithDimension_scheme : (picardDualWithDimension B D m).abelian.scheme = D.abelian := rfl

theorem picardDualWithDimension_poincare : (picardDualWithDimension B D m).poincare = D.poincare := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.DualDimension.Construction
