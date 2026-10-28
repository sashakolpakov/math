import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles

/-! # Poincare Line -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.PoincareLine.Construction

noncomputable section

/-! The actual original HilbertConstruction Poincare sheaf, viewed as an PoincareBundle line
bundle with the same local trivializations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data

universe u

def originalPoincarePoincareBundleLine {S : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) : Picard.PoincareBundle.Line.Bundles.LineBundle (D.abelian.scheme ⊗ A.scheme).left :=
  ⟨D.poincare.sheaf, D.poincare.locallyTrivial⟩

theorem originalPoincarePoincareBundleLine_sheaf {S : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) : (originalPoincarePoincareBundleLine D).sheaf = D.poincare.sheaf := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.PoincareLine.Construction
