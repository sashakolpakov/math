import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.Interchange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility

/-! # Poincare Interchange -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.PoincareInterchange.Construction

/-! The constructed original Poincare multiplications satisfy the
full PoincareBundle biextension interchange predicate. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

theorem originalPoincareMultiplications_interchange :
    Picard.PoincareBundle.Biextension.Compatibility.Interchange (PoincareLine.Construction.originalPoincarePoincareBundleLine D)
      (PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D) (PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D) := by
  intro T
  exact Poincare.Interchange.Construction.poincareProducts_interchange D

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.PoincareInterchange.Construction
