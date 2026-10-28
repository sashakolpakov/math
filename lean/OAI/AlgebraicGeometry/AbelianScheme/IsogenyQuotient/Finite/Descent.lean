import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IsogenyComplement
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Scheme

/-! # Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.Descent.Construction

/-! The accepted FiniteDescent theorem supplies the complete IsogenyQuotient quotient input.
The conversion preserves the underlying scheme, group law, exact kernel
on every test scheme, and universal property for invariant morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

set_option backward.isDefEq.respectTransparency false in
theorem verifiedFiniteDescentInput : IsogenyComplement.Construction.FiniteDescentInput := by
  intro S A H _ i _ hi hH
  let A' : Quotients.FiniteDescent.AbelianQuotient.Construction.AbelianScheme S := { toOver := A.toOver }
  obtain ⟨B, q, hq, hf, hs, hk, hu⟩ :=
    Quotients.FiniteDescent.Scheme.Construction.exists_abelian_scheme_quotient S A' H i hi hH
  let B' : Picard.PoincareBundle.Epi.Construction.AbelianScheme S := { toOver := B.toOver }
  exact ⟨B', q, hq, hf, hs, hk, hu⟩

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.Descent.Construction
