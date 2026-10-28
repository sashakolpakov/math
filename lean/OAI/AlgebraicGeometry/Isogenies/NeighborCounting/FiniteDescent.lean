import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IsogenyComplement
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Scheme

/-! # Finite Descent -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FiniteDescent.Lifts

/-! The proved full FiniteDescent quotient theorem supplies the native quotient
input. Both abelian-scheme bundles retain the same scheme and group law. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

/-- Full FiniteDescent, obtained from its proof rather than its statement checkpoint. -/
theorem verified_FiniteDescentInput : AbelianScheme.IsogenyQuotient.IsogenyComplement.Construction.FiniteDescentInput := by
  intro S A H _ i _ hi hH
  let A' : Quotients.FiniteDescent.AbelianQuotient.Construction.AbelianScheme S := {
    toOver := A.toOver
    group := A.group
    commutative := A.commutative
    proper := A.proper
    smooth := A.smooth
    connected := A.geometricallyConnected }
  obtain ⟨B, f, hf, hfinite, hsurj, hkernel, hquotient⟩ :=
    Quotients.FiniteDescent.Scheme.Construction.exists_abelian_scheme_quotient S A' H i hi hH
  let B' : Picard.PoincareBundle.Epi.Construction.AbelianScheme S := {
    toOver := B.toOver
    group := B.group
    commutative := B.commutative
    proper := B.proper
    smooth := B.smooth
    geometricallyConnected := B.connected }
  exact ⟨B', f, hf, hfinite, hsurj, hkernel, hquotient⟩

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FiniteDescent.Lifts
