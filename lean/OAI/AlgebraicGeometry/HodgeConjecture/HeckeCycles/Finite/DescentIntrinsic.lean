import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Scheme
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IsogenyComplement

/-! # Descent Intrinsic -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.DescentIntrinsic.CM.Intrinsic

noncomputable section

/-! The proved full FiniteDescent quotient theorem supplies IsogenyQuotient's exact quotient
input, including its kernel on all tests and full invariant-map property. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}}

def toQuotientScheme (A : Picard.PoincareBundle.Epi.Construction.AbelianScheme S) : Quotients.FiniteDescent.AbelianQuotient.Construction.AbelianScheme S where
  toOver := A.toOver
  group := A.group
  commutative := A.commutative
  proper := A.proper
  smooth := A.smooth
  connected := A.geometricallyConnected

def fromQuotientScheme (A : Quotients.FiniteDescent.AbelianQuotient.Construction.AbelianScheme S) : Picard.PoincareBundle.Epi.Construction.AbelianScheme S where
  toOver := A.toOver
  group := A.group
  commutative := A.commutative
  smooth := A.smooth
  proper := A.proper
  geometricallyConnected := A.connected

theorem input : AbelianScheme.IsogenyQuotient.IsogenyComplement.Construction.FiniteDescentInput := by
  intro S A H hgroup i himon hi hH
  obtain ⟨B, f, hf, hfinite, hsurj, hkernel, hquotient⟩ :=
    @Quotients.FiniteDescent.Scheme.Construction.exists_abelian_scheme_quotient S (toQuotientScheme A) H hgroup i himon hi hH
  exact ⟨fromQuotientScheme B, f, hf, hfinite, hsurj, hkernel, hquotient⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.DescentIntrinsic.CM.Intrinsic
