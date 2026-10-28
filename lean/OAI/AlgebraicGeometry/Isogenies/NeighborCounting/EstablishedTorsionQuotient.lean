import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Unit
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.RepresentabilityAnd

/-! # Established Torsion Quotient -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EstablishedTorsionQuotient

/-! The full TorsionQuotient consumer interface is inhabited by the actual finite étale
torsion and subgroup-functor representability theorem. No geometric realization
is replaced by an abstract functor or an additional assumption. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

theorem fullTorsionQuotientInput : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput := by
  intro S A _ _ _ _ _ m _ hm_unit M _ _ _
  exact AbelianScheme.TorsionQuotient.RepresentabilityAnd.Construction.finite_etale_torsion_and_subgroup_parameters A m hm_unit M

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EstablishedTorsionQuotient
