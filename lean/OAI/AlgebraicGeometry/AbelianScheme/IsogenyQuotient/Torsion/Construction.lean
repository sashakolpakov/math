import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Unit
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.RepresentabilityAnd

/-! # Construction -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.Construction

/-!
The now-proved TorsionQuotient theorem discharges the complete named IsogenyQuotient input.
All torsion and subgroup-representability clauses are retained; no
statement placeholder or extra representability assumption is used.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

theorem verified_TorsionQuotientInput : Unit.Construction.TorsionQuotientInput := by
  intro S A _ _ _ _ _ n _ hn M _ _ _
  exact TorsionQuotient.RepresentabilityAnd.Construction.finite_etale_torsion_and_subgroup_parameters A n hn M

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.Construction
