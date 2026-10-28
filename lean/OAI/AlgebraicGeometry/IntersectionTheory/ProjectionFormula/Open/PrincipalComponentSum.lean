import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.PrincipalEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.PrincipalIsolation
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportGermOrder
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GeometricPrincipalQuotient

/-! # Principal Component Sum -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.PrincipalComponentSum

noncomputable section

/-! A native quotient pairing computed in an open chart is a sum
on the fixed intersection components of the ambient scheme. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal

theorem coefficient {Y X : Scheme} [IsLocallyNoetherian Y] [IsLocallyNoetherian X] [NoetherianSpace X]
    (j : Y ⟶ X) [IsOpenImmersion j]
    (A B : IrreducibleCloseds Y) (A' B' : IrreducibleCloseds X)
    (hA : j (CycleClass.Thom.IntersectionGeometry.supportPoint A) = CycleClass.Thom.IntersectionGeometry.supportPoint A') (hB : j (CycleClass.Thom.IntersectionGeometry.supportPoint B) = CycleClass.Thom.IntersectionGeometry.supportPoint B')
    (y : Y) [IsDomain (X.presheaf.stalk (j y))]
    (hyA : y ∈ (A : Set Y)) (hyB : y ∈ (B : Set Y))
    (hxA : j y ∈ (A' : Set X)) (hxB : j y ∈ (B' : Set X)) (r : X.presheaf.stalk (j y))
    (hr : Local.Principal.supportStalkMap Y A y hyA (j.stalkMap y r) ≠ 0)
    (d : ℕ) [HasProjectiveDimensionLE (CycleClass.Thom.IntersectionGeometry.localSupportModule X B' (j y) hxB) d]
    (hiso : Module.support (Y.presheaf.stalk y)
        (QuotSMulTop (j.stalkMap y r) (CycleClass.Thom.IntersectionGeometry.localSupportModule Y A y hyA)) ∩
      Module.support (Y.presheaf.stalk y) (CycleClass.Thom.IntersectionGeometry.localSupportModule Y B y hyB) ⊆
        {IsLocalRing.closedPoint (Y.presheaf.stalk y)}) :
    Tor.Euler.euler (Y.presheaf.stalk y)
      (.of _ (QuotSMulTop (j.stalkMap y r) (CycleClass.Thom.IntersectionGeometry.localSupportModule Y A y hyA)))
      (CycleClass.Thom.IntersectionGeometry.localSupportModule Y B y hyB) d =
      ∑ C ∈ Finite.ClosedComponents.components X (IsolatedGeometricComponents.intersection X A' B'),
        TotalTorCoefficient.coefficient X A' B' (CycleClass.Thom.IntersectionGeometry.supportPoint C) d *
          GlobalParameterSum.Weights.weight X (j y) r C := by
  rw [PrincipalEuler.euler j A B A' B' hA hB y hyA hyB hxA hxB r d]
  exact GeometricPrincipalQuotient.All.coefficient X A' B' (j y) hxA hxB r
    ((SupportGermOrder.nonzero_iff j A A' hA y hyA hxA r).mp hr) d
    (PrincipalIsolation.isolated j A B A' B' hA hB y hyA hyB hxA hxB r hiso)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.PrincipalComponentSum
