import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.IsomorphismTor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportGermOrder

/-! # Isomorphism Germ Order -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.IsomorphismGermOrder

noncomputable section

/-! Principal orders on native reduced supports are invariant under
an isomorphism of the ambient stalks, including stalk localizations. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal

theorem order {Y X : Scheme} (j : Y ⟶ X)
    (A : IrreducibleCloseds Y) (B : IrreducibleCloseds X)
    (hAB : j (CycleClass.Thom.IntersectionGeometry.supportPoint A) = CycleClass.Thom.IntersectionGeometry.supportPoint B)
    (y : Y) [IsIso (j.stalkMap y)]
    (hyA : y ∈ (A : Set Y)) (hxB : j y ∈ (B : Set X)) (r : X.presheaf.stalk (j y)) :
    Ring.ord ((CycleClass.Geometric.GenericPoint.reducedSupportScheme A).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage A y hyA))
      (Principal.supportStalkMap Y A y hyA (j.stalkMap y r)) =
    Ring.ord ((CycleClass.Geometric.GenericPoint.reducedSupportScheme B).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage B (j y) hxB))
      (Principal.supportStalkMap X B (j y) hxB r) := by
  let e := (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv
  let φ := Principal.supportStalkMap X B (j y) hxB
  let ψ := Principal.supportStalkMap Y A y hyA
  have hk : RingHom.ker ψ.hom = (RingHom.ker φ.hom).map e.toRingHom :=
    (IsomorphismTor.kernel_map j A B hAB y hyA hxB).symm
  rw [OrderQuotientTransport.ord ψ.hom (Principal.supportStalkMap_surjective Y A y hyA),
    OrderQuotientTransport.ord φ.hom (Principal.supportStalkMap_surjective X B (j y) hxB)]
  exact OrderQuotientTransport.Ring.equiv e (RingHom.ker φ.hom) (RingHom.ker ψ.hom) hk r

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.IsomorphismGermOrder
