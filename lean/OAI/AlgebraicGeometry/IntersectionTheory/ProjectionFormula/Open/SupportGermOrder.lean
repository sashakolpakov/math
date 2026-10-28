import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.OrderQuotientTransport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.StalkSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalParameterSum

/-! # Support Germ Order -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportGermOrder

noncomputable section

/-! Native principal colengths and divisor weights on corresponding
reduced supports agree under an open affine chart. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient

variable {Y X : Scheme} (j : Y ⟶ X) [IsOpenImmersion j]
  (A : IrreducibleCloseds Y) (B : IrreducibleCloseds X)
  (hAB : j (CycleClass.Thom.IntersectionGeometry.supportPoint A) = CycleClass.Thom.IntersectionGeometry.supportPoint B)
  (y : Y) (hyA : y ∈ (A : Set Y)) (hxB : j y ∈ (B : Set X)) (r : X.presheaf.stalk (j y))

include hAB

omit [IsOpenImmersion j] in
theorem nonzero_iff :
    Local.Principal.supportStalkMap Y A y hyA (j.stalkMap y r) ≠ 0 ↔ Local.Principal.supportStalkMap X B (j y) hxB r ≠ 0 := by
  have h := StalkSupport.kernelPrime_comap j A B hAB y hyA hxB
  change ¬ r ∈ (Stalk.PrimeQuotient.kernelPrime Y A y hyA).asIdeal.comap (j.stalkMap y).hom ↔
    ¬ r ∈ (Stalk.PrimeQuotient.kernelPrime X B (j y) hxB).asIdeal
  rw [h]

theorem order :
    Ring.ord ((CycleClass.Geometric.GenericPoint.reducedSupportScheme A).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage A y hyA))
      (Local.Principal.supportStalkMap Y A y hyA (j.stalkMap y r)) =
    Ring.ord ((CycleClass.Geometric.GenericPoint.reducedSupportScheme B).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage B (j y) hxB))
      (Local.Principal.supportStalkMap X B (j y) hxB r) := by
  let e := (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv
  let φ := Local.Principal.supportStalkMap X B (j y) hxB
  let ψ := Local.Principal.supportStalkMap Y A y hyA
  have hk : RingHom.ker ψ.hom = (RingHom.ker φ.hom).map e.toRingHom :=
    (StalkSupport.kernelPrime_map j A B hAB y hyA hxB).symm
  rw [OrderQuotientTransport.ord ψ.hom (Local.Principal.supportStalkMap_surjective Y A y hyA),
    OrderQuotientTransport.ord φ.hom (Local.Principal.supportStalkMap_surjective X B (j y) hxB)]
  exact OrderQuotientTransport.Ring.equiv e (RingHom.ker φ.hom) (RingHom.ker ψ.hom) hk r

include hyA hxB in
theorem weight : GlobalParameterSum.Weights.weight Y y (j.stalkMap y r) A =
    GlobalParameterSum.Weights.weight X (j y) r B := by
  rw [GlobalParameterSum.Weights.weight, dite_eq_left hyA,
    GlobalParameterSum.Weights.weight, dite_eq_left hxB]
  by_cases h : Local.Principal.supportStalkMap X B (j y) hxB r ≠ 0
  · have h' := (nonzero_iff j A B hAB y hyA hxB r).mpr h
    rw [ite_eq_left h', ite_eq_left h, order j A B hAB y hyA hxB r]
  · have h' : ¬ Local.Principal.supportStalkMap Y A y hyA (j.stalkMap y r) ≠ 0 :=
      fun hs => h ((nonzero_iff j A B hAB y hyA hxB r).mp hs)
    rw [ite_eq_right h', ite_eq_right h]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportGermOrder
