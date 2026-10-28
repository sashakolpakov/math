import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.DivisorWeights
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Truncation

/-! # Geometric Divisor Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GeometricDivisorEuler

noncomputable section

/-! The local weighted order formula uses precisely ThomClass's geometric
intersection multiplicities on the closures of the height-one primes. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport

theorem intersectionMultiplicity_eq_euler (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (A C : IrreducibleCloseds X.carrier)
    (hx : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (A : Set X.carrier))
    (p : Spec (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C))) :
    CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X (Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C) p) A C =
      Tor.Euler.euler (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C))
        (.of _ (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C) ⧸ p.asIdeal))
        (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier A (CycleClass.Thom.IntersectionGeometry.supportPoint C) hx) m := by
  have hp := Stalk.DivisorSupport.point_mem_primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C) p
  rw [Truncation.intersectionMultiplicity_eq_relative_sum X m _ A C hp hx]
  exact PrimeFiltrationEuler.euler_iso_left _
    (Stalk.PrimeQuotient.moduleEquiv X.carrier (Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C) p)
      (CycleClass.Thom.IntersectionGeometry.supportPoint C) hp p (Stalk.DivisorSupport.primeClosure_point X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C) p).symm).toModuleIso _ m

theorem order_eq_intersection_sum (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (A : X.DimensionCycleSupport 1) (C : X.DimensionCycleSupport 2)
    (hx : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier))
    (r : X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))
    (hra : Local.Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx r ≠ 0) :
    let R := X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
    ∃ S : Finset (Spec R),
      (∀ p ∈ S, p.asIdeal.height = 1 ∧ r ∈ p.asIdeal ∧
        X.supportCodimension (Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p) = 1) ∧
      (∀ p : Spec R, p.asIdeal.height = 1 → p ∉ S →
        Ring.ord (Localization.AtPrime p.asIdeal)
          (algebraMap R (Localization.AtPrime p.asIdeal) r) = 0) ∧
      ((Ring.ord ((CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).presheaf.stalk
          (CycleClass.Thom.IntersectionGeometry.supportPreimage A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx))
        (Local.Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx r)).toNat : ℚ) =
        ∑ p ∈ S, ((Ring.ord (Localization.AtPrime p.asIdeal)
          (algebraMap R (Localization.AtPrime p.asIdeal) r)).toNat : ℚ) *
          CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X (Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p) A.val C.val := by
  obtain ⟨S, hS, hout, he⟩ := Local.DivisorWeights.order_eq_weighted_sum X m A C hx r hra
  have hCA : C.val ≤ A.val :=
    (Supports.supportPoint_mem_iff_subset
      (⟨(A.val : Set X.carrier), A.val.isClosed⟩ : Closeds X.carrier) C.val).mp hx
  refine ⟨S, fun p hp => ⟨(hS p hp).1, (hS p hp).2,
    Stalk.DivisorSupport.primeClosure_codimension X m A C hCA p (hS p hp).1⟩, hout, ?_⟩
  rw [he]
  apply Finset.sum_congr rfl
  intro p _
  rw [intersectionMultiplicity_eq_euler X m A.val C.val hx p]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GeometricDivisorEuler
