import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Fields
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Etale.Field

/-! # Etale Degree -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.EtaleDegree

noncomputable section

/-! The sum of residue degrees in any fiber of a finite flat
unramified algebra over a domain is its generic module rank. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem algebra_sum (R S : Type) [CommRing R] [CommRing S] [IsDomain R] [Algebra R S]
    [Module.Finite R S] [Module.Flat R S] [Algebra.FormallyUnramified R S]
    (p : Ideal R) [p.IsPrime] [Fintype (p.primesOver S)] :
    ∑ q : p.primesOver S, q.val.inertiaDeg R = Module.finrank R S := by
  have h := Ideal.sum_ramification_inertia_eq_finrank p S
  refine (Finset.sum_congr rfl ?_).trans h
  intro q _
  let : q.val.IsPrime := q.property.1
  rw [Ideal.ramificationIdx_eq_one, one_mul]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.EtaleDegree
