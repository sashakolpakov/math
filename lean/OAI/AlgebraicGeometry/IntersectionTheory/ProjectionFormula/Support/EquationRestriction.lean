import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports

/-! # Equation Restriction -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.EquationRestriction

noncomputable section

/-! A local defining equation restricts nontrivially to an integral
support precisely when that support is not contained in its zero locus. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient

theorem nonzero (X : Scheme) (A B : IrreducibleCloseds X) (x : X)
    (hxA : x ∈ (A : Set X)) (hxB : x ∈ (B : Set X))
    (r : X.presheaf.stalk x)
    (hr : RingHom.ker (Local.Principal.supportStalkMap X B x hxB).hom = Ideal.span {r})
    (hAB : ¬ A ≤ B) : Local.Principal.supportStalkMap X A x hxA r ≠ 0 := by
  intro hz
  let p : PrimeSpectrum (X.presheaf.stalk x) := Stalk.PrimeQuotient.kernelPrime X B x hxB
  let q : PrimeSpectrum (X.presheaf.stalk x) := Stalk.PrimeQuotient.kernelPrime X A x hxA
  have hle : p ≤ q := by
    change RingHom.ker (Local.Principal.supportStalkMap X B x hxB).hom ≤
      RingHom.ker (Local.Principal.supportStalkMap X A x hxA).hom
    rw [hr]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (RingHom.mem_ker.mpr hz))
  have hs : CycleClass.Thom.IntersectionGeometry.supportPoint B ⤳ CycleClass.Thom.IntersectionGeometry.supportPoint A := by
    have h := ((PrimeSpectrum.le_iff_specializes p q).mp hle).map (X.fromSpecStalk x).continuous
    simpa only [p, q, Stalk.PrimeQuotient.kernelPrime_image] using h
  have hx : CycleClass.Thom.IntersectionGeometry.supportPoint A ∈ (B : Set X) := hs.mem_closed B.isClosed
    (B.isIrreducible.isGenericPoint_genericPoint B.isClosed).mem
  apply hAB
  exact (Supports.supportPoint_mem_iff_subset
    (⟨(B : Set X), B.isClosed⟩ : Closeds X) A).mp hx

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.EquationRestriction
