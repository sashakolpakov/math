import OAI.AlgebraicGeometry.CycleClass.Thom.Local.Euler
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.QuotientBaseChange
import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport

/-! # Euler Empty -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Local.EulerEmpty.Constructions

noncomputable section

/-! With no equations remaining, the actual local Euler functional
at a cycle's generic point is exactly its original coefficient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.CycleClass.Thom.Local.Euler.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme
open OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Supports OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Flat.Tor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) (C : Geometric.DimensionCycles.DimensionCycleSupport V p)

theorem support_eq_of_generic_mem (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
    (h : IntersectionGeometry.supportPoint C.val ∈ (D.val : Set V.carrier)) : D = C := by
  have hCD : C.val ≤ D.val := by
    change (C.val : Set V.carrier) ⊆ (D.val : Set V.carrier)
    exact (Intersection.Supports.supportPoint_mem_iff_subset ⟨(D.val : Set V.carrier), D.val.isClosed⟩ C.val).mp h
  apply Subtype.ext
  by_contra hn
  have hl := Intersection.Supports.codimension_strictAnti V.presentation (lt_of_le_of_ne hCD (Ne.symm hn))
  rw [Integral.ProductSupport.Constructions.integralPresentation_supportCodimension, Integral.ProductSupport.Constructions.integralPresentation_supportCodimension,
    C.property, D.property] at hl
  exact Nat.lt_irrefl p hl

theorem supportEuler_empty_self (d : ℕ) : Euler.Constructions.supportEuler V p (IntersectionGeometry.supportPoint C.val) [] d C = 1 := by
  let x := IntersectionGeometry.supportPoint C.val
  let R := V.carrier.presheaf.stalk x
  have hx : x ∈ (C.val : Set V.carrier) :=
    C.val.isIrreducible.isGenericPoint_genericPoint C.val.isClosed |>.mem
  have hp : StalkPrimeQuotient.Constructions.kernelPrime V.carrier C.val x hx = IsLocalRing.closedPoint R := by
    apply (V.carrier.fromSpecStalk x).isEmbedding.injective
    exact (StalkPrimeQuotient.Constructions.kernelPrime_image V.carrier C.val x hx).trans Scheme.fromSpecStalk_closedPoint.symm
  have hl : Module.length R (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier C.val x hx) = 1 := by
    change Module.length R (R ⧸ (StalkPrimeQuotient.Constructions.kernelPrime V.carrier C.val x hx).asIdeal) = 1
    rw [hp]
    exact TorAlgebra.QuotientBaseChange.Tor.residue_quotient_length R
  let e : (R ⧸ Ideal.ofList []) ≃ₗ[R] R :=
    Submodule.quotEquivOfEqBot (R := R) (M := R) (Ideal.ofList []) (Ideal.ofList_nil (R := R))
  rw [Euler.Constructions.supportEuler_of_mem V p x [] d C hx]
  have h := TorAlgebra.Flat.Tor.euler_length_of_unit R (ModuleCat.of R (R ⧸ Ideal.ofList []))
    (ModuleCat.of R (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier C.val x hx)) e d
  exact h.trans (by rw [hl]; rfl)

theorem supportEuler_empty (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (d : ℕ) :
    Euler.Constructions.supportEuler V p (IntersectionGeometry.supportPoint C.val) [] d D = if D = C then 1 else 0 := by
  by_cases h : D = C
  · subst D
    exact (supportEuler_empty_self V p C d).trans (ite_eq_left rfl).symm
  · exact (Euler.Constructions.supportEuler_of_not_mem V p (IntersectionGeometry.supportPoint C.val) [] d D
      (fun hx => h (support_eq_of_generic_mem V p C D hx))).trans (ite_eq_right h).symm

theorem localCycleEuler_empty (c : Geometric.DimensionCycles.RationalDimensionCycle V p) (d : ℕ) :
    Euler.Constructions.localCycleEuler V p (IntersectionGeometry.supportPoint C.val) [] d c = c C := by
  rw [Euler.Constructions.localCycleEuler_eq_sum]
  simp only [supportEuler_empty, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.mp h).symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Local.EulerEmpty.Constructions
