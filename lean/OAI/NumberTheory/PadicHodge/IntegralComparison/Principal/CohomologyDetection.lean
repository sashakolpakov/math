import OAI.NumberTheory.PadicHodge.GeometricComparison.CochainQuotientCohomology
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.ModuleAdicCompleteness

/-! # Cohomology Detection -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CohomologyDetection

noncomputable section

/-! Actual coefficient-power reductions detect cohomology classes whenever
the original cohomology is separated. No finiteness in the next degree is
needed for this assertion. -/

open _root_.CategoryTheory

universe u v
variable (R : Type u) [CommRing R]
  (C : CochainComplex (ModuleCat.{v} R) ℕ) (r : R)
  (hreg : ∀ a, IsSMulRegular (C.X a) r) (i : ℕ)

include hreg

theorem eq_zero [IsHausdorff (Ideal.span {r}) (C.homology i)]
    (x : C.homology i)
    (hx : ∀ n, GeometricComparison.CochainQuotientCohomology.PrincipalCochainQuotient.reduction R C r n i x = 0) : x = 0 := by
  apply IsHausdorff.haus' (I := Ideal.span {r}) x
  intro n
  apply SModEq.zero.mpr
  change x ∈ PowerModuleSequence.submodule R (C.homology i) r n
  rw [← GeometricComparison.CochainQuotientCohomology.PrincipalCochainQuotient.reduction_ker R C r hreg n i]
  exact hx n

theorem eq_zero_of_successors [IsHausdorff (Ideal.span {r}) (C.homology i)]
    (x : C.homology i)
    (hx : ∀ n, GeometricComparison.CochainQuotientCohomology.PrincipalCochainQuotient.reduction R C r (n+1) i x = 0) : x = 0 := by
  apply eq_zero R C r hreg i x
  intro n
  rw [← GeometricComparison.CochainQuotientCohomology.PrincipalCochainQuotient.reduction_transition R C r i n (n+1)
    (Nat.le_succ n) x, hx n, map_zero]

theorem finite_eq_zero [IsNoetherianRing R] [IsAdicComplete (Ideal.span {r}) R]
    [Module.Finite R (C.homology i)] (x : C.homology i)
    (hx : ∀ n, GeometricComparison.CochainQuotientCohomology.PrincipalCochainQuotient.reduction R C r (n+1) i x = 0) : x = 0 := by
  let := AlgebraicGeometry.Crystalline.Cohomology.Finite.ModuleAdicCompleteness.FiniteModuleAdicCompleteness.complete R
    (Ideal.span {r}) (C.homology i)
  exact eq_zero_of_successors R C r hreg i x hx

theorem finite_exists_nonzero_reduction
    [IsNoetherianRing R] [IsAdicComplete (Ideal.span {r}) R]
    [Module.Finite R (C.homology i)] (x : C.homology i) (hx : x ≠ 0) :
    ∃ n, GeometricComparison.CochainQuotientCohomology.PrincipalCochainQuotient.reduction R C r (n+1) i x ≠ 0 := by
  by_contra! h
  exact hx (finite_eq_zero R C r hreg i x h)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CohomologyDetection
