import OAI.NumberTheory.PadicHodge.GeometricComparison.CochainQuotientCohomology

/-! # Cochain Reduction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CochainReduction.CochainReductionDivisibility

noncomputable section

/-! Vanishing after coefficient reduction detects scalar divisibility of original cohomology. -/

open _root_.CategoryTheory

universe u v
variable (R : Type u) [CommRing R] (C : CochainComplex (ModuleCat.{v} R) ℕ) (r : R)
  (hreg : ∀ a, IsSMulRegular (C.X a) r)

include hreg

theorem zero_iff (i : ℕ) (x : C.homology i) :
    CochainQuotientCohomology.PrincipalCochainQuotient.reduction R C r 1 i x = 0 ↔ ∃ y, r • y = x := by
  rw [← LinearMap.mem_ker, CochainQuotientCohomology.PrincipalCochainQuotient.reduction_ker R C r hreg]
  simpa only [pow_one] using IntegralComparison.Principal.PowerModuleSequence.mem_submodule R (C.homology i) r 1 x

theorem image_divisible (i : ℕ) (F : Module.End R (C.homology i))
    (L : Submodule R (C.homology i))
    (hF : ∀ x ∈ L, CochainQuotientCohomology.PrincipalCochainQuotient.reduction R C r 1 i (F x) = 0) :
    ∀ x ∈ L, ∃ y, F x = r • y := by
  intro x hx
  obtain ⟨y, hy⟩ := (zero_iff R C r hreg i (F x)).mp (hF x hx)
  exact ⟨y, hy.symm⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CochainReduction.CochainReductionDivisibility
