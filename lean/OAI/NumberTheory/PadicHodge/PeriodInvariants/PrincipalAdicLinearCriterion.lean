import OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicMapInjectivity
import OAI.NumberTheory.PadicHodge.PeriodInvariants.ScalarDivisibilityModules

/-! # Principal Adic Linear Criterion -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.PrincipalAdicLinearCriterion

/-! # A separated linear map with injective principal reduction is injective -/

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] (q : R) (f : M →ₗ[R] N)
  (hq : IsSMulRegular N q)
  (hf : ∀ x, (∃ y, q • y = f x) → ∃ y, q • y = x)

include hq hf in
theorem reflects_power (n : ℕ) (x : M) (hx : ∃ y, q ^ n • y = f x) :
    ∃ y, q ^ n • y = x := by
  induction n generalizing x with
  | zero => exact ⟨x, by rw [pow_zero, one_smul]⟩
  | succ n ih =>
    obtain ⟨y, hy⟩ := hx
    have hfirst : q • (q ^ n • y) = f x := by rw [← mul_smul, ← pow_succ']; exact hy
    obtain ⟨z, hz⟩ := hf x ⟨q ^ n • y, hfirst⟩
    have hrest : q ^ n • y = f z := by
      apply hq
      change q • (q ^ n • y) = q • f z
      rw [hfirst, ← hz, map_smul]
    obtain ⟨w, hw⟩ := ih z ⟨y, hrest⟩
    exact ⟨w, by rw [pow_succ', mul_smul, hw, hz]⟩

include hq hf in
theorem injective [IsHausdorff (Ideal.span {q}) M] : Function.Injective f := by
  apply (injective_iff_map_eq_zero f).mpr
  intro x hx
  apply IsHausdorff.haus' (I := Ideal.span {q})
  intro n
  have hn := reflects_power q f hq hf n x ⟨0, by rw [smul_zero, hx]⟩
  have hm := (ScalarDivisibilityModules.principal_power_mem q n x).mpr hn
  simpa only [SModEq.sub_mem, sub_zero] using hm

end OAI.NumberTheory.PadicHodge.PeriodInvariants.PrincipalAdicLinearCriterion
