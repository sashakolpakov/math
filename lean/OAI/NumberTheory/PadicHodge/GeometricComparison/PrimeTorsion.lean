import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Algebra.Module.Torsion.Free

/-! # Prime Torsion -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.PrimeTorsion.PrimeTorsionCriterion

noncomputable section

/-! Over the p-adic integers, absence of p-torsion implies torsion-freeness. -/

theorem torsionFree (p : ℕ) [Fact p.Prime] {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]
    (hp : ∀ x : M, (p : ℤ_[p]) • x = 0 → x = 0) : Module.IsTorsionFree ℤ_[p] M := by
  have hpow : ∀ (n : ℕ) (x : M), (p : ℤ_[p]) ^ n • x = 0 → x = 0 := by
    intro n
    induction n with
    | zero => intro x hx; simpa only [pow_zero, one_smul] using hx
    | succ n ih =>
      intro x hx
      apply ih x
      apply hp
      simpa only [pow_succ', mul_smul] using hx
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro r x hx
  by_cases hr : r = 0
  · exact Or.inl hr
  right
  rw [PadicInt.unitCoeff_spec hr, mul_smul] at hx
  exact hpow r.valuation x ((PadicInt.unitCoeff hr).isUnit.smul_eq_zero.mp hx)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.PrimeTorsion.PrimeTorsionCriterion
