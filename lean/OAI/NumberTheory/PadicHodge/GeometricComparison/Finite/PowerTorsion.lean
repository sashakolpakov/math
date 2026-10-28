import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Noetherian.Defs

/-! # Power Torsion -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.PowerTorsion.FinitePowerTorsion

noncomputable section

/-! In a Noetherian module, power torsion has a uniform exponent and no nonzero infinitely divisible compatible tower. -/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [IsNoetherian R M] (r : R)

def kernels : ℕ →o Submodule R M where
  toFun n := Submodule.torsionBy R M (r ^ n)
  monotone' a b hab := by
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
    intro x hx
    change r ^ (a + c) • x = 0
    change r ^ a • x = 0 at hx
    rw [pow_add, mul_comm, mul_smul, hx, smul_zero]

theorem bounded : ∃ N : ℕ, ∀ x : M, (∃ n : ℕ, r ^ n • x = 0) → r ^ N • x = 0 := by
  obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian R M)
    (kernels (M := M) r)
  refine ⟨N, ?_⟩
  rintro x ⟨n, hn⟩
  have hx : x ∈ kernels (M := M) r n := hn
  have hm : x ∈ kernels (M := M) r (max n N) :=
    (kernels (M := M) r).monotone (le_max_left n N) hx
  rw [← hN (max n N) (le_max_right n N)] at hm
  exact hm

theorem compatible_zero (x : ℕ → M)
    (htorsion : ∀ n, ∃ a : ℕ, r ^ a • x n = 0)
    (hcompat : ∀ n, r • x (n + 1) = x n) : ∀ n, x n = 0 := by
  obtain ⟨N, hN⟩ := bounded (M := M) r
  have hiter (n a : ℕ) : r ^ a • x (n + a) = x n := by
    induction a with
    | zero => simp
    | succ a ih =>
        rw [pow_succ, mul_smul, show n + (a + 1) = (n + a) + 1 by omega,
          hcompat, ih]
  intro n
  exact (hiter n N).symm.trans (hN (x (n + N)) (htorsion (n + N)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.PowerTorsion.FinitePowerTorsion
