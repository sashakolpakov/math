import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.WittVector.DiscreteValuationRing

/-! # Rational Torsion -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.RationalTorsion

noncomputable section

/-! Vanishing after actual Witt fraction-field extension is detected
by an ordinary integer power of the residue characteristic. -/

open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p] [PerfectRing k p]
  (M : Type*) [AddCommGroup M] [Module (WittVector p k) M]

theorem one_tmul_eq_zero_iff (x : M) :
    (1 : FractionRing (WittVector p k)) ⊗ₜ[WittVector p k] x = 0 ↔
      ∃ n : ℕ, p^n • x = 0 := by
  rw [show (1 : FractionRing (WittVector p k)) ⊗ₜ[WittVector p k] x =
    (TensorProduct.mk (WittVector p k) (FractionRing (WittVector p k)) M 1) x from rfl,
    IsLocalizedModule.eq_zero_iff (nonZeroDivisors (WittVector p k))]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨n, b, hb⟩ := WittVector.exists_eq_pow_p_mul' s.val
      (mem_nonZeroDivisors_iff_ne_zero.mp s.property)
    refine ⟨n, ?_⟩
    change s.val • x = 0 at hs
    rw [hb, mul_comm, mul_smul] at hs
    have hzero : (p : WittVector p k)^n • x = 0 :=
      (IsUnit.smul_left_cancel b.isUnit).mp (hs.trans (smul_zero _).symm)
    simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using hzero
  · rintro ⟨n, hn⟩
    refine ⟨⟨(p : WittVector p k)^n,
      mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n (WittVector.p_nonzero p k))⟩, ?_⟩
    simpa only [Submonoid.mk_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using hn

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.RationalTorsion
