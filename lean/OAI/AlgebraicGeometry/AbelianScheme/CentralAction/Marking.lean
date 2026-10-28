import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Arithmetic
import Mathlib.RingTheory.Coprime.Lemmas

/-! # Marking -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Marking.Construction

noncomputable section

/-! The actual finite ring of scalar full-level labels, and the elementary
reason that congruence to one fixes all N-torsion in every O_E-module. -/

open _root_.NumberField

variable (E : Type*) [Field E] [NumberField E]

abbrev LevelRing (N : ℕ) := 𝓞 E ⧸ Ideal.span ({(N : 𝓞 E)} : Set (𝓞 E))

def levelReduction (N : ℕ) : 𝓞 E →+* LevelRing E N := Ideal.Quotient.mk _

theorem finite_level_ring (N : ℕ) (hN : 0 < N) : Finite (LevelRing E N) := by
  have hN0 : (N : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hN)
  exact Ring.HasFiniteQuotients.finiteQuotient
    (I := Ideal.span ({(N : 𝓞 E)} : Set (𝓞 E)))
    (mt Ideal.span_singleton_eq_bot.mp hN0)

omit [NumberField E] in
theorem level_natCast_zero (N : ℕ) : (N : LevelRing E N) = 0 := by
  change levelReduction E N (N : 𝓞 E) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Set.mem_singleton _)

omit [NumberField E] in
theorem level_prime_unit (N q : ℕ) (h : Nat.Coprime q N) :
    IsUnit (levelReduction E N (q : 𝓞 E)) := by
  have hc := h.isCoprime.map (Int.castRingHom (LevelRing E N))
  simp only [map_natCast, level_natCast_zero, isCoprime_zero_right] at hc
  exact hc

omit [NumberField E] in
theorem level_eq_one_iff (N : ℕ) (b : 𝓞 E) :
    levelReduction E N b = 1 ↔ b - 1 ∈ Ideal.span ({(N : 𝓞 E)} : Set (𝓞 E)) := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change levelReduction E N b = 1 ↔ levelReduction E N (b - 1) = 0
  rw [map_sub, map_one, sub_eq_zero]

omit [NumberField E] in
theorem congruent_scalar_fixes_torsion
    {M : Type*} [AddCommGroup M] [Module (𝓞 E) M]
    (N : ℕ) (b : 𝓞 E) (hlevel : levelReduction E N b = 1)
    (x : M) (hx : N • x = 0) : b • x = x := by
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp ((level_eq_one_iff E N b).mp hlevel)
  have hb : b = 1 + (N : 𝓞 E) * r := by
    rw [← hr]
    abel
  rw [hb, add_smul, one_smul, mul_comm (N : 𝓞 E), mul_smul,
    Nat.cast_smul_eq_nsmul, hx, smul_zero, add_zero]

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Marking.Construction
