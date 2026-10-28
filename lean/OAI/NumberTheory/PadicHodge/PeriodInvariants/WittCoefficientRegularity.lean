import Mathlib

/-! # Witt Coefficient Regularity -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.WittCoefficientRegularity

/-!
# Regular zeroth coefficients give regular Witt vectors

The proof uses p-torsion-freeness and p-adic separation of Witt vectors
over a perfect ring. No domain assumption on the coefficient ring occurs.
-/

variable (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]

theorem p_regular : IsSMulRegular (WittVector p R) (p : WittVector p R) := by
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro x hx
  apply WittVector.eq_zero_of_p_mul_eq_zero x
  simpa only [smul_eq_mul, mul_comm] using hx

theorem eq_zero_of_mul_eq_zero (w x : WittVector p R)
    (hw : IsSMulRegular R (w.coeff 0)) (hx : w * x = 0) : x = 0 := by
  have hp : ∀ n : ℕ, (p : WittVector p R) ^ n ∣ x := by
    intro n
    induction n with
    | zero => simp only [pow_zero, one_dvd]
    | succ n ih =>
      obtain ⟨a, ha⟩ := ih
      have hwa : w * a = 0 := by
        apply ((p_regular p (R := R)).pow n).isLeftRegular
        change (p : WittVector p R) ^ n * (w * a) = (p : WittVector p R) ^ n * 0
        rw [mul_zero]
        calc
          (p : WittVector p R) ^ n * (w * a) = w * x := by rw [ha]; ring
          _ = 0 := hx
      have ha0 : a.coeff 0 = 0 := by
        apply hw.right_eq_zero_of_smul
        have he := congrArg (WittVector.constantCoeff (p := p)) hwa
        rw [map_mul, map_zero] at he
        exact he
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp
        ((WittVector.mem_span_p_iff_coeff_zero_eq_zero a).mpr ha0)
      exact ⟨b, by rw [ha, hb, pow_succ, mul_assoc]⟩
  apply IsHausdorff.haus' (I := Ideal.span {(p : WittVector p R)})
  intro n
  simpa only [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton] using hp n

theorem regular_of_coefficient (w : WittVector p R)
    (hw : IsSMulRegular R (w.coeff 0)) : IsSMulRegular (WittVector p R) w := by
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro x hx
  exact eq_zero_of_mul_eq_zero p w x hw hx

end OAI.NumberTheory.PadicHodge.PeriodInvariants.WittCoefficientRegularity
