import Mathlib

/-! # Principal Completion -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.PrincipalCompletion

noncomputable section

/-! Separation and regularity for completion at a principal ideal. -/

variable {R : Type*} [CommRing R]

theorem eval_factor (I : Ideal R) {m n : ℕ} (h : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  apply AdicCompletion.induction_on I R x
  intro c
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk]
  apply Ideal.Quotient.eq.mpr
  simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using (c.property h).symm

theorem completion_generator_cancel [IsDomain R] (I : Ideal R) (q : R)
    (hI : I = Ideal.span {q}) (hq : q ≠ 0) (x : AdicCompletion I R)
    (hx : algebraMap R (AdicCompletion I R) q * x = 0) : x = 0 := by
  subst I
  apply AdicCompletion.ext_evalₐ
  intro n
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (Ideal.span {q}) (n + 1) x)
  have he := congrArg (AdicCompletion.evalₐ (Ideal.span {q}) (n + 1)) hx
  change AdicCompletion.evalₐ _ (n + 1) (AdicCompletion.of _ R q * x) = _ at he
  rw [map_mul, AdicCompletion.evalₐ_of, ← ha, ← map_mul, map_zero] at he
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at he
  obtain ⟨b, hb⟩ := he
  have hab : a = q ^ n * b := by
    apply mul_left_cancel₀ hq
    rw [hb, pow_succ]
    ring
  have hz : Ideal.Quotient.mk ((Ideal.span {q}) ^ n) a = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (by
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact ⟨b, hab⟩)
  have hc := eval_factor (Ideal.span {q}) (Nat.le_succ n) x
  rw [← ha, Ideal.Quotient.factor_mk, hz] at hc
  rw [← hc, map_zero]

theorem exists_order_factor_aux (q x : R) (N : ℕ) (hN : ¬q ^ N ∣ x) :
    ∃ n : ℕ, ∃ a : R, x = q ^ n * a ∧ ¬q ∣ a := by
  induction N generalizing x with
  | zero => exact (hN (by simp)).elim
  | succ N ih =>
    by_cases hx : q ∣ x
    · obtain ⟨y, rfl⟩ := hx
      have hy : ¬q ^ N ∣ y := by
        rintro ⟨b, hb⟩
        apply hN
        refine ⟨b, ?_⟩
        rw [hb, pow_succ]
        ring
      obtain ⟨n, a, ha, hqa⟩ := ih y hy
      refine ⟨n + 1, a, ?_, hqa⟩
      rw [ha, pow_succ]
      ring
    · exact ⟨0, x, by simp, hx⟩

theorem exists_order_factor (q : R) [IsHausdorff (Ideal.span {q}) R]
    (x : R) (hx : x ≠ 0) : ∃ n : ℕ, ∃ a : R, x = q ^ n * a ∧ ¬q ∣ a := by
  have hN : ∃ n : ℕ, ¬q ^ n ∣ x := by
    by_contra h
    push Not at h
    apply hx
    apply IsHausdorff.haus (show IsHausdorff (Ideal.span {q}) R from inferInstance)
    intro n
    rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact h n
  obtain ⟨N, hN⟩ := hN
  exact exists_order_factor_aux q x N hN

theorem isUnit_of_residue_ne_zero {F : Type*} [Field F] (f : R →+* F)
    (hs : Function.Surjective f) (hJ : RingHom.ker f ≤ (⊥ : Ideal R).jacobson)
    (x : R) (hx : f x ≠ 0) : IsUnit x := by
  obtain ⟨y, hy⟩ := hs ((f x)⁻¹)
  have he : x * y - 1 ∈ RingHom.ker f := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_one, hy, mul_inv_cancel₀ hx, sub_self]
  exact isUnit_of_mul_isUnit_left (Ideal.isUnit_of_sub_one_mem_jacobson_bot _ (hJ he))

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.PrincipalCompletion
