import Mathlib

/-! # Adic Generation -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.AdicGeneration

noncomputable section

/-!
An explicit adic lifting argument for a principal ideal. The digit-step
hypothesis will be discharged for Fontaine theta using the actual tilt.
-/

variable {R : Type*} [CommRing R]

/-- In a q-adically complete ring, generation by c modulo q lifts to exact
generation when the residual digit remains in the ideal. -/
theorem ideal_le_span_of_adic_step (q c : R) (J : Ideal R)
    [IsAdicComplete (Ideal.span {q}) R]
    (hstep : ∀ x : J, ∃ a : R, ∃ b : J, (x : R) = c * a + q * (b : R)) :
    J ≤ Ideal.span {c} := by
  classical
  choose a b hstep using hstep
  intro x hx
  let u : ℕ → J := fun n => b^[n] ⟨x, hx⟩
  let s : ℕ → R := fun n => ∑ i ∈ Finset.range n, q ^ i * a (u i)
  let I : Ideal R := Ideal.span {q}
  have hu (n : ℕ) : (u n : R) = c * a (u n) + q * (u (n + 1) : R) := by
    have hn : u (n + 1) = b (u n) := by
      exact Function.iterate_succ_apply' b n ⟨x, hx⟩
    rw [hn]
    exact hstep (u n)
  have hs (n : ℕ) : s (n + 1) = s n + q ^ n * a (u n) :=
    Finset.sum_range_succ _ n
  have hres (n : ℕ) : x = c * s n + q ^ n * (u n : R) := by
    induction n with
    | zero => simp [s, u]
    | succ n ih =>
      rw [hs, ih, hu n, pow_succ]
      ring
  have hterm (m i : ℕ) (hmi : m ≤ i) : q ^ i * a (u i) ∈ I ^ m := by
    apply Ideal.pow_le_pow_right hmi
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) i)
  have hcauchy : ∀ {m n : ℕ}, m ≤ n →
      s m ≡ s n [SMOD (I ^ m • ⊤ : Submodule R R)] := by
    intro m n hmn
    change (Submodule.mkQ _) (s m) = (Submodule.mkQ _) (s n)
    dsimp only [s]
    rw [map_sum, map_sum]
    apply Finset.sum_subset (Finset.range_mono hmn)
    intro i _ hi
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    have hmi : m ≤ i := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hi)
    simpa only [smul_eq_mul, Ideal.mul_top] using hterm m i hmi
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (show IsPrecomplete I R from inferInstance) hcauchy
  have hzero : x - c * L = 0 := by
    apply IsHausdorff.haus (show IsHausdorff I R from inferInstance)
    intro n
    have hsum : s n - L ∈ I ^ n := by
      simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using hL n
    have hrem : q ^ n * (u n : R) ∈ I ^ n :=
      Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) n)
    have he : x - c * L = c * (s n - L) + q ^ n * (u n : R) := by
      rw [hres n]
      ring
    have hmem : x - c * L ∈ I ^ n := by
      rw [he]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hsum) hrem
    simpa only [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top] using hmem
  exact Ideal.mem_span_singleton.mpr ⟨L, sub_eq_zero.mp hzero⟩

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.AdicGeneration
