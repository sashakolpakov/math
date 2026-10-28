import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.TruncationTransition

/-! # Prime Power Transition Kernel -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrimePowerTransitionKernel

/-! The actual prime-power transition has the expected prime-power kernel in its source ring. -/

universe u

variable (p : ℕ) (A : Type u) [CommRing A] (n m : ℕ) (hnm : n ≤ m)

theorem kernel : RingHom.ker (PD.TruncationTransition.map A (Ideal.span {(p : A)}) n m hnm) =
    (Ideal.span {(p : A ⧸ (Ideal.span {(p : A)}) ^ (m + 1))}) ^ (n + 1) := by
  have h := Ideal.ker_quotient_lift (I := (Ideal.span {(p : A)}) ^ (m + 1))
    (Ideal.Quotient.mk ((Ideal.span {(p : A)}) ^ (n + 1))) (fun a ha =>
      Ideal.Quotient.eq_zero_iff_mem.mpr ((Ideal.pow_le_pow_right (Nat.add_le_add_right hnm 1)) ha))
  refine h.trans ?_
  rw [Ideal.mk_ker, Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast]

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrimePowerTransitionKernel
