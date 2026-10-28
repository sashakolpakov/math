import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CompletionQuotientCoordinates

/-! # Completion Quotient Strictness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.CompletionQuotientStrictness

noncomputable section

/-! Every finite thickening of the completion along a non-nilpotent
element is a strict quotient of the original ring. -/

universe u
variable {R : Type u} [CommRing R]

theorem principal_completion_quotient_kernel_ne_bot (s : R) (hs : ¬ IsNilpotent s) (n : ℕ) :
    RingHom.ker ((Ideal.Quotient.mk
      (((Ideal.span {s}).map (algebraMap R (AdicCompletion (Ideal.span {s}) R))) ^ n)).comp
        (algebraMap R (AdicCompletion (Ideal.span {s}) R))) ≠ ⊥ := by
  let I : Ideal R := Ideal.span {s}
  let H := AdicCompletion I R
  let J : Ideal H := I.map (algebraMap R H)
  have hm : algebraMap R H (s ^ n) ∈ J ^ n := by
    rw [map_pow]
    apply Ideal.pow_mem_pow
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_singleton s))
  intro hker
  have hk : s ^ n ∈ RingHom.ker ((Ideal.Quotient.mk (J ^ n)).comp (algebraMap R H)) :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hm
  rw [hker] at hk
  exact hs ⟨n, hk⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.CompletionQuotientStrictness
