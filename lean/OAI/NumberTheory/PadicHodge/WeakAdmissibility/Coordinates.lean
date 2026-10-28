import OAI.NumberTheory.PadicHodge.WeakAdmissibility.RestrictedCoefficients

/-! # Coordinates -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.Coordinates

noncomputable section

/-! Canonical coordinates and coefficientwise equality in a completed direct sum. -/

open AdicCompletion OAI.NumberTheory.PadicHodge.WeakAdmissibility.RestrictedCoefficients OAI.NumberTheory.PadicHodge.WeakAdmissibility.RestrictedCoefficients.Series
variable {R : Type*} [CommRing R] (q : R) [IsAdicComplete (Ideal.span {q}) R]

def coordinate (i : ℕ) : AdicCompletion (Ideal.span {q}) (ℕ →₀ R) →ₗ[R] R :=
  (AdicCompletion.ofLinearEquiv (Ideal.span {q}) R).symm.toLinearMap.comp
    ((AdicCompletion.map (Ideal.span {q}) (Finsupp.lapply i)).restrictScalars R)

theorem coordinate_of (i : ℕ) (f : ℕ →₀ R) :
    coordinate q i (AdicCompletion.of (Ideal.span {q}) (ℕ →₀ R) f) = f i := by
  change (AdicCompletion.ofLinearEquiv (Ideal.span {q}) R).symm
    (AdicCompletion.map (Ideal.span {q}) (Finsupp.lapply i)
      (AdicCompletion.of (Ideal.span {q}) (ℕ →₀ R) f)) = _
  rw [AdicCompletion.map_of, AdicCompletion.ofLinearEquiv_symm_of]
  rfl

theorem coordinate_approx (x : AdicCompletion (Ideal.span {q}) (ℕ →₀ R)) (r : ℕ) (f : ℕ →₀ R)
    (hf : AdicCompletion.eval (Ideal.span {q}) (ℕ →₀ R) r x = Submodule.mkQ _ f) (i : ℕ) :
    q ^ r ∣ coordinate q i x - f i := by
  have hm : x - AdicCompletion.of (Ideal.span {q}) (ℕ →₀ R) f ∈
      (Ideal.span {q}) ^ r • (⊤ : Submodule R (AdicCompletion (Ideal.span {q}) (ℕ →₀ R))) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _), LinearMap.mem_ker]
    rw [map_sub, hf, AdicCompletion.eval_of, sub_self]
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at hm
  obtain ⟨z, _, hz⟩ := hm
  have he := congrArg (coordinate q i) hz
  simp only [map_smul, map_sub, coordinate_of, smul_eq_mul] at he
  exact ⟨coordinate q i z, he.symm⟩

theorem coordinate_mk_approx (c : AdicCauchySequence (Ideal.span {q}) (ℕ →₀ R)) (r i : ℕ) :
    q ^ r ∣ coordinate q i (AdicCompletion.mk (Ideal.span {q}) (ℕ →₀ R) c) - c r i :=
  coordinate_approx q _ r (c r) rfl i

theorem coordinates_restricted (x : AdicCompletion (Ideal.span {q}) (ℕ →₀ R)) :
    RestrictedCoefficients.IsRestricted q (fun i => coordinate q i x) := by
  obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective (Ideal.span {q}) (ℕ →₀ R) x
  intro r
  refine ⟨(c r).support.sup id + 1, fun n hn => ?_⟩
  have hnmem : n ∉ (c r).support := by
    intro hmem
    have hnle : n ≤ (c r).support.sup id := Finset.le_sup (f := id) hmem
    omega
  have hz : c r n = 0 := Finsupp.notMem_support_iff.mp hnmem
  simpa only [hz, sub_zero] using coordinate_mk_approx q c r n

theorem coordinates_injective : Function.Injective
    (fun x : AdicCompletion (Ideal.span {q}) (ℕ →₀ R) => fun i => coordinate q i x) := by
  intro x y hxy
  obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective (Ideal.span {q}) (ℕ →₀ R) x
  obtain ⟨d, rfl⟩ := AdicCompletion.mk_surjective (Ideal.span {q}) (ℕ →₀ R) y
  apply RestrictedCoefficients.Series.completion_eq_of_coefficients q c d
    (fun i => coordinate q i (AdicCompletion.mk (Ideal.span {q}) (ℕ →₀ R) c))
    (coordinate_mk_approx q c)
  intro r i
  exact (congrArg (fun a : R => q ^ r ∣ a - d r i) (congrFun hxy i)).mpr
    (coordinate_mk_approx q d r i)

theorem reconstructed_coordinates (x : AdicCompletion (Ideal.span {q}) (ℕ →₀ R)) :
    RestrictedCoefficients.Series.restrictedSeries q (fun i => coordinate q i x) (coordinates_restricted q x) = x := by
  obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective (Ideal.span {q}) (ℕ →₀ R) x
  apply RestrictedCoefficients.Series.completion_eq_of_coefficients q _ c _
  · exact RestrictedCoefficients.Series.truncatedCauchy_approx q _ _
  · exact coordinate_mk_approx q c

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.Coordinates
