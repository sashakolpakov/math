import Mathlib

/-! # Restricted Coefficients -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.WeakAdmissibility.RestrictedCoefficients

/-! Restricted coefficient sequences extracted from completed direct sums. -/

open AdicCompletion
variable {R : Type*} [CommRing R] (q : R)

/-- The coefficients tend to zero in the q-adic topology. -/
def IsRestricted (a : ℕ → R) : Prop := ∀ r : ℕ, ∃ N : ℕ, ∀ n ≥ N, q ^ r ∣ a n

theorem coordinate_dvd_of_mem (r : ℕ) (f : ℕ →₀ R)
    (hf : f ∈ (Ideal.span {q}) ^ r • (⊤ : Submodule R (ℕ →₀ R))) (i : ℕ) : q ^ r ∣ f i := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at hf
  obtain ⟨g, _, hg⟩ := hf
  exact ⟨g i, (DFunLike.congr_fun hg i).symm⟩

def coordinateCauchy (c : AdicCauchySequence (Ideal.span {q}) (ℕ →₀ R)) (i : ℕ) :
    AdicCauchySequence (Ideal.span {q}) R :=
  ⟨fun n => c n i, by
    intro m n hmn
    have hm := c.property hmn
    rw [SModEq.sub_mem] at hm
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact coordinate_dvd_of_mem q m (c m - c n) hm i⟩

variable [IsPrecomplete (Ideal.span {q}) R]

theorem cauchy_coefficients (c : AdicCauchySequence (Ideal.span {q}) (ℕ →₀ R)) :
    ∃ a : ℕ → R, (∀ r i : ℕ, q ^ r ∣ a i - c r i) ∧ IsRestricted q a := by
  have hlim (i : ℕ) : ∃ a : R, ∀ r : ℕ,
      c r i ≡ a [SMOD (Ideal.span {q}) ^ r • (⊤ : Submodule R R)] :=
    IsPrecomplete.prec (show IsPrecomplete (Ideal.span {q}) R from inferInstance)
      (coordinateCauchy q c i).property
  choose a ha using hlim
  have happrox (r i : ℕ) : q ^ r ∣ a i - c r i := by
    have he := (ha i r).symm
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at he
  refine ⟨a, happrox, ?_⟩
  intro r
  refine ⟨(c r).support.sup id + 1, fun n hn => ?_⟩
  have hnmem : n ∉ (c r).support := by
    intro hmem
    have hnle : n ≤ (c r).support.sup id := Finset.le_sup (f := id) hmem
    omega
  have hz : c r n = 0 := Finsupp.notMem_support_iff.mp hnmem
  simpa only [hz, sub_zero] using happrox r n

theorem completed_coefficients (x : AdicCompletion (Ideal.span {q}) (ℕ →₀ R)) :
    ∃ (c : AdicCauchySequence (Ideal.span {q}) (ℕ →₀ R)) (a : ℕ → R),
      AdicCompletion.mk (Ideal.span {q}) (ℕ →₀ R) c = x ∧
      (∀ r i : ℕ, q ^ r ∣ a i - c r i) ∧ IsRestricted q a := by
  obtain ⟨c, hc⟩ := AdicCompletion.mk_surjective (Ideal.span {q}) (ℕ →₀ R) x
  obtain ⟨a, ha, hnull⟩ := cauchy_coefficients q c
  exact ⟨c, a, hc, ha, hnull⟩

end NumberTheory.PadicHodge.WeakAdmissibility.RestrictedCoefficients

namespace NumberTheory.PadicHodge.WeakAdmissibility.RestrictedCoefficients.Series

/-! Construction of completed direct sums from restricted coefficient sequences. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.RestrictedCoefficients AdicCompletion
variable {R : Type*} [CommRing R] (q : R)

theorem mem_power_smul_finsupp (r : ℕ) (f : ℕ →₀ R) :
    f ∈ (Ideal.span {q}) ^ r • (⊤ : Submodule R (ℕ →₀ R)) ↔ ∀ i, q ^ r ∣ f i := by
  classical
  refine ⟨fun hf i => coordinate_dvd_of_mem q r f hf i, fun hf => ?_⟩
  let g : ℕ →₀ R := Finsupp.onFinset f.support
    (fun i => if i ∈ f.support then (hf i).choose else 0) (by
      intro i hi
      by_contra h
      simp only [h, ↓reduceIte] at hi
      exact hi rfl)
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  refine ⟨g, Submodule.mem_top, ?_⟩
  ext i
  change q ^ r * g i = f i
  simp only [g, Finsupp.onFinset_apply]
  split_ifs with hi
  · exact (hf i).choose_spec.symm
  · simp only [mul_zero, (Finsupp.notMem_support_iff.mp hi)]

def truncate (N : ℕ) (a : ℕ → R) : ℕ →₀ R :=
  Finsupp.onFinset (Finset.range N) (fun i => if i < N then a i else 0) (by
    intro i hi
    rw [Finset.mem_range]
    by_contra h
    simp only [h, ↓reduceIte] at hi
    exact hi rfl)

theorem truncate_apply (N : ℕ) (a : ℕ → R) (i : ℕ) :
    truncate N a i = if i < N then a i else 0 := rfl

def cutoff (a : ℕ → R) (ha : IsRestricted q a) (r : ℕ) : ℕ :=
  (Finset.range (r + 1)).sup (fun n => (ha n).choose)

theorem cutoff_mono (a : ℕ → R) (ha : IsRestricted q a) : Monotone (cutoff q a ha) := by
  intro m n hmn
  apply Finset.sup_mono
  exact Finset.range_mono (Nat.add_le_add_right hmn 1)

theorem cutoff_bound (a : ℕ → R) (ha : IsRestricted q a) (r i : ℕ)
    (hi : cutoff q a ha r ≤ i) : q ^ r ∣ a i := by
  apply (ha r).choose_spec
  apply le_trans ?_ hi
  exact Finset.le_sup (f := fun n => (ha n).choose) (Finset.mem_range.mpr (Nat.lt_succ_self r))

def truncatedCauchy (a : ℕ → R) (ha : IsRestricted q a) :
    AdicCauchySequence (Ideal.span {q}) (ℕ →₀ R) :=
  ⟨fun r => truncate (cutoff q a ha r) a, by
    intro m n hmn
    rw [SModEq.sub_mem, mem_power_smul_finsupp]
    intro i
    change q ^ m ∣ truncate (cutoff q a ha m) a i - truncate (cutoff q a ha n) a i
    rw [truncate_apply, truncate_apply]
    by_cases him : i < cutoff q a ha m
    · have hin := lt_of_lt_of_le him (cutoff_mono q a ha hmn)
      simp only [him, hin, ↓reduceIte, sub_self, dvd_zero]
    · by_cases hin : i < cutoff q a ha n
      · simp only [him, hin, ↓reduceIte, zero_sub]
        exact dvd_neg.mpr (cutoff_bound q a ha m i (Nat.le_of_not_gt him))
      · simp only [him, hin, ↓reduceIte, sub_self, dvd_zero]⟩

def restrictedSeries (a : ℕ → R) (ha : IsRestricted q a) :
    AdicCompletion (Ideal.span {q}) (ℕ →₀ R) :=
  AdicCompletion.mk (Ideal.span {q}) (ℕ →₀ R) (truncatedCauchy q a ha)

theorem truncatedCauchy_approx (a : ℕ → R) (ha : IsRestricted q a) (r i : ℕ) :
    q ^ r ∣ a i - truncatedCauchy q a ha r i := by
  change q ^ r ∣ a i - truncate (cutoff q a ha r) a i
  rw [truncate_apply]
  split_ifs with hi
  · simp only [sub_self, dvd_zero]
  · rw [sub_zero]
    exact cutoff_bound q a ha r i (Nat.le_of_not_gt hi)

theorem completion_eq_of_coefficients
    (c d : AdicCauchySequence (Ideal.span {q}) (ℕ →₀ R)) (a : ℕ → R)
    (hc : ∀ r i, q ^ r ∣ a i - c r i) (hd : ∀ r i, q ^ r ∣ a i - d r i) :
    AdicCompletion.mk (Ideal.span {q}) (ℕ →₀ R) c =
      AdicCompletion.mk (Ideal.span {q}) (ℕ →₀ R) d := by
  apply Subtype.ext
  funext r
  change Submodule.Quotient.mk (c r) = Submodule.Quotient.mk (d r)
  apply (Submodule.Quotient.eq _).mpr
  rw [mem_power_smul_finsupp]
  intro i
  change q ^ r ∣ c r i - d r i
  have h := dvd_sub (hd r i) (hc r i)
  simpa only [sub_sub_sub_cancel_left] using h

end NumberTheory.PadicHodge.WeakAdmissibility.RestrictedCoefficients.Series

end

end OAI
