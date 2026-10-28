import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCodeBasic

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SparseCode

open scoped BigOperators

variable {C E R : Type*} [Fintype C] [Fintype E]
    [DecidableEq C] [DecidableEq E]

/-- Executable zero extension along an embedding. Finite summation avoids
any choice of an inverse for an index outside the image. -/
def zeroExtend (e : C ↪ E) (w : C → F3) : E → F3 :=
  fun z => ∑ c, if e c = z then w c else 0

/-- Keep selected columns. Its code is a zero-shortening, not a puncture. -/
def shorten (Q : CheckMatrix R E) (e : C ↪ E) : CheckMatrix R C :=
  fun r c => Q r (e c)

omit [Fintype E] in
@[simp] theorem zeroExtend_apply (e : C ↪ E) (w : C → F3) (c : C) :
    zeroExtend e w (e c) = w c := by
  simp [zeroExtend, e.injective.eq_iff]

omit [Fintype E] [DecidableEq C] in
theorem zeroExtend_eq_zero_of_not_mem (e : C ↪ E) (w : C → F3) (z : E)
    (hz : ∀ c, e c ≠ z) : zeroExtend e w z = 0 := by
  simp [zeroExtend, hz]

theorem support_zeroExtend (e : C ↪ E) (w : C → F3) :
    support (zeroExtend e w) = (support w).image e := by
  ext z
  by_cases hz : ∃ c, e c = z
  · obtain ⟨c, rfl⟩ := hz
    simp only [mem_support, zeroExtend_apply, Finset.mem_image]
    constructor
    · intro hw
      exact ⟨c, hw, rfl⟩
    · rintro ⟨a, ha, he⟩
      have hac : a = c := e.injective he
      simpa [hac] using ha
  · have he : ∀ c, e c ≠ z := by simpa only [not_exists] using hz
    simp only [mem_support, zeroExtend_eq_zero_of_not_mem e w z he, ne_eq,
      not_true_eq_false, Finset.mem_image]
    constructor
    · intro h
      exact h.elim
    · rintro ⟨c, _, hc⟩
      exact he c hc

@[simp] theorem weight_zeroExtend (e : C ↪ E) (w : C → F3) :
    weight (zeroExtend e w) = weight w := by
  simp only [weight, support_zeroExtend]
  exact Finset.card_image_of_injective _ e.injective

omit [Fintype E] in
theorem zeroExtend_ne_zero (e : C ↪ E) {w : C → F3} (hw : w ≠ 0) :
    zeroExtend e w ≠ 0 := by
  intro h
  apply hw
  funext c
  have := congrFun h (e c)
  simpa using this

omit [DecidableEq C] in
theorem check_zeroExtend (Q : CheckMatrix R E) (e : C ↪ E)
    (w : C → F3) (r : R) :
    check Q (zeroExtend e w) r = check (shorten Q e) w r := by
  simp only [check, zeroExtend, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp [shorten, mul_ite]

omit [DecidableEq C] in
theorem isCodeword_shorten_iff (Q : CheckMatrix R E) (e : C ↪ E) (w : C → F3) :
    IsCodeword (shorten Q e) w ↔ IsCodeword Q (zeroExtend e w) := by
  simp only [IsCodeword, check_zeroExtend]

theorem distance_shorten (Q : CheckMatrix R E) (e : C ↪ E) {d : ℕ}
    (hQ : HasDistance Q d) : HasDistance (shorten Q e) d := by
  intro w hw hw0
  simpa using hQ _ ((isCodeword_shorten_iff Q e w).mp hw) (zeroExtend_ne_zero e hw0)

/-- Preserve the absolute lower bound, using the original column count.
Only the later arithmetic wrapper replaces it by the smaller count. -/
theorem relativeDistance_shorten_absolute (Q : CheckMatrix R E) (e : C ↪ E)
    {δ : ℝ} (hQ : HasRelativeDistance Q δ) (w : C → F3)
    (hw : IsCodeword (shorten Q e) w) (hw0 : w ≠ 0) :
    δ * Fintype.card E ≤ (weight w : ℝ) := by
  simpa using hQ _ ((isCodeword_shorten_iff Q e w).mp hw) (zeroExtend_ne_zero e hw0)

theorem relativeDistance_shorten (Q : CheckMatrix R E) (e : C ↪ E)
    {δ : ℝ} (hδ : 0 ≤ δ) (hQ : HasRelativeDistance Q δ) :
    HasRelativeDistance (shorten Q e) δ := by
  intro w hw hw0
  have hc : (Fintype.card C : ℝ) ≤ Fintype.card E := by
    exact_mod_cast Fintype.card_le_of_injective e e.injective
  exact (mul_le_mul_of_nonneg_left hc hδ).trans
    (relativeDistance_shorten_absolute Q e hQ w hw hw0)

omit [DecidableEq C] in
theorem rowSupport_shorten_card_le (Q : CheckMatrix R E) (e : C ↪ E) (r : R) :
    (rowSupport (shorten Q e) r).card ≤ (rowSupport Q r).card := by
  have hs : (rowSupport (shorten Q e) r).image e ⊆ rowSupport Q r := by
    intro z hz
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hz
    simpa [rowSupport, mem_support, shorten] using hc
  calc
    _ = ((rowSupport (shorten Q e) r).image e).card :=
      (Finset.card_image_of_injective _ e.injective).symm
    _ ≤ _ := Finset.card_le_card hs

omit [Fintype C] [Fintype E] [DecidableEq C] [DecidableEq E] in
@[simp] theorem columnSupport_shorten [Fintype R]
    (Q : CheckMatrix R E) (e : C ↪ E) (c : C) :
    columnSupport (shorten Q e) c = columnSupport Q (e c) := rfl

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
