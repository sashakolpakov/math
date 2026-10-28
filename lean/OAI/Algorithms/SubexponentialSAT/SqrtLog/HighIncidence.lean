import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Incidence

namespace OAI.Algorithms

/-! Integer high-incidence cutoff and disjoint branching on original coordinates. -/
namespace SubexponentialSAT.SqrtLog.HighIncidence

open scoped BigOperators

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

def totalScope (scope : E → Finset V) : ℕ := ∑ e, (scope e).card

def high (scope : E → Finset V) (cut : ℕ) : Finset V :=
  Finset.univ.filter fun v => cut < Incidence.degree scope v

def cutoff (scope : E → Finset V) (t : ℕ) : ℕ :=
  (totalScope scope * t) ⌈/⌉ Fintype.card V

omit [DecidableEq V] [DecidableEq E] in
theorem cutoff_eq (scope : E → Finset V) (t : ℕ) :
    cutoff scope t = (totalScope scope * t + Fintype.card V - 1) / Fintype.card V := rfl

omit [DecidableEq E] in
theorem high_mass_le (scope : E → Finset V) (cut : ℕ) :
    (high scope cut).card * (cut + 1) ≤ totalScope scope := by
  calc
    _ = ∑ _v ∈ high scope cut, (cut + 1) := by simp
    _ ≤ ∑ v ∈ high scope cut, Incidence.degree scope v := by
      apply Finset.sum_le_sum
      intro v hv
      exact Nat.succ_le_of_lt (Finset.mem_filter.mp hv).2
    _ ≤ ∑ v, Incidence.degree scope v :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; omega)
    _ = totalScope scope := Incidence.sum_degrees scope

omit [DecidableEq E] in
theorem high_card_mul_le (scope : E → Finset V) (cut t : ℕ)
    (hbudget : totalScope scope * t ≤ Fintype.card V * cut) :
    (high scope cut).card * t ≤ Fintype.card V := by
  have hm := high_mass_le scope cut
  have hmul := Nat.mul_le_mul_right t hm
  by_cases hc : cut = 0
  · simp only [hc, Nat.mul_zero] at hbudget
    have hh : (high scope cut).card ≤ totalScope scope := by nlinarith
    have := (Nat.mul_le_mul_right t hh).trans hbudget
    omega
  · have hp : 0 < cut := Nat.pos_of_ne_zero hc
    have hsmall : (high scope cut).card * t * cut ≤ Fintype.card V * cut := by
      nlinarith
    exact Nat.le_of_mul_le_mul_right hsmall hp

omit [DecidableEq E] in
theorem high_cutoff_card_mul_le (scope : E → Finset V) (t : ℕ)
    (hn : 0 < Fintype.card V) :
    (high scope (cutoff scope t)).card * t ≤ Fintype.card V := by
  apply high_card_mul_le
  exact (ceilDiv_le_iff_le_mul hn).mp le_rfl

omit [DecidableEq E] in
theorem high_cutoff_card_le_div (scope : E → Finset V) (t : ℕ)
    (hn : 0 < Fintype.card V) (ht : 0 < t) :
    (high scope (cutoff scope t)).card ≤ Fintype.card V / t := by
  exact (Nat.le_div_iff_mul_le ht).mpr (high_cutoff_card_mul_le scope t hn)

omit [DecidableEq E] in
theorem degree_not_high (scope : E → Finset V) (cut : ℕ) (v : V)
    (hv : v ∉ high scope cut) : Incidence.degree scope v ≤ cut := by
  simpa [high] using hv

def remainingScope (H : Finset V) (scope : E → Finset V) (e : E) :
    Finset {v : V // v ∉ H} := Finset.subtype (fun v => v ∉ H) (scope e)

omit [Fintype V] [DecidableEq E] in
@[simp] theorem degree_remainingScope (H : Finset V) (scope : E → Finset V)
    (v : {v : V // v ∉ H}) :
    Incidence.degree (remainingScope H scope) v = Incidence.degree scope v.val := by
  simp [Incidence.degree, Incidence.incident, remainingScope]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem card_remainingScope_le (H : Finset V) (scope : E → Finset V) (e : E) :
    (remainingScope H scope e).card ≤ (scope e).card := by
  rw [remainingScope, Finset.card_subtype]
  exact Finset.card_filter_le _ _

omit [DecidableEq E] in
theorem degree_remaining_high_le (scope : E → Finset V) (cut : ℕ)
    (v : {v : V // v ∉ high scope cut}) :
    Incidence.degree (remainingScope (high scope cut) scope) v ≤ cut := by
  rw [degree_remainingScope]
  exact degree_not_high scope cut v.val v.property

def glue (H : Finset V) (a : H → Bool) (b : {v : V // v ∉ H} → Bool) : V → Bool :=
  fun v => if hv : v ∈ H then a ⟨v, hv⟩ else b ⟨v, hv⟩

def assignmentEquiv (H : Finset V) :
    ((H → Bool) × ({v : V // v ∉ H} → Bool)) ≃ (V → Bool) where
  toFun ab := glue H ab.1 ab.2
  invFun x := (fun v => x v.val, fun v => x v.val)
  left_inv := by
    intro ab
    apply Prod.ext <;> funext v <;> simp [glue, v.property]
  right_inv := by
    intro x
    funext v
    simp [glue]

omit [Fintype V] in
theorem glue_injective (H : Finset V) :
    Function.Injective (fun ab : (H → Bool) × ({v : V // v ∉ H} → Bool) =>
      glue H ab.1 ab.2) := (assignmentEquiv H).injective

theorem sum_assignments_split {M : Type*} [AddCommMonoid M]
    (H : Finset V) (f : (V → Bool) → M) :
    ∑ x, f x = ∑ a : H → Bool, ∑ b : {v : V // v ∉ H} → Bool, f (glue H a b) := by
  calc
    _ = ∑ ab : (H → Bool) × ({v : V // v ∉ H} → Bool), f (glue H ab.1 ab.2) :=
      (Fintype.sum_equiv (assignmentEquiv H) _ _ (fun _ => rfl)).symm
    _ = _ := Fintype.sum_prod_type _

omit [Fintype V] in
theorem branch_count (H : Finset V) : Fintype.card (H → Bool) = 2 ^ H.card := by
  simp

theorem remaining_variable_count (H : Finset V) :
    Fintype.card {v : V // v ∉ H} = Fintype.card V - H.card := by
  calc
    _ = Fintype.card V - Fintype.card H := Fintype.card_subtype_compl (fun v => v ∈ H)
    _ = _ := by rw [Fintype.card_coe]

omit [DecidableEq E] in
theorem remaining_high_at_least_half (scope : E → Finset V) (t : ℕ)
    (hn : 0 < Fintype.card V) (ht : 2 ≤ t) :
    Fintype.card V ≤ 2 * Fintype.card {v : V // v ∉ high scope (cutoff scope t)} := by
  have hh := high_cutoff_card_mul_le scope t hn
  have htwo := Nat.mul_le_mul_left (high scope (cutoff scope t)).card ht
  rw [remaining_variable_count]
  omega

theorem count_predicate_split (H : Finset V) (P : (V → Bool) → Prop) [DecidablePred P] :
    (∑ x : V → Bool, if P x then 1 else 0 : ℕ) =
      ∑ a : H → Bool, ∑ b : {v : V // v ∉ H} → Bool, if P (glue H a b) then 1 else 0 :=
  sum_assignments_split H _

end SubexponentialSAT.SqrtLog.HighIncidence

end OAI.Algorithms
