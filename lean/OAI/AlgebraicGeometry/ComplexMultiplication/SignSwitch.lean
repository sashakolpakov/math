import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Logic.Relation
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! # Sign Switch -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM

/-!
# The finite sign-switch reduction for CM tensors

This is the combinatorial step in Section 2 of
`/docs/hodge_cm_claimed_result.tex`. A coordinate indexes a conjugate
pair of embeddings; `true` and `false` denote the two possible Hodge signs
on the chosen representative. The sign on its conjugate is forced to be
the opposite one.

The results in this file concern sign patterns only. In particular, they
do not assume or assert that a switch is realized by an algebraic cycle.
-/

variable {ι κ : Type*}

/-- A CM sign pattern on representatives of conjugate embedding pairs. -/
abbrev SignPattern (ι : Type*) := ι → Bool

/-- A finite family of weight-one sign patterns, indexed by tensor slots. -/
abbrev SignFamily (κ ι : Type*) := κ → SignPattern ι

/-- The integer signs used in the manuscript. -/
def signValue (b : Bool) : ℤ := if b then 1 else -1

@[simp]
theorem signValue_not (b : Bool) : signValue (!b) = -signValue b := by
  cases b <;> rfl

/-- Recover the odd sign function on both members of each conjugate pair. -/
def oddExtension (v : SignPattern ι) (e : ι × Bool) : ℤ :=
  if e.2 then -signValue (v e.1) else signValue (v e.1)

/-- The extension changes sign under the conjugation involution. -/
theorem oddExtension_conjugate (v : SignPattern ι) (e : ι × Bool) :
    oddExtension v (e.1, !e.2) = -oddExtension v e := by
  rcases e with ⟨t, b⟩
  cases b <;> simp [oddExtension]

/-- Reindex the slots at a single embedding coordinate. -/
def permuteAt [DecidableEq ι] (v : SignFamily κ ι) (t : ι)
    (π : Equiv.Perm κ) : SignFamily κ ι :=
  fun i u => if u = t then v (π i) u else v i u

/-- Exchange two slot signs at one coordinate, leaving all other entries fixed. -/
def CoordinateSwitch [DecidableEq ι] [DecidableEq κ]
    (v w : SignFamily κ ι) : Prop :=
  ∃ (t : ι) (a b : κ), w = permuteAt v t (Equiv.swap a b)

/-- A finite sequence of coordinate switches, including the empty sequence. -/
abbrev SwitchChain [DecidableEq ι] [DecidableEq κ] :=
  Relation.ReflTransGen (CoordinateSwitch (ι := ι) (κ := κ))

/-- Each coordinate exchange is a four-factor identity: only two whole sign
patterns change, and their pointwise sum is preserved. -/
theorem CoordinateSwitch.pair_identity [DecidableEq ι] [DecidableEq κ]
    {v w : SignFamily κ ι} (h : CoordinateSwitch v w) :
    ∃ a b : κ,
      (∀ i, i ≠ a → i ≠ b → w i = v i) ∧
      ∀ t, signValue (v a t) + signValue (v b t) =
        signValue (w a t) + signValue (w b t) := by
  obtain ⟨u, a, b, rfl⟩ := h
  refine ⟨a, b, ?_, ?_⟩
  · intro i hia hib
    funext t
    simp [permuteAt, Equiv.swap_apply_of_ne_of_ne hia hib]
  · intro t
    by_cases ht : t = u
    · simp [permuteAt, ht, add_comm]
    · simp [permuteAt, ht]

variable [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The number of slots carrying a specified sign at a coordinate. -/
def signCount (v : SignFamily κ ι) (t : ι) (b : Bool) : ℕ :=
  Fintype.card {i : κ // v i t = b}

/-- Balance means equality of the two sign multisets at each coordinate. -/
def Balanced (v w : SignFamily κ ι) : Prop :=
  ∀ (t : ι) (b : Bool), signCount v t b = signCount w t b

/-- The signed Hodge weight at an embedding coordinate. -/
def signSum (v : SignFamily κ ι) (t : ι) : ℤ :=
  ∑ i, signValue (v i t)

omit [DecidableEq ι] [DecidableEq κ] in
theorem signCount_true_add_false (v : SignFamily κ ι) (t : ι) :
    signCount v t true + signCount v t false = Fintype.card κ := by
  simpa [signCount, Fintype.card_subtype, Bool.not_eq_true] using
    (Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => v i t = true))

omit [DecidableEq ι] [DecidableEq κ] in
theorem signSum_eq_counts (v : SignFamily κ ι) (t : ι) :
    signSum v t = (signCount v t true : ℤ) - (signCount v t false : ℤ) := by
  classical
  simp [signSum, signValue, Finset.sum_ite, signCount, Fintype.card_subtype,
    Bool.not_eq_true, sub_eq_add_neg]

omit [DecidableEq ι] [DecidableEq κ] in
/-- For equally many tensor slots, equality of signed sums is precisely balance. -/
theorem balanced_iff_signSum_eq (v w : SignFamily κ ι) :
    Balanced v w ↔ ∀ t, signSum v t = signSum w t := by
  constructor
  · intro h t
    simp only [signSum_eq_counts, h t true, h t false]
  · intro h t b
    have hv := signCount_true_add_false v t
    have hw := signCount_true_add_false w t
    have hs := h t
    rw [signSum_eq_counts, signSum_eq_counts] at hs
    cases b <;> omega

omit [DecidableEq κ] in
theorem signSum_permuteAt (v : SignFamily κ ι) (t u : ι) (π : Equiv.Perm κ) :
    signSum (permuteAt v t π) u = signSum v u := by
  by_cases hu : u = t
  · simpa [signSum, permuteAt, hu] using
      Equiv.sum_comp π (fun i => signValue (v i t))
  · simp [signSum, permuteAt, hu]

theorem CoordinateSwitch.signSum_eq {v w : SignFamily κ ι}
    (h : CoordinateSwitch v w) (t : ι) : signSum v t = signSum w t := by
  obtain ⟨u, a, b, rfl⟩ := h
  exact (signSum_permuteAt v u t (Equiv.swap a b)).symm

theorem SwitchChain.signSum_eq {v w : SignFamily κ ι}
    (h : SwitchChain v w) (t : ι) : signSum v t = signSum w t := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (hstep.signSum_eq t)

theorem switchChain_permuteAt (v : SignFamily κ ι) (t : ι) (π : Equiv.Perm κ) :
    SwitchChain v (permuteAt v t π) := by
  induction π using Equiv.Perm.swap_induction_on' with
  | one =>
    have h : permuteAt v t 1 = v := by
      funext i u
      simp [permuteAt]
    rw [h]
  | mul_swap π a b _ ih =>
    have h : permuteAt v t (π * Equiv.swap a b) =
        permuteAt (permuteAt v t π) t (Equiv.swap a b) := by
      funext i u
      by_cases hu : u = t <;> simp [permuteAt, hu, Equiv.Perm.mul_apply]
    rw [h]
    exact ih.tail ⟨t, a, b, rfl⟩

/-- Reindex any specified finite set of coordinates independently. -/
def permuteOn (v : SignFamily κ ι) (s : Finset ι)
    (π : ι → Equiv.Perm κ) : SignFamily κ ι :=
  fun i t => if t ∈ s then v (π t i) t else v i t

theorem switchChain_permuteOn (v : SignFamily κ ι) (s : Finset ι)
    (π : ι → Equiv.Perm κ) : SwitchChain v (permuteOn v s π) := by
  induction s using Finset.induction_on with
  | empty =>
    have h : permuteOn v ∅ π = v := by
      funext i t
      simp [permuteOn]
    rw [h]
  | @insert t s ht ih =>
    have h : permuteOn v (insert t s) π =
        permuteAt (permuteOn v s π) t (π t) := by
      funext i u
      by_cases hu : u = t
      · subst u
        simp [permuteOn, permuteAt, ht]
      · simp [permuteOn, permuteAt, hu]
    rw [h]
    exact ih.trans (switchChain_permuteAt _ _ _)

omit [DecidableEq ι] [DecidableEq κ] in
/-- Equal coordinate multisets can be matched by coordinatewise slot permutations. -/
theorem Balanced.exists_permutations {v w : SignFamily κ ι} (h : Balanced v w) :
    ∃ π : ι → Equiv.Perm κ, ∀ (i : κ) (t : ι), v (π t i) t = w i t := by
  let e (t : ι) (b : Bool) : {i : κ // w i t = b} ≃ {i : κ // v i t = b} :=
    Fintype.equivOfCardEq (h t b).symm
  exact ⟨fun t => Equiv.ofFiberEquiv (e t),
    fun i t => Equiv.ofFiberEquiv_map (e t) i⟩

/-- The finite combinatorial reduction in the manuscript: every balanced pair of
families is connected by swaps of two slots at one embedding coordinate. -/
theorem Balanced.switchChain [Fintype ι] {v w : SignFamily κ ι} (h : Balanced v w) :
    SwitchChain v w := by
  obtain ⟨π, hπ⟩ := h.exists_permutations
  have heq : permuteOn v Finset.univ π = w := by
    funext i t
    simpa [permuteOn] using hπ i t
  rw [← heq]
  exact switchChain_permuteOn v Finset.univ π

/-- The signed-sum formulation used for the CM tensor reduction. -/
theorem switchChain_of_signSum_eq [Fintype ι] {v w : SignFamily κ ι}
    (h : ∀ t, signSum v t = signSum w t) : SwitchChain v w :=
  ((balanced_iff_signSum_eq v w).mpr h).switchChain

/-- The reduction is exact: switches connect precisely the balanced sign families. -/
theorem switchChain_iff_balanced [Fintype ι] (v w : SignFamily κ ι) :
    SwitchChain v w ↔ Balanced v w := by
  constructor
  · intro h
    exact (balanced_iff_signSum_eq v w).mpr h.signSum_eq
  · exact Balanced.switchChain

end OAI.AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM
