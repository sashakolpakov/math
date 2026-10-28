import OAI.AlgebraicGeometry.ComplexMultiplication.SignSwitch
import Mathlib.Algebra.BigOperators.Fin

/-! # Odd Sign Switch -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.OddSignSwitch.CM

/-!
# Switches through odd sign types

For a fixed-point-free involution, choose one representative of each pair
using an order. Every sign pattern on representatives extends uniquely to
an odd sign function. Consequently the finite switch reduction can be
carried out entirely within odd sign types. Each transition changes at most
two types and preserves their sum on the full set of embeddings.
This is a statement about types, not their geometric realization.
-/

variable {α κ : Type*}

/-- Boolean sign functions that reverse under the specified conjugation. -/
def OddSignPattern (ν : α → α) := {v : SignSwitch.CM.SignPattern α // ∀ x, v (ν x) = !v x}

/-- Reverse all signs, retaining oddness under conjugation. -/
def OddSignPattern.neg {ν : α → α} (v : OddSignPattern ν) : OddSignPattern ν :=
  ⟨fun x => !v.val x, fun x => congrArg Bool.not (v.property x)⟩

@[simp]
theorem OddSignPattern.neg_apply {ν : α → α} (v : OddSignPattern ν) (x : α) :
    v.neg.val x = !v.val x := rfl

section Representatives

variable [LinearOrder α] (ν : α → α)
variable (hν : Function.Involutive ν) (hne : ∀ x, ν x ≠ x)

/-- The smaller member of each conjugate pair. -/
abbrev ConjugateRepresentative := {x : α // x < ν x}

include hν hne in
theorem conjugate_lt_of_not_lt (x : α) (hx : ¬x < ν x) : ν x < ν (ν x) := by
  rw [hν x]
  exact lt_of_le_of_ne (le_of_not_gt hx) (hne x)

/-- Extend arbitrary representative signs to an odd type on all embeddings. -/
def extendOddSign (v : SignSwitch.CM.SignPattern (ConjugateRepresentative ν)) (x : α) : Bool :=
  if hx : x < ν x then v ⟨x, hx⟩
  else !v ⟨ν x, conjugate_lt_of_not_lt ν hν hne x hx⟩

theorem extendOddSign_odd (v : SignSwitch.CM.SignPattern (ConjugateRepresentative ν)) (x : α) :
    extendOddSign ν hν hne v (ν x) = !extendOddSign ν hν hne v x := by
  by_cases hx : x < ν x
  · have hn : ¬ν x < x := not_lt_of_gt hx
    simp only [extendOddSign, hν x, dite_eq_right hn, dite_eq_left hx]
  · have hy := conjugate_lt_of_not_lt ν hν hne x hx
    simp only [extendOddSign, dite_eq_left hy, dite_eq_right hx, Bool.not_not]

@[simp]
theorem extendOddSign_representative (v : SignSwitch.CM.SignPattern (ConjugateRepresentative ν))
    (x : ConjugateRepresentative ν) : extendOddSign ν hν hne v x = v x := by
  simp only [extendOddSign, dite_eq_left x.property]

@[simp]
theorem extendOddSign_restrict (v : OddSignPattern ν) :
    extendOddSign ν hν hne (fun x => v.val x) = v.val := by
  funext x
  by_cases hx : x < ν x
  · simp only [extendOddSign, dite_eq_left hx]
  · simp only [extendOddSign, dite_eq_right hx, v.property x, Bool.not_not]

/-- Odd types are exactly arbitrary signs on conjugate-pair representatives. -/
def oddSignEquiv : SignSwitch.CM.SignPattern (ConjugateRepresentative ν) ≃ OddSignPattern ν where
  toFun v := ⟨extendOddSign ν hν hne v, extendOddSign_odd ν hν hne v⟩
  invFun v := fun x => v.val x
  left_inv v := by funext x; exact extendOddSign_representative ν hν hne v x
  right_inv v := Subtype.ext (extendOddSign_restrict ν hν hne v)

end Representatives

/-- A transition between lists of odd types changes at most two entire
functions and preserves their pointwise sum on all embeddings. -/
def OddFourFactorSwitch {ν : α → α} (v w : κ → OddSignPattern ν) : Prop :=
  ∃ a b : κ, (∀ i, i ≠ a → i ≠ b → w i = v i) ∧
    ∀ x, SignSwitch.CM.signValue ((v a).val x) + SignSwitch.CM.signValue ((v b).val x) =
      SignSwitch.CM.signValue ((w a).val x) + SignSwitch.CM.signValue ((w b).val x)

/-- A finite chain whose every intermediate list consists of odd types. -/
abbrev OddSwitchChain {ν : α → α} :=
  Relation.ReflTransGen (OddFourFactorSwitch (κ := κ) (ν := ν))

variable [LinearOrder α] [DecidableEq κ] (ν : α → α)
variable (hν : Function.Involutive ν) (hne : ∀ x, ν x ≠ x)

theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.CoordinateSwitch.oddFourFactor {v w : SignSwitch.CM.SignFamily κ (ConjugateRepresentative ν)}
    (h : SignSwitch.CM.CoordinateSwitch v w) :
    OddFourFactorSwitch (fun i => oddSignEquiv ν hν hne (v i))
      (fun i => oddSignEquiv ν hν hne (w i)) := by
  obtain ⟨a, b, hrest, hsum⟩ := h.pair_identity
  refine ⟨a, b, ?_, ?_⟩
  · intro i hia hib
    exact congrArg (oddSignEquiv ν hν hne) (hrest i hia hib)
  · intro x
    change SignSwitch.CM.signValue (extendOddSign ν hν hne (v a) x) +
        SignSwitch.CM.signValue (extendOddSign ν hν hne (v b) x) =
      SignSwitch.CM.signValue (extendOddSign ν hν hne (w a) x) +
        SignSwitch.CM.signValue (extendOddSign ν hν hne (w b) x)
    by_cases hx : x < ν x
    · simpa only [extendOddSign, dite_eq_left hx] using hsum ⟨x, hx⟩
    · simp only [extendOddSign, dite_eq_right hx, SignSwitch.CM.signValue_not]
      have hs := hsum ⟨ν x, conjugate_lt_of_not_lt ν hν hne x hx⟩
      omega

/-- Lift the coordinate-switch chain without ever leaving the space of odd types. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.SwitchChain.oddSwitchChain {v w : SignSwitch.CM.SignFamily κ (ConjugateRepresentative ν)}
    (h : SignSwitch.CM.SwitchChain v w) :
    OddSwitchChain (fun i => oddSignEquiv ν hν hne (v i))
      (fun i => oddSignEquiv ν hν hne (w i)) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (hstep.oddFourFactor ν hν hne)

include hν hne in
/-- Equal sums of odd types can be joined by four-factor identities between odd types. -/
theorem oddSwitchChain_of_signSum_eq [Fintype α] [Fintype κ]
    (v w : κ → OddSignPattern ν)
    (hs : ∀ x, (∑ i, SignSwitch.CM.signValue ((v i).val x)) = ∑ i, SignSwitch.CM.signValue ((w i).val x)) :
    OddSwitchChain v w := by
  let v₀ : SignSwitch.CM.SignFamily κ (ConjugateRepresentative ν) := fun i x => (v i).val x
  let w₀ : SignSwitch.CM.SignFamily κ (ConjugateRepresentative ν) := fun i x => (w i).val x
  have h : SignSwitch.CM.SwitchChain v₀ w₀ := SignSwitch.CM.switchChain_of_signSum_eq (fun x => hs x)
  have hv : (fun i => oddSignEquiv ν hν hne (v₀ i)) = v := by
    funext i
    exact (oddSignEquiv ν hν hne).apply_symm_apply (v i)
  have hw : (fun i => oddSignEquiv ν hν hne (w₀ i)) = w := by
    funext i
    exact (oddSignEquiv ν hν hne).apply_symm_apply (w i)
  simpa only [hv, hw] using h.oddSwitchChain ν hν hne

include hν hne in
/-- Split a balanced list of `2p` odd signs into `p` identity slots and `p`
conjugate slots. The endpoint lists are joined through odd four-factor switches. -/
theorem balancedOddTuple_switchChain [Fintype α] (p : ℕ)
    (v : Fin (p + p) → OddSignPattern ν)
    (hs : ∀ x, (∑ i, SignSwitch.CM.signValue ((v i).val x)) = 0) :
    OddSwitchChain (fun i : Fin p => v (Fin.castAdd p i))
      (fun i : Fin p => (v (Fin.natAdd p i)).neg) := by
  apply oddSwitchChain_of_signSum_eq ν hν hne
  intro x
  have hx := hs x
  rw [Fin.sum_univ_add] at hx
  simp only [OddSignPattern.neg_apply, SignSwitch.CM.signValue_not, Finset.sum_neg_distrib]
  exact eq_neg_of_add_eq_zero_left hx

end OAI.AlgebraicGeometry.ComplexMultiplication.OddSignSwitch.CM
