import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.SetTheory.Cardinal.Finite

/-! # Conjugate Labels -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ConjugateLabels.Construction

noncomputable section

/-!
A choice of exactly one label in each conjugate pair gives the two
rank-three block families. Both sides are indexed by one common Fin s;
the resulting total label map is a bijection, not a separation premise.
-/

variable {I : Type*} (c : Equiv.Perm I) (hc : Function.Involutive c)
  (chosen : Set I) (hchosen : ∀ i, i ∈ chosen ↔ c i ∉ chosen)

def conjugateLabelEquiv : chosen ⊕ chosen ≃ I :=
  Equiv.ofBijective (Sum.elim Subtype.val (fun i : chosen => c i.val)) (by
    constructor
    · intro x y he
      rcases x with x | x <;> rcases y with y | y
      · exact congrArg Sum.inl (Subtype.ext he)
      · change x.val = c y.val at he
        exact False.elim (((hchosen y.val).mp y.property) (he ▸ x.property))
      · change c x.val = y.val at he
        exact False.elim (((hchosen x.val).mp x.property) (he.symm ▸ y.property))
      · exact congrArg Sum.inr (Subtype.ext (c.injective he))
    · intro i
      by_cases hi : i ∈ chosen
      · exact ⟨Sum.inl ⟨i, hi⟩, rfl⟩
      · have hci : c i ∈ chosen := (hchosen (c i)).mpr (by rwa [hc i])
        exact ⟨Sum.inr ⟨c i, hci⟩, hc i⟩)

include c hc hchosen in
theorem chosen_card [Fintype I] (s : ℕ) (hcard : Fintype.card I = 2 * s) :
    Nat.card chosen = s := by
  have he := Nat.card_congr (conjugateLabelEquiv c hc chosen hchosen)
  have hi : Nat.card I = 2 * s := by simpa only [Nat.card_eq_fintype_card] using hcard
  rw [Nat.card_sum, hi] at he
  omega

def indexedConjugateLabels [Fintype I] (s : ℕ) (hcard : Fintype.card I = 2 * s) :
    (Fin s ⊕ Fin s) ≃ I := by
  classical
  let : Fintype chosen := Fintype.ofFinite _
  have hs : Fintype.card chosen = s := by
    simpa only [Nat.card_eq_fintype_card] using chosen_card c hc chosen hchosen s hcard
  let e := (Fintype.equivFinOfCardEq hs).symm
  exact (Equiv.sumCongr e e).trans (conjugateLabelEquiv c hc chosen hchosen)

theorem indexedConjugateLabels_opposite [Fintype I] (s : ℕ) (hcard : Fintype.card I = 2 * s)
    (i : Fin s) :
    indexedConjugateLabels c hc chosen hchosen s hcard (Sum.inr i) =
      c (indexedConjugateLabels c hc chosen hchosen s hcard (Sum.inl i)) := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ConjugateLabels.Construction
