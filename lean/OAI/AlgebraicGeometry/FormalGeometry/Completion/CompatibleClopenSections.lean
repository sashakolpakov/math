import OAI.AlgebraicGeometry.FormalGeometry.Completion.ClopenIdempotents

/-! # Compatible Clopen Sections -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.CompatibleClopenSections.Construction

noncomputable section

/-!
# Completion: compatible clopen idempotents on a sequence of schemes

The ring below consists of actual compatible global sections. Compatible
open-and-closed pieces give a canonical idempotent in this ring. If the
ring is local, all of those pieces must be empty or all must be the whole
scheme. No comparison with a completed base ring is postulated here.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (X : ℕ → Scheme.{u}) (d : ∀ n, X n ⟶ X (n + 1))

/-- The actual ring of global sections compatible under restriction along the sequence. -/
def compatibleGlobalSections : Subring (∀ n, Γ(X n, ⊤)) where
  carrier := {s | ∀ n, (d n).appTop (s (n + 1)) = s n}
  zero_mem' := by intro n; simp
  one_mem' := by intro n; simp
  add_mem' := by
    intro a b ha hb n
    change (d n).appTop (a (n + 1) + b (n + 1)) = a n + b n
    rw [map_add, ha n, hb n]
  mul_mem' := by
    intro a b ha hb n
    change (d n).appTop (a (n + 1) * b (n + 1)) = a n * b n
    rw [map_mul, ha n, hb n]
  neg_mem' := by
    intro a ha n
    change (d n).appTop (-a (n + 1)) = -a n
    rw [map_neg, ha n]

variable (U : ∀ n, (X n).Opens) (hU : ∀ n, IsClosed (U n : Set (X n)))
  (hcompat : ∀ n, (d n) ⁻¹ᵁ U (n + 1) = U n)

/-- Compatible clopen pieces define an idempotent in the actual ring of compatible sections. -/
def compatibleClopenIndicator : compatibleGlobalSections X d :=
  ⟨fun n => ClopenIdempotents.Construction.clopenIndicator (U n) (hU n), fun n => by
    simpa only [hcompat n] using ClopenIdempotents.Construction.clopenIndicator_pullback (d n) (U (n + 1)) (hU (n + 1))⟩

theorem compatibleClopenIndicator_isIdempotent :
    IsIdempotentElem (compatibleClopenIndicator X d U hU hcompat) := by
  apply Subtype.ext
  funext n
  exact (ClopenIdempotents.Construction.clopenIndicator_isIdempotent (U n) (hU n)).eq

include hU hcompat

/-- Locality of the actual compatible-section ring rules out a nontrivial compatible clopen family. -/
theorem compatibleClopen_trivial_of_local_globalSections
    [IsLocalRing (compatibleGlobalSections X d)] :
    (∀ n, U n = ⊥) ∨ (∀ n, U n = ⊤) := by
  rcases IntegralIdempotents.Construction.local_idempotent_eq_zero_or_one (compatibleGlobalSections X d)
    (compatibleClopenIndicator_isIdempotent X d U hU hcompat) with h | h
  · left
    intro n
    apply (ClopenIdempotents.Construction.clopenIndicator_eq_zero_iff (U n) (hU n)).mp
    exact congrArg (fun s : compatibleGlobalSections X d => s.val n) h
  · right
    intro n
    apply (ClopenIdempotents.Construction.clopenIndicator_eq_one_iff (U n) (hU n)).mp
    exact congrArg (fun s : compatibleGlobalSections X d => s.val n) h

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.CompatibleClopenSections.Construction
