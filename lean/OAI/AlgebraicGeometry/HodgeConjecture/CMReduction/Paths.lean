import OAI.AlgebraicGeometry.ComplexMultiplication.GaloisCMType
import OAI.AlgebraicGeometry.ComplexMultiplication.CMKnownResults

/-! # Paths -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Paths.CM.Construction

/-! CMReduction's exact PairSwitches input and elementary bookkeeping for switch paths.
Repeated active indices give an identity step and must not be counted as
two distinct changed tensor slots. -/

open scoped BigOperators

def PairSwitchesInput : Prop :=
  ∀ (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (p : ℕ)
    (v w : Fin p → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
      (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (_hbalance : ∀ τ : Gal(E/ℚ),
      (∑ i : Fin p, ComplexMultiplication.SignSwitch.CM.signValue ((v i).val τ)) =
        ∑ i : Fin p, ComplexMultiplication.SignSwitch.CM.signValue ((w i).val τ)),
    ∃ (n : ℕ)
      (path : Fin (n + 1) → Fin p → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
        (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)),
      path 0 = v ∧ path (Fin.last n) = w ∧
      (∀ k : Fin n, ComplexMultiplication.OddSignSwitch.CM.OddFourFactorSwitch (path k.castSucc) (path k.succ)) ∧
      (∀ (k : Fin (n + 1)) (i : Fin p), Nonempty
        (ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (path k i))))

theorem chain_of_indexed_path {α : Type*} (R : α → α → Prop)
    (n : ℕ) (path : Fin (n + 1) → α)
    (hstep : ∀ k : Fin n, R (path k.castSucc) (path k.succ)) :
    Relation.ReflTransGen R (path 0) (path (Fin.last n)) := by
  have h : ∀ k : Fin (n + 1), Relation.ReflTransGen R (path 0) (path k) :=
    Fin.induction (.refl) (fun k ih => ih.tail (hstep k))
  exact h (Fin.last n)

theorem oddSwitch_eq_or_distinct
    {α κ : Type*} {ν : α → α}
    {v w : κ → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern ν} (h : ComplexMultiplication.OddSignSwitch.CM.OddFourFactorSwitch v w) :
    v = w ∨ ∃ a b : κ, a ≠ b ∧
      (∀ i, i ≠ a → i ≠ b → w i = v i) ∧
      ∀ x, ComplexMultiplication.SignSwitch.CM.signValue ((v a).val x) + ComplexMultiplication.SignSwitch.CM.signValue ((v b).val x) =
        ComplexMultiplication.SignSwitch.CM.signValue ((w a).val x) + ComplexMultiplication.SignSwitch.CM.signValue ((w b).val x) := by
  classical
  obtain ⟨a, b, hrest, hsum⟩ := h
  by_cases hab : a = b
  · subst b
    left
    funext i
    by_cases hi : i = a
    · subst i
      apply Subtype.ext
      funext x
      have hx := hsum x
      cases hv : (v a).val x <;> cases hw : (w a).val x <;>
        simp_all [ComplexMultiplication.SignSwitch.CM.signValue]
    · exact (hrest i hi hi).symm
  · exact Or.inr ⟨a, b, hab, hrest, hsum⟩

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Paths.CM.Construction
