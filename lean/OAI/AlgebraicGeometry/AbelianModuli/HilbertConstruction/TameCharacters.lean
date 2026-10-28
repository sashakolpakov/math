import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CharacterBasis

/-! # Tame Characters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TameCharacters

noncomputable section

/-! Algebraically closed fields supply the character basis when the finite group order is invertible, including the exact ordered full-level group. -/
universe u v
variable (K : Type u) [Field K] [IsAlgClosed K] (G : Type v) [CommGroup G] [Fintype G]

theorem tameFiniteAbelian_hasEnoughRoots (hG : (Fintype.card G : K) ≠ 0) :
    HasEnoughRootsOfUnity K (Monoid.exponent G) := by
  have : NeZero (Monoid.exponent G : K) := ⟨by
    intro he
    obtain ⟨m, hm⟩ := Group.exponent_dvd_card (G := G)
    apply hG
    rw [hm, Nat.cast_mul, he, zero_mul]⟩
  infer_instance

def tameFiniteAbelianCharacterBasis (hG : (Fintype.card G : K) ≠ 0) :
    Module.Basis (G →* Kˣ) K (G → K) := by
  have := tameFiniteAbelian_hasEnoughRoots K G hG
  exact Finite.CharacterBasis.finiteAbelianCharacterBasis K G

@[simp]
theorem tameFiniteAbelianCharacterBasis_apply (hG : (Fintype.card G : K) ≠ 0)
    (χ : G →* Kˣ) (g : G) : tameFiniteAbelianCharacterBasis K G hG χ g = (χ g : K) := by
  have := tameFiniteAbelian_hasEnoughRoots K G hG
  exact Finite.CharacterBasis.finiteAbelianCharacterBasis_apply K G χ g

variable (g N : ℕ) [NeZero N]

omit [IsAlgClosed K] in
theorem fullLevelCharacter_order_nonzero (hN : (N : K) ≠ 0) :
    (Fintype.card (ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) : K) ≠ 0 := by
  simpa only [Fintype.card_ulift, Fintype.card_multiplicative, Fintype.card_fun,
    ZMod.card, Fintype.card_fin, Nat.cast_pow] using pow_ne_zero (2 * g) hN

def fullLevelCharacterBasis (hN : (N : K) ≠ 0) :
    Module.Basis ((ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) →* Kˣ) K
      ((ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) → K) :=
  tameFiniteAbelianCharacterBasis K _ (fullLevelCharacter_order_nonzero K g N hN)

theorem fullLevelCharacter_card (hN : (N : K) ≠ 0) :
    Nat.card ((ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) →* Kˣ) = N ^ (2 * g) := by
  have := tameFiniteAbelian_hasEnoughRoots K _ (fullLevelCharacter_order_nonzero K g N hN)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_ulift, Fintype.card_multiplicative,
    Fintype.card_fun, ZMod.card, Fintype.card_fin] using
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity
        (ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) K

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TameCharacters
