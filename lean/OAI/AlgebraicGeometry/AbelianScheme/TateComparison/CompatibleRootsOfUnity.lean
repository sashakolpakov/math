import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Lean.Util.CollectAxioms

/-! # Compatible Roots Of Unity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CompatibleRootsOfUnity

noncomputable section

/-! Construct compatible primitive q-power roots over any algebraically
closed characteristic-zero field. These provide compatible value
coordinates for the finite-level Weil pairings. -/

variable (q : ℕ) [Fact q.Prime] (k : Type*) [Field k] [CharZero k] [IsAlgClosed k]

theorem primitiveQPowerRoot_lift (n : ℕ) (ζ : k) (hζ : IsPrimitiveRoot ζ (q ^ n)) :
    ∃ η : k, IsPrimitiveRoot η (q ^ (n + 1)) ∧ η ^ q = ζ := by
  have : NeZero (q : k) := ⟨Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero⟩
  have : NeZero (q ^ n) := ⟨pow_ne_zero n (Fact.out : q.Prime).ne_zero⟩
  obtain ⟨η, hη⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k (q ^ (n + 1))
  by_cases hn : n = 0
  · subst n
    have hz : ζ = 1 := IsPrimitiveRoot.one_right_iff.mp hζ
    refine ⟨η, hη, ?_⟩
    simpa only [Nat.zero_add, pow_one, hz] using hη.pow_eq_one
  · have hηq : IsPrimitiveRoot (η ^ q) (q ^ n) :=
      hη.pow (pow_pos (Fact.out : q.Prime).pos (n + 1))
        (by rw [pow_succ, Nat.mul_comm])
    obtain ⟨i, _, hi, hiζ⟩ := hηq.isPrimitiveRoot_iff.mp hζ
    have hiq : i.Coprime q := (Nat.coprime_pow_right_iff (Nat.pos_of_ne_zero hn) i q).mp hi
    refine ⟨η ^ i, hη.pow_of_coprime i (hiq.pow_right (n + 1)), ?_⟩
    exact (pow_right_comm η i q).trans hiζ

def compatiblePrimitiveRoots : ∀ n : ℕ, {ζ : k // IsPrimitiveRoot ζ (q ^ n)}
  | 0 => ⟨1, IsPrimitiveRoot.one⟩
  | n + 1 =>
    let h := primitiveQPowerRoot_lift q k n (compatiblePrimitiveRoots n).val (compatiblePrimitiveRoots n).property
    ⟨h.choose, h.choose_spec.1⟩

theorem compatiblePrimitiveRoots_pow (n : ℕ) :
    (CompatibleRootsOfUnity.compatiblePrimitiveRoots q k (n + 1)).val ^ q = (CompatibleRootsOfUnity.compatiblePrimitiveRoots q k n).val :=
  (primitiveQPowerRoot_lift q k n (CompatibleRootsOfUnity.compatiblePrimitiveRoots q k n).val
    (CompatibleRootsOfUnity.compatiblePrimitiveRoots q k n).property).choose_spec.2

theorem compatiblePrimitiveRoots_iterate (m r : ℕ) :
    (CompatibleRootsOfUnity.compatiblePrimitiveRoots q k (m + r)).val ^ (q ^ r) = (CompatibleRootsOfUnity.compatiblePrimitiveRoots q k m).val := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, Nat.mul_comm, pow_mul, ← Nat.add_assoc, compatiblePrimitiveRoots_pow]
    exact ih

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CompatibleRootsOfUnity
