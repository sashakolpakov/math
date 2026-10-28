import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FiniteFreeCompletion
import Mathlib.RingTheory.Henselian

/-! # Adic Transport -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.AdicTransport.Lifts

/-! Transport adic completeness between cofinal ideal powers and
construct the henselian local-ring structure from actual completeness. -/

universe u v

variable {R : Type u} [CommRing R] (I J : Ideal R)
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- If powers of J enter I and I is contained in J, the two completions
agree. A convergent subsequence and its limit are constructed explicitly. -/
theorem adic_complete_of_cofinal_powers [IsAdicComplete I M]
    (hIJ : I ≤ J) (e : ℕ) (hJI : J ^ e ≤ I) : IsAdicComplete J M := by
  let d := e + 1
  have hd : J ^ d ≤ I := (Ideal.pow_le_pow_right (Nat.le_succ e)).trans hJI
  have hp (n : ℕ) : J ^ (d * n) ≤ I ^ n := by
    rw [pow_mul]
    exact pow_le_pow_left' hd n
  have hs (n : ℕ) :
      J ^ (d * n) • (⊤ : Submodule R M) ≤ I ^ n • (⊤ : Submodule R M) :=
    Submodule.smul_mono (hp n) le_rfl
  have ht (n : ℕ) : I ^ n • (⊤ : Submodule R M) ≤ J ^ n • (⊤ : Submodule R M) :=
    Submodule.smul_mono (pow_le_pow_left' hIJ n) le_rfl
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    exact IsHausdorff.haus' (I := I) x (fun n => SModEq.mono (hs n) (hx (d * n)))
  · intro f hf
    have hc : ∀ {m n : ℕ}, m ≤ n →
        f (d * m) ≡ f (d * n) [SMOD I ^ m • (⊤ : Submodule R M)] := by
      intro m n hmn
      exact SModEq.mono (hs m) (hf (Nat.mul_le_mul_left d hmn))
    obtain ⟨l, hl⟩ := IsPrecomplete.prec' (I := I) (fun n => f (d * n)) hc
    refine ⟨l, fun n => ?_⟩
    have hn : n ≤ d * n := by
      exact (Nat.one_mul n).symm.trans_le (Nat.mul_le_mul_right n (Nat.le_add_left 1 e))
    exact (hf hn).trans (SModEq.mono (ht n) (hl n))

theorem complete_local_henselian (R : Type u) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] : HenselianLocalRing R where
  is_henselian f hf a ha hd :=
    HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal R) f hf a ha
      (hd.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)))

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.AdicTransport.Lifts
