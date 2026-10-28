import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ElementaryModules
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Elementary Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ElementaryUniqueness.Construction

noncomputable section

/-!
The abstract additive group determines the dominant rank-three q-power
exponents. Counts of q^k-torsion recover the sums of min(a_i,k), so a
prescribed subgroup isomorphism type determines the Smith lattice type.
-/

open scoped BigOperators

def killedPointEquiv {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (n : ℕ) : {x : G // n • x = 0} ≃ {y : H // n • y = 0} :=
  e.toEquiv.subtypeEquiv (fun x => by
    change n • x = 0 ↔ n • e x = 0
    rw [← map_nsmul e, ← map_zero e, e.injective.eq_iff])

theorem card_zmod_pow_killed (q a k : ℕ) [NeZero q] :
    Nat.card {x : ZMod (q ^ a) // (q ^ k) • x = 0} = q ^ min a k := by
  change Nat.card (nsmulAddMonoidHom (q ^ k) : ZMod (q ^ a) →+ ZMod (q ^ a)).ker = _
  rw [IsAddCyclic.card_nsmulAddMonoidHom_ker, Nat.card_eq_fintype_card, ZMod.card]
  rcases le_total a k with hak | hka
  · rw [min_eq_left hak, Nat.gcd_eq_left (pow_dvd_pow q hak)]
  · rw [min_eq_right hka, Nat.gcd_eq_right (pow_dvd_pow q hka)]

def elementaryKilledPiEquiv {d : ℕ} (q k : ℕ) (a : Fin d → ℕ) :
    {x : (∀ i, ZMod (q ^ a i)) // (q ^ k) • x = 0} ≃
      (∀ i, {x : ZMod (q ^ a i) // (q ^ k) • x = 0}) where
  toFun x i := ⟨x.val i, congrFun x.property i⟩
  invFun x := ⟨fun i => (x i).val, funext (fun i => (x i).property)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_elementary_killed {d : ℕ} (q k : ℕ) [NeZero q] (a : Fin d → ℕ) :
    Nat.card {x : (∀ i, ZMod (q ^ a i)) // (q ^ k) • x = 0} =
      q ^ (∑ i, min (a i) k) := by
  rw [Nat.card_congr (elementaryKilledPiEquiv q k a), Nat.card_pi]
  simp_rw [card_zmod_pow_killed]
  simp [Finset.prod_pow_eq_pow_sum]

theorem elementary_min_sums_eq {d : ℕ} (q : ℕ) (hq : q.Prime)
    (a b : Fin d → ℕ) (e : (∀ i, ZMod (q ^ a i)) ≃+ (∀ i, ZMod (q ^ b i))) (k : ℕ) :
    (∑ i, min (a i) k) = ∑ i, min (b i) k := by
  let : NeZero q := ⟨hq.ne_zero⟩
  have he := Nat.card_congr (killedPointEquiv e (q ^ k))
  rw [card_elementary_killed, card_elementary_killed] at he
  exact (Nat.pow_right_injective hq.two_le) he

theorem rankThree_eq_of_min_sums
    (a b : Fin 3 → ℕ) (ha : Antitone a) (hb : Antitone b)
    (hmin : ∀ k, (∑ i, min (a i) k) = ∑ i, min (b i) k) : a = b := by
  have ha10 : a 1 ≤ a 0 := ha (by decide)
  have ha21 : a 2 ≤ a 1 := ha (by decide)
  have hb10 : b 1 ≤ b 0 := hb (by decide)
  have hb21 : b 2 ≤ b 1 := hb (by decide)
  have hmin' (k : ℕ) : min (a 0) k + min (a 1) k + min (a 2) k =
      min (b 0) k + min (b 1) k + min (b 2) k := by
    simpa [Fin.sum_univ_succ, add_assoc] using hmin k
  have hzero : a 0 = b 0 := by
    have h1 := hmin' (a 0)
    have h2 := hmin' (a 0 + 1)
    have h3 := hmin' (b 0)
    have h4 := hmin' (b 0 + 1)
    omega
  have hone : a 1 = b 1 := by
    have h1 := hmin' (a 1)
    have h2 := hmin' (a 1 + 1)
    have h3 := hmin' (b 1)
    have h4 := hmin' (b 1 + 1)
    omega
  have htwo : a 2 = b 2 := by
    have hh := hmin' (a 2 + b 2)
    omega
  funext i
  fin_cases i
  · exact hzero
  · exact hone
  · exact htwo

/-- Dominant rank-three elementary q-power groups have unique exponents,
including zero exponents. -/
theorem rankThree_elementary_exponents_unique
    (q : ℕ) (hq : q.Prime) (a b : Fin 3 → ℕ) (ha : Antitone a) (hb : Antitone b)
    (e : (∀ i, ZMod (q ^ a i)) ≃+ (∀ i, ZMod (q ^ b i))) : a = b :=
  rankThree_eq_of_min_sums a b ha hb (elementary_min_sums_eq q hq a b e)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ElementaryUniqueness.Construction
