import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Rational Common Denominator -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.RationalCommonDenominator

noncomputable section

/-! A finite strictly positive rational vector becomes a strictly
positive natural vector after multiplication by a common denominator. -/
open scoped BigOperators Classical
universe u

theorem positiveRationalVector_commonDenominator {ι : Type u} [Fintype ι]
    (q : ι → ℚ) (hq : ∀ i, 0 < q i) :
    ∃ D : ℕ, 0 < D ∧ ∃ a : ι → ℕ, (∀ i, 0 < a i) ∧ ∀ i, (a i : ℚ) = D * q i := by
  let D := ∏ i, (q i).den
  have hD : 0 < D := Finset.prod_pos (fun i _ => (q i).den_pos)
  have hdiv (i : ι) : (q i).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  let a : ι → ℕ := fun i => (q i).num.toNat * (D / (q i).den)
  have hnum (i : ι) : 0 < (q i).num := Rat.num_pos.mpr (hq i)
  refine ⟨D, hD, a, ?_, ?_⟩
  · intro i
    exact Nat.mul_pos (Int.pos_iff_toNat_pos.mp (hnum i))
      (Nat.div_pos (Nat.le_of_dvd hD (hdiv i)) (q i).den_pos)
  · intro i
    have hn : (((q i).num.toNat : ℕ) : ℚ) = ((q i).num : ℚ) := by
      exact_mod_cast (Int.toNat_of_nonneg (hnum i).le)
    have hd : ((D / (q i).den : ℕ) : ℚ) * ((q i).den : ℚ) = (D : ℚ) := by
      exact_mod_cast (Nat.div_mul_cancel (hdiv i))
    have hden : ((q i).den : ℚ) ≠ 0 := by exact_mod_cast (q i).den_nz
    have hqnum : ((q i).num : ℚ) = q i * ((q i).den : ℚ) :=
      (div_eq_iff hden).mp (q i).num_div_den
    change (((q i).num.toNat * (D / (q i).den) : ℕ) : ℚ) = _
    rw [Nat.cast_mul, hn, hqnum]
    calc
      q i * ((q i).den : ℚ) * ((D / (q i).den : ℕ) : ℚ) =
          (((D / (q i).den : ℕ) : ℚ) * ((q i).den : ℚ)) * q i := by ring
      _ = (D : ℚ) * q i := by rw [hd]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.RationalCommonDenominator
