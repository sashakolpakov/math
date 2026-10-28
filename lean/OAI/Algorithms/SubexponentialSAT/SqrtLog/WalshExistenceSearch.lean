import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.WalshExistence

namespace OAI.Algorithms

/-! Size and correctness of the executable exhaustive Walsh search. -/
namespace SubexponentialSAT.SqrtLog.WalshExistence

open scoped BigOperators
open Cayley

@[simp] theorem length_tuples {X : Type*} (xs : List X) (D : ℕ) :
    (tuples xs D).length = xs.length ^ D := by
  induction D with
  | zero => simp [tuples]
  | succ D ih =>
    simp [tuples, ih, List.map_const', pow_succ, Nat.mul_comm]

@[simp] theorem length_cubeList (r : ℕ) : (cubeList r).length = 2 ^ r := by
  simp [cubeList]

theorem candidate_count (r D : ℕ) :
    (tuples (cubeList r) D).length = 2 ^ (r * D) := by
  simp [pow_mul]

/-- A total executable choice. The default is used only outside the proven
parameter range; no proof, real arithmetic, or choice operator is evaluated. -/
def construct (r D q : ℕ) : Fin D → Cube r :=
  (search r D q).getD (fun _ => 0)

theorem construct_smallWalsh (r D q : ℕ) (hq : 1 ≤ q)
    (hD : 8 * q ^ 2 * (r + 1) ≤ D) :
    SmallWalsh (construct r D q) (1 / (q : ℝ)) := by
  obtain ⟨s, hs, hgood⟩ := search_succeeds r D q hq hD
  simpa [construct, hs] using hgood

theorem construct_good (r D q : ℕ) (hq : 1 ≤ q)
    (hD : 8 * q ^ 2 * (r + 1) ≤ D) : Good q (construct r D q) :=
  (good_iff_smallWalsh hq _).mpr (construct_smallWalsh r D q hq hD)

/-- The one-vertex cube requires no degree lower bound. -/
theorem smallWalsh_zero_dim {P : Type*} [Fintype P]
    (s : P → Cube 0) (ε : ℝ) : SmallWalsh s ε := by
  intro a ha
  exact (ha (Subsingleton.elim a 0)).elim

theorem construct_smallWalsh_zero_dim (D q : ℕ) :
    SmallWalsh (construct 0 D q) (1 / (q : ℝ)) :=
  smallWalsh_zero_dim _ _

theorem abs_characterInt (r : ℕ) (a x : Cube r) : |characterInt a x| = 1 := by
  have hr : |(characterInt a x : ℝ)| = 1 := by
    rw [characterInt_cast]
    rcases character_eq_one_or_neg_one a x with h | h <;> rw [h] <;> norm_num
  exact_mod_cast hr

theorem abs_walshInt_le {r D : ℕ} (s : Fin D → Cube r) (a : Cube r) :
    |walshInt s a| ≤ D := by
  unfold walshInt
  calc
    |∑ i, characterInt a (s i)| ≤ ∑ i, |characterInt a (s i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = D := by simp [abs_characterInt]

end SubexponentialSAT.SqrtLog.WalshExistence

end OAI.Algorithms
