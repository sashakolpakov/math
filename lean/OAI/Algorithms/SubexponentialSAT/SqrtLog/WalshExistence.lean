import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.WalshExistenceCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CayleyCharacters

namespace OAI.Algorithms

/-! Existence and finite executable search for a small Walsh spectrum. -/
namespace SubexponentialSAT.SqrtLog.WalshExistence

open scoped BigOperators
open Cayley

theorem exists_smallWalsh_of_budget (r D : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hbudget : 2 * (Fintype.card {a : Cube r // a ≠ 0} : ℝ) <
      Real.exp ((D : ℝ) * ε ^ 2 / 2)) :
    ∃ s : Fin D → Cube r, SmallWalsh s ε := by
  classical
  obtain ⟨s, hs⟩ := exists_samples
    (fun (a : {a : Cube r // a ≠ 0}) x => character a.val x)
    (by
      intro a x
      rcases character_eq_one_or_neg_one a.val x with h | h <;> rw [h] <;> norm_num)
    (fun a => character_sum_of_ne_zero a.val a.property) D ε hε hbudget
  refine ⟨s, ?_⟩
  intro a ha
  simpa [walsh] using hs ⟨a, ha⟩

theorem exists_smallWalsh (r D q : ℕ) (hq : 1 ≤ q)
    (hD : 8 * q ^ 2 * (r + 1) ≤ D) :
    ∃ s : Fin D → Cube r, SmallWalsh s (1 / (q : ℝ)) := by
  classical
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
  apply exists_smallWalsh_of_budget r D (1 / (q : ℝ)) (by positivity)
  have hc : (Fintype.card {a : Cube r // a ≠ 0} : ℝ) ≤ (2 : ℝ) ^ r := by
    have hn := Fintype.card_subtype_le (fun a : Cube r => a ≠ 0)
    rw [cube_card] at hn
    exact_mod_cast hn
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hpow : (2 : ℝ) ^ (r + 1) ≤ Real.exp ((r : ℝ) + 1) := by
    calc
      (2 : ℝ) ^ (r + 1) ≤ (Real.exp 1) ^ (r + 1) :=
        pow_le_pow_left₀ (by norm_num) htwo _
      _ = Real.exp ((r : ℝ) + 1) := by rw [← Real.exp_nat_mul]; simp
  have hident : ((8 * q ^ 2 * (r + 1) : ℕ) : ℝ) * (1 / (q : ℝ)) ^ 2 / 2 =
      4 * ((r : ℝ) + 1) := by
    push_cast
    field_simp
    ring
  have hhalf : 4 * ((r : ℝ) + 1) ≤ (D : ℝ) * (1 / (q : ℝ)) ^ 2 / 2 := by
    rw [← hident]
    gcongr
  calc
    2 * (Fintype.card {a : Cube r // a ≠ 0} : ℝ) ≤ 2 * (2 : ℝ) ^ r := by
      gcongr
    _ = (2 : ℝ) ^ (r + 1) := by rw [pow_succ]; ring
    _ ≤ Real.exp ((r : ℝ) + 1) := hpow
    _ < Real.exp (4 * ((r : ℝ) + 1)) := by
      apply Real.exp_lt_exp.mpr
      have : (0 : ℝ) ≤ r := by positivity
      linarith
    _ ≤ Real.exp ((D : ℝ) * (1 / (q : ℝ)) ^ 2 / 2) := Real.exp_le_exp.mpr hhalf

/-- The integer counterpart makes the predicate executable. -/
def characterInt {r : ℕ} (a x : Cube r) : ℤ :=
  ∏ j, if a j * x j = 0 then 1 else -1

def walshInt {r D : ℕ} (s : Fin D → Cube r) (a : Cube r) : ℤ :=
  ∑ i, characterInt a (s i)

@[simp] theorem characterInt_cast {r : ℕ} (a x : Cube r) :
    (characterInt a x : ℝ) = character a x := by
  simp [characterInt, character, bitSign]

@[simp] theorem walshInt_cast {r D : ℕ} (s : Fin D → Cube r) (a : Cube r) :
    (walshInt s a : ℝ) = walsh s a := by
  simp [walshInt, walsh]

def Good {r D : ℕ} (q : ℕ) (s : Fin D → Cube r) : Prop :=
  ∀ a, a ≠ 0 → (q : ℤ) * |walshInt s a| ≤ D

instance {r D : ℕ} (q : ℕ) (s : Fin D → Cube r) : Decidable (Good q s) :=
  inferInstanceAs (Decidable (∀ a, a ≠ 0 → (q : ℤ) * |walshInt s a| ≤ D))

theorem good_iff_smallWalsh {r D q : ℕ} (hq : 1 ≤ q) (s : Fin D → Cube r) :
    Good q s ↔ SmallWalsh s (1 / (q : ℝ)) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  constructor
  · intro h a ha
    have hi := h a ha
    have hr : (q : ℝ) * |(walshInt s a : ℝ)| ≤ (D : ℝ) := by exact_mod_cast hi
    rw [walshInt_cast] at hr
    simpa only [Fintype.card_fin, div_eq_mul_inv, one_mul, mul_one, mul_comm] using
      (le_div_iff₀ hqpos).mpr (show |walsh s a| * q ≤ (D : ℝ) by nlinarith)
  · intro h a ha
    have hr := h a ha
    simp only [Fintype.card_fin] at hr
    have hr' : |walsh s a| ≤ (D : ℝ) / q := by
      simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hr
    have hh := (le_div_iff₀ hqpos).mp hr'
    have hz : (q : ℝ) * |(walshInt s a : ℝ)| ≤ (D : ℝ) := by
      rw [walshInt_cast]
      nlinarith
    exact_mod_cast hz

/-- Explicit lexicographic enumeration of finite tuples. -/
def tuples {X : Type*} (xs : List X) : (D : ℕ) → List (Fin D → X)
  | 0 => [Fin.elim0]
  | D + 1 => xs.flatMap (fun x => (tuples xs D).map (Fin.cons x))

theorem mem_tuples {X : Type*} (xs : List X) (hxs : ∀ x, x ∈ xs)
    (D : ℕ) (s : Fin D → X) : s ∈ tuples xs D := by
  induction D with
  | zero =>
    have hs : s = Fin.elim0 := by funext i; exact Fin.elim0 i
    simp [tuples, hs]
  | succ D ih =>
    simp only [tuples, List.mem_flatMap, List.mem_map]
    refine ⟨s 0, hxs _, Fin.tail s, ih _, ?_⟩
    exact Fin.cons_self_tail s

def cubeList (r : ℕ) : List (Cube r) := tuples [0, 1] r

theorem mem_cubeList (r : ℕ) (x : Cube r) : x ∈ cubeList r := by
  apply mem_tuples
  intro z
  have hz : z = 0 ∨ z = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp z.val_lt) with h | h
    · left
      apply ZMod.val_injective
      simpa only [ZMod.val_zero] using h
    · right
      apply ZMod.val_injective
      simpa only [ZMod.val_one] using h
  simpa only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using hz

/-- Tests only integer Walsh sums; every search state and every candidate is finite. -/
def search (r D q : ℕ) : Option (Fin D → Cube r) :=
  (tuples (cubeList r) D).find? (fun s => decide (Good q s))

theorem search_some_good {r D q : ℕ} {s : Fin D → Cube r}
    (h : search r D q = some s) : Good q s := by
  have := List.find?_some h
  exact of_decide_eq_true this

theorem search_succeeds (r D q : ℕ) (hq : 1 ≤ q)
    (hD : 8 * q ^ 2 * (r + 1) ≤ D) :
    ∃ s, search r D q = some s ∧ SmallWalsh s (1 / (q : ℝ)) := by
  obtain ⟨s, hs⟩ := exists_smallWalsh r D q hq hD
  have hg : Good q s := (good_iff_smallWalsh hq s).mpr hs
  have hsome : (search r D q).isSome := by
    apply List.find?_isSome.mpr
    exact ⟨s, mem_tuples _ (mem_cubeList r) D s, decide_eq_true hg⟩
  cases he : search r D q with
  | none => simp [he] at hsome
  | some z =>
    exact ⟨z, rfl, (good_iff_smallWalsh hq z).mp (search_some_good he)⟩

end SubexponentialSAT.SqrtLog.WalshExistence

end OAI.Algorithms
