import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingRelations

namespace OAI.Algorithms

/-! One-hot word overlap is exactly the number of equal head coordinates. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes

private theorem zipWith_ofFn' {A B C : Type*} (op : A → B → C) {n : ℕ}
    (f : Fin n → A) (g : Fin n → B) :
    List.zipWith op (List.ofFn f) (List.ofFn g) = List.ofFn (fun i => op (f i) (g i)) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.ofFn_succ, ih]

private theorem count_true_ofFn {n : ℕ} (f : Fin n → Bool) :
    (List.ofFn f).count true = ∑ i, if f i then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ, ih]
    cases f 0 <;> simp [Nat.add_comm]

theorem headColorBits_and_count {r Q : ℕ} (u v : Word r Q) (t : Fin Q) :
    (List.zipWith (· && ·) (headColorBits u t) (headColorBits v t)).count true =
      if u t = v t then 1 else 0 := by
  rw [headColorBits, headColorBits, zipWith_ofFn', count_true_ofFn]
  by_cases h : u t = v t
  · simp [h]
  · apply (Finset.sum_eq_zero fun c _ => ?_).trans (ite_eq_right h).symm
    by_cases hu : u t = c
    · have hv : v t ≠ c := by intro hv; exact h (hu.trans hv.symm)
      simp [hu, hv]
    · simp [hu]

theorem encodeWord_and_count {r Q : ℕ} (u v : Word r Q) :
    (List.zipWith (· && ·) (SubexponentialSAT.Subexp.ReadPlan.encodeWord u)
      (SubexponentialSAT.Subexp.ReadPlan.encodeWord v)).count true =
      ∑ t : Fin Q, if u t = v t then 1 else 0 := by
  induction Q with
  | zero => simp [SubexponentialSAT.Subexp.ReadPlan.encodeWord]
  | succ Q ih =>
    have split (w : Word r (Q+1)) : SubexponentialSAT.Subexp.ReadPlan.encodeWord w =
        headColorBits w 0 ++ SubexponentialSAT.Subexp.ReadPlan.encodeWord (fun t => w t.succ) := by
      simp only [SubexponentialSAT.Subexp.ReadPlan.encodeWord, headColorBits, List.ofFn_succ,
        List.flatten_cons]
    rw [split u, split v, List.zipWith_append (by simp), List.count_append,
      headColorBits_and_count, ih, Fin.sum_univ_succ]

theorem encodeWord_and_count_eq_coordinate_count {r Q : ℕ} (u v : Word r Q) :
    (List.zipWith (· && ·) (SubexponentialSAT.Subexp.ReadPlan.encodeWord u)
      (SubexponentialSAT.Subexp.ReadPlan.encodeWord v)).count true =
      (List.ofFn (fun t : Fin Q => decide (u t = v t))).count true := by
  rw [encodeWord_and_count, count_true_ofFn]
  simp

end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
