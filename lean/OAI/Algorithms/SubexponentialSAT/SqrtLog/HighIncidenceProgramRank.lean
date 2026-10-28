import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence
import OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration

namespace OAI.Algorithms

/-! Rank semantics for the native all-visits Boolean odometer. These maps are
proof-level reindexings; the machine changes its physical tuple in place. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Rank
open scoped BigOperators

def bitRank (h : ℕ) (a : Fin h → Bool) : Fin (2 ^ h) :=
  ⟨CounterPrograms.value (List.ofFn a), by
    simpa using ExecCNFTupleOdometer.value_lt_power_length (List.ofFn a)⟩

theorem bitRank_injective (h : ℕ) : Function.Injective (bitRank h) := by
  intro a b hab
  apply List.ofFn_injective
  apply ExecCNFTupleEnumeration.word_eq_of_length_value (by simp)
  exact congrArg Fin.val hab

noncomputable def rankEquiv (h : ℕ) : (Fin h → Bool) ≃ Fin (2 ^ h) :=
  Equiv.ofBijective (bitRank h)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨bitRank_injective h, by simp⟩)

noncomputable def assignment (h : ℕ) (r : Fin (2 ^ h)) : Fin h → Bool :=
  (rankEquiv h).symm r

theorem assignment_value (h : ℕ) (r : Fin (2 ^ h)) :
    CounterPrograms.value (List.ofFn (assignment h r)) = r.val := by
  exact congrArg Fin.val ((rankEquiv h).apply_symm_apply r)

theorem assignment_fixedBits (h : ℕ) (r : Fin (2 ^ h)) :
    List.ofFn (assignment h r) = ExecCNFTupleEnumeration.fixedBits h r.val := by
  apply ExecCNFTupleEnumeration.word_eq_of_length_value (by simp)
  rw [assignment_value, ExecCNFTupleEnumeration.fixedBits_value h r.val r.isLt]

theorem tuple_of_rank {h : ℕ} (words : List (List Bool))
    (hshape : words.map List.length = List.replicate h 1)
    (r : Fin (2 ^ h)) (hr : CounterPrograms.value words.flatten = r.val) :
    words = (List.ofFn (assignment h r)).map (fun b => [b]) := by
  apply ExecCNFTupleEnumeration.tuple_eq_of_shape_value
  · simpa [List.map_map, Function.comp_def] using hshape
  · have hflat : ((List.ofFn (assignment h r)).map (fun b => [b])).flatten =
          List.ofFn (assignment h r) := by
        generalize List.ofFn (assignment h r) = xs
        induction xs with
        | nil => rfl
        | cons x xs ih => simp [ih]
    rw [hflat]
    exact hr.trans (assignment_value h r).symm

def reindex {H : Type*} {h : ℕ} (order : Fin h ≃ H) : (Fin h → Bool) ≃ (H → Bool) where
  toFun a v := a (order.symm v)
  invFun b i := b (order i)
  left_inv := by intro a; funext i; simp
  right_inv := by intro b; funext v; simp

noncomputable def highEquiv {H : Type*} {h : ℕ} (order : Fin h ≃ H) :
    Fin (2 ^ h) ≃ (H → Bool) := (rankEquiv h).symm.trans (reindex order)

theorem sum_by_rank {H M : Type*} [Fintype H] [DecidableEq H] [AddCommMonoid M] {h : ℕ}
    (order : Fin h ≃ H) (f : (H → Bool) → M) :
    ∑ a, f a = ∑ r : Fin (2 ^ h), f (highEquiv order r) := by
  exact (Fintype.sum_equiv (highEquiv order) _ _ (fun _ => rfl)).symm

/-- Every original assignment occurs once in the outer rank sum and inner
free-coordinate sum. This is the exact count bridge, including unused vars. -/
theorem sum_original_by_rank {V M : Type*} [Fintype V] [DecidableEq V]
    [AddCommMonoid M] (H : Finset V) (order : Fin H.card ≃ H)
    (f : (V → Bool) → M) :
    ∑ x, f x = ∑ r : Fin (2 ^ H.card),
      ∑ b : {v : V // v ∉ H} → Bool, f (HighIncidence.glue H (highEquiv order r) b) := by
  rw [HighIncidence.sum_assignments_split H f]
  exact sum_by_rank order _

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Rank

end OAI.Algorithms
