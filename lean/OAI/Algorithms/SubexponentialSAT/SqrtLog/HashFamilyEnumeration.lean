import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamily

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashFamily

open scoped BigOperators
open Finset

/-- Explicit mixed-radix indexing: the coordinate tuple is encoded in base
`m`, and the coefficient tuple in base three. No choice is used by the map. -/
def candidateEquivFin (m d : ℕ) : Candidate m d ≃ Fin ((3 * m) ^ d) :=
  (Equiv.prodCongr
    (finFunctionFinEquiv : IndexTuple m d ≃ Fin (m ^ d))
    ((Equiv.piCongrRight fun _ : Fin d => (ZMod.finEquiv 3).symm.toEquiv).trans
      (finFunctionFinEquiv : (Fin d → Fin 3) ≃ Fin (3 ^ d)))).trans
    (finProdFinEquiv.trans (finCongr (by simp [mul_pow, Nat.mul_comm])))

/-- The finite hash family, in a computable order suitable for `List.ofFn`. -/
def enumerate (m d : ℕ) : Fin ((3 * m) ^ d) → Candidate m d :=
  (candidateEquivFin m d).symm

theorem enumerate_bijective (m d : ℕ) : Function.Bijective (enumerate m d) :=
  (candidateEquivFin m d).symm.bijective

theorem enumerate_row_support_le (m d : ℕ) (i : Fin ((3 * m) ^ d)) :
    supportCard (row (enumerate m d i)) ≤ d :=
  row_support_le _

theorem enumerate_detecting_card {m d : ℕ} (v : Fin m → ZMod 3) :
    (univ.filter fun i : Fin ((3 * m) ^ d) => eval (enumerate m d i) v ≠ 0).card =
      detectingCard (d := d) v := by
  classical
  unfold detectingCard
  exact Finset.card_equiv (candidateEquivFin m d).symm (fun i => by
    constructor
    · intro hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      simpa only [enumerate] using (Finset.mem_filter.mp hi).2
    · intro hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      simpa only [enumerate] using (Finset.mem_filter.mp hi).2)

/-- The indexed family detects every heavy vector on at least a third of its
indices, with repetitions in coordinate tuples and even repeated rows kept. -/
theorem enumerate_detection {m d : ℕ} (v : Fin m → ZMod 3) (hm : 0 < m)
    (heavy : m ≤ d * supportCard v) :
    (3 * m) ^ d ≤
      3 * (univ.filter fun i : Fin ((3 * m) ^ d) =>
        (∑ j, row (enumerate m d i) j * v j) ≠ 0).card := by
  simp_rw [row_dot]
  rw [enumerate_detecting_card, ← candidate_card]
  exact detecting_card_lower v hm heavy

end SubexponentialSAT.SqrtLog.HashFamily

end OAI.Algorithms
