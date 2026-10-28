import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelection
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionCost
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BinaryArgminRecords
import OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
import OAI.Algorithms.SubexponentialSAT.ProgramEncoding

namespace OAI.Algorithms

/-! Concrete scored-record representation of maximal-minor selection.
The accompanying score command and determinant command must produce this
stream before the closed record scanner is invoked. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgramSelect

open scoped BigOperators
open RowSelection

variable {a b : ℕ}

def score (P : Fin a → Fin b → ℤ) (cap : ℕ) (c : Candidate a b) : ℕ :=
  if c.determinant P ≠ 0 then cap-c.size else cap

def payload (c : Candidate a b) : List Bool :=
  (List.ofFn fun i => Encoding.encodeNat (c.rows i).val).flatten

def entry (P : Fin a → Fin b → ℤ) (cap B : ℕ) (c : Candidate a b) :
    BinaryArgmin.Entry :=
  ⟨payload c, SubexpLiftRing.fixedBits B (score P cap c)⟩

theorem score_le (P : Fin a → Fin b → ℤ) (cap : ℕ) (c : Candidate a b) :
    score P cap c ≤ cap+1 := by
  unfold score
  split_ifs <;> omega

theorem entry_value (P : Fin a → Fin b → ℤ) (cap B : ℕ)
    (hB : cap+1 < 2^B) (c : Candidate a b) :
    BinaryArgmin.value (entry P cap B c) = score P cap c := by
  exact SubexpLiftRing.toNat_fixedBits_of_lt B _ ((score_le P cap c).trans_lt hB)

theorem payload_length_le (cap : ℕ) (c : Candidate a b) (hc : c.size ≤ cap) :
    (payload c).length ≤ 2*cap*(a+2)+1 := by
  rw [payload, List.length_flatten]
  simp only [ List.map_ofFn, Function.comp_apply, Encoding.length_encodeNat, List.sum_ofFn]
  have hm : (∑ i : Fin c.size, ((c.rows i).val+1)) ≤ c.size*(a+1) := by
    calc
      _ ≤ ∑ _ : Fin c.size, (a+1) := Finset.sum_le_sum (fun i _ => by omega)
      _ = _ := by simp
  nlinarith

theorem entry_fits (P : Fin a → Fin b → ℤ) (cap B : ℕ)
    (c : Candidate a b) (hc : c.size ≤ cap) :
    BinaryArgmin.Fits B (2*cap*(a+2)+1) (entry P cap B c) := by
  exact ⟨SubexpLiftRing.fixedBits_length _ _, payload_length_le cap c hc⟩

theorem score_lt_iff (P : Fin a → Fin b → ℤ) (cap : ℕ)
    (old next : Candidate a b) (ho : old.determinant P ≠ 0)
    (hos : old.size ≤ cap) (hns : next.size ≤ cap) :
    score P cap next < score P cap old ↔
      next.determinant P ≠ 0 ∧ old.size < next.size := by
  by_cases hn : next.determinant P ≠ 0 <;> simp [score, ho, hn] ; omega

theorem pick_entry (P : Fin a → Fin b → ℤ) (cap B : ℕ)
    (hB : cap+1 < 2^B) (old next : Candidate a b)
    (ho : old.determinant P ≠ 0) (hos : old.size ≤ cap) (hns : next.size ≤ cap) :
    BinaryArgmin.pick (entry P cap B old) (entry P cap B next) =
      entry P cap B (choose P old next) := by
  simp only [BinaryArgmin.pick, entry_value P cap B hB,
    score_lt_iff P cap old next ho hos hns, choose]
  split_ifs <;> rfl

theorem best_entries (P : Fin a → Fin b → ℤ) (cap B : ℕ)
    (hB : cap+1 < 2^B) (cs : List (Candidate a b)) (old : Candidate a b)
    (ho : old.determinant P ≠ 0) (hos : old.size ≤ cap)
    (hcs : ∀ c ∈ cs, c.size ≤ cap) :
    HashSelect.best BinaryArgmin.value (entry P cap B old) (cs.map (entry P cap B)) =
      entry P cap B (scan P cs old) := by
  induction cs generalizing old with
  | nil => rfl
  | cons c cs ih =>
    have hc := hcs c (by simp)
    change HashSelect.best BinaryArgmin.value
      (BinaryArgmin.pick (entry P cap B old) (entry P cap B c))
      (cs.map (entry P cap B)) = _
    rw [pick_entry P cap B hB old c ho hos hc]
    exact ih _ (choose_good P old c ho) (choose_le P old c hos hc)
      (fun x hx => hcs x (by simp [hx]))

end SubexponentialSAT.SqrtLog.RowSelectionProgramSelect

end OAI.Algorithms
