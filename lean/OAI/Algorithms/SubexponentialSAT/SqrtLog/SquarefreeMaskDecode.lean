import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeIndexEncoding

namespace OAI.Algorithms

/-! The fixed-length support-mask encoding and its executable inverse.
Words shorter than n are padded by false; longer words are truncated.
On length-n words these operations are mutually inverse. -/

namespace SubexponentialSAT.SqrtLog.Squarefree

def decodeMask (n : ℕ) (xs : List Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => xs[i.val]?.getD false = true)

@[simp] theorem mem_decodeMask (n : ℕ) (xs : List Bool) (i : Fin n) :
    i ∈ decodeMask n xs ↔ xs[i.val]?.getD false = true := by
  simp [decodeMask]

@[simp] theorem decodeMask_encodeMask {n : ℕ} (s : Finset (Fin n)) :
    decodeMask n (encodeMask s) = s := by
  ext i
  simp [decodeMask, encodeMask]

theorem encodeMask_decodeMask (n : ℕ) (xs : List Bool) (h : xs.length = n) :
    encodeMask (decodeMask n xs) = xs := by
  apply List.ext_getElem
  · simp [h]
  · intro i hi hj
    simp [encodeMask, decodeMask, List.getElem?_eq_getElem hj]

@[simp] theorem encodeMask_count {n : ℕ} (s : Finset (Fin n)) :
    (encodeMask s).count true = s.card := by
  let selected := (List.finRange n).filter (fun i => decide (i ∈ s))
  have hn : selected.Nodup := (List.nodup_finRange n).filter _
  have hs : selected.toFinset = s := by
    ext i
    simp [selected]
  have hc : ∀ l : List (Fin n),
      (l.map (fun i => decide (i ∈ s))).count true =
        (l.filter (fun i => decide (i ∈ s))).length := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih => by_cases hi : i ∈ s <;> simp [hi, ih]
  calc
    (encodeMask s).count true = selected.length := by
      simpa only [encodeMask, List.ofFn_eq_map, selected] using hc (List.finRange n)
    _ = selected.toFinset.card := (List.toFinset_card_of_nodup hn).symm
    _ = s.card := congrArg Finset.card hs

theorem decodeMask_card (n : ℕ) (xs : List Bool) (h : xs.length = n) :
    (decodeMask n xs).card = xs.count true := by
  rw [← encodeMask_count, encodeMask_decodeMask n xs h]

end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
