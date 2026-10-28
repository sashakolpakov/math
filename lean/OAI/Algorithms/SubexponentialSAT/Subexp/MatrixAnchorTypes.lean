import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorReadProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.ReadPlan

namespace OAI.Algorithms

/-! Canonical one-hot color reads for the explicit joint-membership guard. -/

namespace SubexponentialSAT.Subexp.MatrixAnchorReadProgram

open BitProgram StructuredCalls StackRoutines MulticolorTypes

variable {r Q Δ : ℕ}

def colorWord (c : Fin r) : List Bool := List.ofFn fun d : Fin r => decide (c = d)
def wordRows (w : Word r Q) : List (List Bool) := List.ofFn fun t => colorWord (w t)

@[simp] theorem colorWord_length (c : Fin r) : (colorWord c).length = r := by simp [colorWord]

theorem colorWord_injective : Function.Injective (@colorWord r) := by
  intro a b h
  have hh := congrFun (List.ofFn_injective h) a
  simp only [decide_true] at hh
  exact (of_decide_eq_true hh.symm).symm

@[simp] theorem colorWord_eq_iff (a b : Fin r) : colorWord a = colorWord b ↔ a = b :=
  colorWord_injective.eq_iff

theorem wordRows_split (w : Word r Q) (t : Fin Q) :
    wordRows w = (wordRows w).take t.val ++ colorWord (w t) :: (wordRows w).drop (t.val + 1) := by
  have ht : t.val < (wordRows w).length := by simp [wordRows]
  have h := List.take_append_drop t.val (wordRows w)
  rw [List.drop_eq_getElem_cons ht] at h
  simpa [wordRows] using h.symm

theorem encodeWord_split (w : Word r Q) (t : Fin Q) :
    ReadPlan.encodeWord w = ((wordRows w).take t.val).flatten ++
      (colorWord (w t) ++ ((wordRows w).drop (t.val + 1)).flatten) := by
  change (wordRows w).flatten = _
  conv_lhs => rw [wordRows_split w t]
  simp

theorem readOne_typed (a : Data) (i : Fin 4) (w : Word r Q) (t : Fin Q)
    (hwork : ∀ j : Fin 42, j.val < 9 → a.stacks j = [])
    (hd : a.stacks (target i) = []) (hs : a.stacks (source i) = ReadPlan.encodeWord w)
    (hi : (a.stacks 37).length = t.val) (hw : (a.stacks 21).length = r) :
    Eval (readOne i) (9 * (Q * r) + t.val * (14 * r + 17) + 30 * r + 43)
      a (readOneResult a i (colorWord (w t))) := by
  have h := readOne_eval a i ((wordRows w).take t.val) (colorWord (w t))
    (((wordRows w).drop (t.val + 1)).flatten) hwork hd
    (by rw [hs, encodeWord_split])
    (by simpa [wordRows, Nat.min_eq_left t.isLt.le] using hi)
    (by
      intro row hrow
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hrow)
      simp [hw])
    (by simp [hw])
  simpa [hs, hw, wordRows, Nat.min_eq_left t.isLt.le, ReadPlan.wordWidth] using h

abbrev readFour : Cmd 10 42 := .seq (readOne 0) (.seq (readOne 1) (.seq (readOne 2) (readOne 3)))

def fourReadResult (a : Data) (words : Fin 4 → List Bool) : Data :=
  readOneResult (readOneResult (readOneResult (readOneResult a 0 (words 0)) 1 (words 1))
    2 (words 2)) 3 (words 3)

theorem readOneResult_work (a : Data) (i : Fin 4) (word : List Bool)
    (h : ∀ j : Fin 42, j.val < 9 → a.stacks j = []) :
    ∀ j : Fin 42, j.val < 9 → (readOneResult a i word).stacks j = [] := by
  intro j hj
  have hn : j ≠ target i := by
    intro he
    have hv := congrArg (fun k : Fin 42 => k.val) he
    change j.val = 38 + i.val at hv
    omega
  simpa [readOneResult, hn] using h j hj

theorem readFour_typed (a : Data) (words : Fin 4 → Word r Q) (t : Fin Q)
    (hwork : ∀ j : Fin 42, j.val < 9 → a.stacks j = [])
    (hd : ∀ i, a.stacks (target i) = [])
    (hs : ∀ i, a.stacks (source i) = ReadPlan.encodeWord (words i))
    (hi : (a.stacks 37).length = t.val) (hw : (a.stacks 21).length = r) :
    Eval readFour (4 * (9 * (Q * r) + t.val * (14 * r + 17) + 30 * r + 43)) a
      (fourReadResult a (fun i => colorWord (words i t))) := by
  let a1 := readOneResult a 0 (colorWord (words 0 t))
  let a2 := readOneResult a1 1 (colorWord (words 1 t))
  let a3 := readOneResult a2 2 (colorWord (words 2 t))
  have h1 := readOne_typed a 0 (words 0) t hwork (hd 0) (hs 0) hi hw
  have w1 := readOneResult_work a 0 (colorWord (words 0 t)) hwork
  have h2 := readOne_typed a1 1 (words 1) t w1
    (by simpa [a1, readOneResult, target] using hd 1)
    (by simpa [a1, readOneResult, source, target] using hs 1)
    (by simpa [a1, readOneResult, target] using hi)
    (by simpa [a1, readOneResult, target] using hw)
  have w2 := readOneResult_work a1 1 (colorWord (words 1 t)) w1
  have h3 := readOne_typed a2 2 (words 2) t w2
    (by simpa [a2, a1, readOneResult, target] using hd 2)
    (by simpa [a2, a1, readOneResult, source, target] using hs 2)
    (by simpa [a2, a1, readOneResult, target] using hi)
    (by simpa [a2, a1, readOneResult, target] using hw)
  have w3 := readOneResult_work a2 2 (colorWord (words 2 t)) w2
  have h4 := readOne_typed a3 3 (words 3) t w3
    (by simpa [a3, a2, a1, readOneResult, target] using hd 3)
    (by simpa [a3, a2, a1, readOneResult, source, target] using hs 3)
    (by simpa [a3, a2, a1, readOneResult, target] using hi)
    (by simpa [a3, a2, a1, readOneResult, target] using hw)
  have he := h1.seq (h2.seq (h3.seq h4))
  convert he using 1
  · ring
  · simp [fourReadResult, a3, a2, a1]

end SubexponentialSAT.Subexp.MatrixAnchorReadProgram

end OAI.Algorithms
