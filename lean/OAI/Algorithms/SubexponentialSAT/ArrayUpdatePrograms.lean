import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ArrayPrograms
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace OAI.Algorithms

/-!
# Preserving access and update of packed arrays

The instruction tables have eight Boolean stacks. The record index and width
are unary stack data, so neither value affects the finite program control.
Stack 7 saves the preceding records in reverse order and restores them after
the selected record is read or replaced.
-/

namespace SubexponentialSAT.ArrayUpdatePrograms

open BitProgram StackRoutines ArrayPrograms StructuredCalls

private theorem copy_eval {r s : ℕ} (src dst tmp : Fin s) (value present : Fin r)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (hvp : value ≠ present)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) (ht : stk tmp = []) :
    Eval (.call (copyProgram src dst tmp value present)) (7 * (stk src).length + 5)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, copyStacks src dst stk⟩ := by
  apply Eval.call
  have t := halt_after_trace _
    (copyProgram_trace src dst tmp value present hsd hst htd hvp regs stk ht) 7 rfl rfl
  simpa [StructuredProgram.State.withPC, copyResult, copyProgram, Nat.add_assoc] using t

private theorem transfer_eval {r s : ℕ} (src dst : Fin s) (value present : Fin r)
    (hsd : src ≠ dst) (hvp : value ≠ present)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    Eval (.call (transferProgram src dst value present)) (3 * (stk src).length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, transferStacks src dst stk⟩ := by
  apply Eval.call
  have t := halt_after_trace _
    (transferProgram_trace src dst value present hsd hvp regs stk) 3 rfl rfl
  simpa [StructuredProgram.State.withPC, transferResult, transferProgram, Nat.add_assoc] using t

private theorem countedTransfer_eval {r s : ℕ} (counter src dst : Fin s)
    (value present : Fin r) (hcs : counter ≠ src) (hcd : counter ≠ dst)
    (hsd : src ≠ dst) (hvp : value ≠ present)
    (segment rest countWord : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hs : stk src = segment ++ rest) (hc : stk counter = countWord)
    (hlen : countWord.length = segment.length) :
    Eval (.call (countedTransferProgram counter src dst value present))
      (4 * segment.length + 3) ⟨regs, stk⟩
      ⟨readRegs regs value present none, countedTransferStacks counter src dst segment rest stk⟩ := by
  apply Eval.call
  have t := halt_after_trace _ (countedTransferProgram_trace counter src dst value present
    hcs hcd hsd hvp segment rest countWord regs stk hs hc hlen) 4 rfl rfl
  simpa [StructuredProgram.State.withPC, countedTransferResult, countedTransferProgram,
    Nat.add_assoc] using t

private theorem countedCopy_eval {r s : ℕ} (counter src dst tmp : Fin s)
    (value present : Fin r) (hcs : counter ≠ src) (hcd : counter ≠ dst)
    (hct : counter ≠ tmp) (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (hvp : value ≠ present) (segment rest countWord : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hs : stk src = segment ++ rest) (hc : stk counter = countWord)
    (hlen : countWord.length = segment.length) (ht : stk tmp = []) :
    Eval (.call (countedCopyProgram counter src dst tmp value present))
      (8 * segment.length + 5) ⟨regs, stk⟩
      ⟨readRegs regs value present none, countedCopyStacks counter dst segment stk⟩ := by
  apply Eval.call
  have t := halt_after_trace _ (countedCopyProgram_trace counter src dst tmp value present
    hcs hcd hct hsd hst htd hvp segment rest countWord regs stk hs hc hlen ht) 8 rfl rfl
  simpa [StructuredProgram.State.withPC, countedCopyResult, countedCopyProgram,
    Nat.add_assoc] using t

private theorem countedSkip_eval {r s : ℕ} (counter src tmp : Fin s)
    (value present : Fin r) (hcs : counter ≠ src) (hct : counter ≠ tmp)
    (hst : src ≠ tmp) (hvp : value ≠ present)
    (segment rest countWord : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hs : stk src = segment ++ rest) (hc : stk counter = countWord)
    (hlen : countWord.length = segment.length) (ht : stk tmp = []) :
    Eval (.call (countedSkipProgram counter src tmp value present))
      (6 * segment.length + 5) ⟨regs, stk⟩
      ⟨readRegs regs value present none, countedSkipStacks counter src rest stk⟩ := by
  apply Eval.call
  have t := halt_after_trace _ (countedSkipProgram_trace counter src tmp value present
    hcs hct hst hvp segment rest countWord regs stk hs hc hlen ht) 6 rfl rfl
  simpa [StructuredProgram.State.withPC, countedSkipResult, countedSkipProgram,
    Nat.add_assoc] using t

/-- Save one runtime-width record on stack 7, consuming neither the width nor
the existing saved records. -/
abbrev saveRecordCmd {r : ℕ} (value present : Fin r) : Cmd r 8 :=
  .seq (.call (copyProgram 3 4 5 value present))
    (.call (countedTransferProgram 4 0 7 value present))

def savedRecordStacks (record rest : List Bool) (stk : Stacks (Fin 8)) :
    Stacks (Fin 8) :=
  Function.update (Function.update stk 0 rest) 7 (record.reverse ++ stk 7)

theorem saveRecord_eval {r : ℕ} (value present : Fin r) (hvp : value ≠ present)
    (record rest widthWord : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin 8))
    (hs : stk 0 = record ++ rest) (hw : stk 3 = widthWord)
    (hlen : record.length = widthWord.length) (hc : stk 4 = []) (ht : stk 5 = []) :
    Eval (saveRecordCmd value present) (11 * widthWord.length + 8)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, savedRecordStacks record rest stk⟩ := by
  have a := copy_eval (3 : Fin 8) 4 5 value present (by decide) (by decide) (by decide)
    hvp regs stk ht
  have b := countedTransfer_eval (4 : Fin 8) 0 7 value present
    (by decide) (by decide) (by decide) hvp record rest widthWord
    (readRegs regs value present none) (copyStacks 3 4 stk)
    (by simpa [copyStacks] using hs) (by simp [copyStacks, hw, hc]) hlen.symm
  have hfinal : countedTransferStacks 4 0 7 record rest (copyStacks 3 4 stk) =
      savedRecordStacks record rest stk := by
    funext j
    fin_cases j <;> simp [countedTransferStacks, copyStacks, savedRecordStacks, hc]
  have t := a.seq b
  dsimp [saveRecordCmd]
  convert t using 1 <;> simp [hw, hlen, readRegs_reset, hfinal] ; omega

abbrev readIndexCmd {r : ℕ} (value present : Fin r) : Cmd r 8 :=
  .base (.atom (.pop 2 value present))

def afterIndexRead {r : ℕ} (value present : Fin r) (regs : Fin r → Bool)
    (stk : Stacks (Fin 8)) : State r 8 :=
  ⟨readRegs regs value present (stk 2).head?, Function.update stk 2 (stk 2).tail⟩

private theorem readIndex_eval {r : ℕ} (value present : Fin r) (regs : Fin r → Bool)
    (stk : Stacks (Fin 8)) :
    Eval (readIndexCmd value present) 1 ⟨regs, stk⟩ (afterIndexRead value present regs stk) := by
  exact .base (.atom _ _)

abbrev saveBeforeLoop {r : ℕ} (value present : Fin r) : Cmd r 8 :=
  .while present (.seq (saveRecordCmd value present) (readIndexCmd value present))

/-- The index is consumed; the width is preserved. -/
abbrev saveBeforeCmd {r : ℕ} (value present : Fin r) : Cmd r 8 :=
  .seq (readIndexCmd value present) (saveBeforeLoop value present)

def savedBeforeStacks (earlier : List (List Bool)) (rest : List Bool)
    (stk : Stacks (Fin 8)) : Stacks (Fin 8) :=
  Function.update (Function.update (Function.update stk 2 []) 0 rest)
    7 (earlier.flatten.reverse ++ stk 7)

private theorem savedBeforeStacks_cons (row : List Bool) (earlier : List (List Bool))
    (rest indexTail : List Bool) (stk : Stacks (Fin 8)) :
    savedBeforeStacks earlier rest
        (savedRecordStacks row (earlier.flatten ++ rest) (Function.update stk 2 indexTail)) =
      savedBeforeStacks (row :: earlier) rest stk := by
  funext j
  fin_cases j <;> simp [savedBeforeStacks, savedRecordStacks, List.flatten_cons,
    List.reverse_append, List.append_assoc]

theorem saveBeforeLoop_eval {r : ℕ} (value present : Fin r) (hvp : value ≠ present)
    (earlier : List (List Bool)) (rest widthWord indexWord : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin 8))
    (hs : stk 0 = earlier.flatten ++ rest) (hw : stk 3 = widthWord)
    (hi : stk 2 = indexWord) (hiLen : indexWord.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
    (hc : stk 4 = []) (ht : stk 5 = []) :
    Eval (saveBeforeLoop value present) (earlier.length * (11 * widthWord.length + 10) + 1)
      (afterIndexRead value present regs stk)
      ⟨readRegs regs value present none, savedBeforeStacks earlier rest stk⟩ := by
  induction earlier generalizing indexWord regs stk with
  | nil =>
      have hi0 : indexWord = [] := List.length_eq_zero_iff.mp (by simpa using hiLen)
      have hnil : stk 2 = [] := hi.trans hi0
      have hst : savedBeforeStacks [] rest stk = Function.update stk 2 [] := by
        funext j
        fin_cases j <;> simp_all [savedBeforeStacks]
      simpa [saveBeforeLoop, afterIndexRead, hnil, hst] using
        (Eval.while_false (test := present)
          (body := .seq (saveRecordCmd value present) (readIndexCmd value present))
          (a := afterIndexRead value present regs stk)
          (by simp [afterIndexRead, hnil, readRegs_present]))
  | cons row earlier ih =>
      cases indexWord with
      | nil => simp at hiLen
      | cons bit indexTail =>
          have hrow : row.length = widthWord.length := hrows row (by simp)
          have htail : ∀ x ∈ earlier, x.length = widthWord.length := by
            intro x hx
            exact hrows x (by simp [hx])
          let regs₁ := readRegs regs value present (some bit)
          let regs₂ := readRegs regs₁ value present none
          let stk₁ := Function.update stk 2 indexTail
          let stk₂ := savedRecordStacks row (earlier.flatten ++ rest) stk₁
          have a := saveRecord_eval value present hvp row (earlier.flatten ++ rest) widthWord
            regs₁ stk₁ (by simpa [stk₁, List.flatten_cons, List.append_assoc] using hs)
            (by simpa [stk₁] using hw) hrow (by simpa [stk₁] using hc)
            (by simpa [stk₁] using ht)
          have b := readIndex_eval value present regs₂ stk₂
          have c := ih indexTail regs₂ stk₂
            (by simp [stk₂, savedRecordStacks])
            (by simpa [stk₂, stk₁, savedRecordStacks] using hw)
            (by simp [stk₂, stk₁, savedRecordStacks]) (by simpa using hiLen) htail
            (by simpa [stk₂, stk₁, savedRecordStacks] using hc)
            (by simpa [stk₂, stk₁, savedRecordStacks] using ht)
          have loop := Eval.while_true (test := present)
            (by simp [regs₁, readRegs_present]) (a.seq b) c
          have hfinal := savedBeforeStacks_cons row earlier rest indexTail stk
          dsimp [saveBeforeLoop]
          convert loop using 1 <;>
            simp [afterIndexRead, hi, stk₁, stk₂, regs₁, regs₂, readRegs_reset,
              hfinal ] ; ring

theorem saveBefore_eval {r : ℕ} (value present : Fin r) (hvp : value ≠ present)
    (earlier : List (List Bool)) (rest widthWord indexWord : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin 8))
    (hs : stk 0 = earlier.flatten ++ rest) (hw : stk 3 = widthWord)
    (hi : stk 2 = indexWord) (hiLen : indexWord.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
    (hc : stk 4 = []) (ht : stk 5 = []) :
    Eval (saveBeforeCmd value present) (earlier.length * (11 * widthWord.length + 10) + 2)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, savedBeforeStacks earlier rest stk⟩ := by
  have t := (readIndex_eval value present regs stk).seq
    (saveBeforeLoop_eval value present hvp earlier rest widthWord indexWord regs stk
      hs hw hi hiLen hrows hc ht)
  convert t using 1
  omega

/-- Copy the selected record in forward order onto stack 1, preserving the
array suffix on stack 0. -/
abbrev readSelectedCmd {r : ℕ} (value present : Fin r) : Cmd r 8 :=
  .seq (.call (copyProgram 3 4 5 value present))
    (.call (countedCopyProgram 4 0 1 6 value present))

theorem readSelected_eval {r : ℕ} (value present : Fin r) (hvp : value ≠ present)
    (record rest widthWord : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin 8))
    (hs : stk 0 = record ++ rest) (hw : stk 3 = widthWord)
    (hlen : record.length = widthWord.length)
    (hc : stk 4 = []) (ht : stk 5 = []) (hb : stk 6 = []) :
    Eval (readSelectedCmd value present) (15 * widthWord.length + 10)
      ⟨regs, stk⟩
      ⟨readRegs regs value present none, Function.update stk 1 (record ++ stk 1)⟩ := by
  have a := copy_eval (3 : Fin 8) 4 5 value present (by decide) (by decide) (by decide)
    hvp regs stk ht
  have b := countedCopy_eval (4 : Fin 8) 0 1 6 value present
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hvp
    record rest widthWord (readRegs regs value present none) (copyStacks 3 4 stk)
    (by simpa [copyStacks] using hs) (by simp [copyStacks, hw, hc]) hlen.symm
    (by simpa [copyStacks] using hb)
  have hfinal : countedCopyStacks 4 1 record (copyStacks 3 4 stk) =
      Function.update stk 1 (record ++ stk 1) := by
    funext j
    fin_cases j <;> simp [countedCopyStacks, copyStacks, hc]
  have t := a.seq b
  dsimp [readSelectedCmd]
  convert t using 1 <;> simp [hw, hlen, readRegs_reset, hfinal] ; omega

/-- Replace the selected record by the equally wide word in stack 1.
The replacement word itself is preserved. -/
abbrev replaceSelectedCmd {r : ℕ} (value present : Fin r) : Cmd r 8 :=
  .seq (.call (copyProgram 3 4 5 value present))
    (.seq (.call (countedSkipProgram 4 0 6 value present))
      (.call (copyProgram 1 0 6 value present)))

theorem replaceSelected_eval {r : ℕ} (value present : Fin r) (hvp : value ≠ present)
    (record replacement rest widthWord : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin 8))
    (hs : stk 0 = record ++ rest) (hn : stk 1 = replacement) (hw : stk 3 = widthWord)
    (hlen : record.length = widthWord.length) (hnew : replacement.length = widthWord.length)
    (hc : stk 4 = []) (ht : stk 5 = []) (hb : stk 6 = []) :
    Eval (replaceSelectedCmd value present) (20 * widthWord.length + 15)
      ⟨regs, stk⟩
      ⟨readRegs regs value present none, Function.update stk 0 (replacement ++ rest)⟩ := by
  have a := copy_eval (3 : Fin 8) 4 5 value present (by decide) (by decide) (by decide)
    hvp regs stk ht
  have b := countedSkip_eval (4 : Fin 8) 0 6 value present
    (by decide) (by decide) (by decide) hvp record rest widthWord
    (readRegs regs value present none) (copyStacks 3 4 stk)
    (by simpa [copyStacks] using hs) (by simp [copyStacks, hw, hc]) hlen.symm
    (by simpa [copyStacks] using hb)
  have c := copy_eval (1 : Fin 8) 0 6 value present (by decide) (by decide) (by decide)
    hvp (readRegs (readRegs regs value present none) value present none)
    (countedSkipStacks 4 0 rest (copyStacks 3 4 stk))
    (by simpa [countedSkipStacks, copyStacks] using hb)
  have hfinal : copyStacks 1 0 (countedSkipStacks 4 0 rest (copyStacks 3 4 stk)) =
      Function.update stk 0 (replacement ++ rest) := by
    funext j
    fin_cases j <;> simp [countedSkipStacks, copyStacks, hc, hn]
  have t := a.seq (b.seq c)
  simp only [readRegs_reset, hfinal] at t
  dsimp [replaceSelectedCmd]
  convert t using 1 ;
    simp [hw, hlen, hnew, hn, countedSkipStacks, copyStacks] ; omega

/-- The full access command restores all preceding records after reading. -/
abbrev readCmd {r : ℕ} (value present : Fin r) : Cmd r 8 :=
  .seq (saveBeforeCmd value present)
    (.seq (readSelectedCmd value present) (.call (transferProgram 7 0 value present)))

/-- The full update command restores all preceding records after replacement. -/
abbrev replaceCmd {r : ℕ} (value present : Fin r) : Cmd r 8 :=
  .seq (saveBeforeCmd value present)
    (.seq (replaceSelectedCmd value present) (.call (transferProgram 7 0 value present)))

def readStacks (record : List Bool) (stk : Stacks (Fin 8)) : Stacks (Fin 8) :=
  Function.update (Function.update stk 2 []) 1 (record ++ stk 1)

def replaceStacks (earlier : List (List Bool)) (replacement rest : List Bool)
    (stk : Stacks (Fin 8)) : Stacks (Fin 8) :=
  Function.update (Function.update stk 2 []) 0 (earlier.flatten ++ (replacement ++ rest))

theorem uniform_flatten_length (earlier : List (List Bool)) (width : ℕ)
    (hrows : ∀ row ∈ earlier, row.length = width) :
    earlier.flatten.length = earlier.length * width := by
  induction earlier with
  | nil => simp
  | cons row earlier ih =>
      have hr := hrows row (by simp)
      have ht : ∀ x ∈ earlier, x.length = width := by
        intro x hx
        exact hrows x (by simp [hx])
      simp only [List.flatten_cons, List.length_append, List.length_cons, hr, ih ht]
      ring

theorem read_eval {r : ℕ} (value present : Fin r) (hvp : value ≠ present)
    (earlier : List (List Bool)) (record rest widthWord indexWord : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin 8))
    (hs : stk 0 = earlier.flatten ++ (record ++ rest)) (hw : stk 3 = widthWord)
    (hi : stk 2 = indexWord) (hiLen : indexWord.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
    (hlen : record.length = widthWord.length)
    (hc : stk 4 = []) (ht : stk 5 = []) (hb : stk 6 = []) (hp : stk 7 = []) :
    Eval (readCmd value present)
      (earlier.length * (14 * widthWord.length + 10) + 15 * widthWord.length + 15)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, readStacks record stk⟩ := by
  have a := saveBefore_eval value present hvp earlier (record ++ rest) widthWord indexWord
    regs stk hs hw hi hiLen hrows hc ht
  have b := readSelected_eval value present hvp record rest widthWord
    (readRegs regs value present none) (savedBeforeStacks earlier (record ++ rest) stk)
    (by simp [savedBeforeStacks]) (by simpa [savedBeforeStacks] using hw) hlen
    (by simpa [savedBeforeStacks] using hc) (by simpa [savedBeforeStacks] using ht)
    (by simpa [savedBeforeStacks] using hb)
  have c := transfer_eval (7 : Fin 8) 0 value present (by decide) hvp
    (readRegs (readRegs regs value present none) value present none)
    (Function.update (savedBeforeStacks earlier (record ++ rest) stk) 1
      (record ++ savedBeforeStacks earlier (record ++ rest) stk 1))
  have hfinal : transferStacks 7 0
      (Function.update (savedBeforeStacks earlier (record ++ rest) stk) 1
        (record ++ savedBeforeStacks earlier (record ++ rest) stk 1)) =
      readStacks record stk := by
    funext j
    fin_cases j <;> simp [transferStacks, savedBeforeStacks, readStacks, hp, hs]
  have hf := uniform_flatten_length earlier widthWord.length hrows
  have t := a.seq (b.seq c)
  simp only [readRegs_reset, hfinal] at t
  dsimp [readCmd]
  convert t using 1 ;
    simp [savedBeforeStacks, hp, hf] ; ring

theorem replace_eval {r : ℕ} (value present : Fin r) (hvp : value ≠ present)
    (earlier : List (List Bool)) (record replacement rest widthWord indexWord : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin 8))
    (hs : stk 0 = earlier.flatten ++ (record ++ rest)) (hn : stk 1 = replacement)
    (hw : stk 3 = widthWord) (hi : stk 2 = indexWord) (hiLen : indexWord.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
    (hlen : record.length = widthWord.length) (hnew : replacement.length = widthWord.length)
    (hc : stk 4 = []) (ht : stk 5 = []) (hb : stk 6 = []) (hp : stk 7 = []) :
    Eval (replaceCmd value present)
      (earlier.length * (14 * widthWord.length + 10) + 20 * widthWord.length + 20)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, replaceStacks earlier replacement rest stk⟩ := by
  have a := saveBefore_eval value present hvp earlier (record ++ rest) widthWord indexWord
    regs stk hs hw hi hiLen hrows hc ht
  have b := replaceSelected_eval value present hvp record replacement rest widthWord
    (readRegs regs value present none) (savedBeforeStacks earlier (record ++ rest) stk)
    (by simp [savedBeforeStacks]) (by simpa [savedBeforeStacks] using hn)
    (by simpa [savedBeforeStacks] using hw) hlen hnew
    (by simpa [savedBeforeStacks] using hc) (by simpa [savedBeforeStacks] using ht)
    (by simpa [savedBeforeStacks] using hb)
  have c := transfer_eval (7 : Fin 8) 0 value present (by decide) hvp
    (readRegs (readRegs regs value present none) value present none)
    (Function.update (savedBeforeStacks earlier (record ++ rest) stk) 0 (replacement ++ rest))
  have hfinal : transferStacks 7 0
      (Function.update (savedBeforeStacks earlier (record ++ rest) stk) 0 (replacement ++ rest)) =
      replaceStacks earlier replacement rest stk := by
    funext j
    fin_cases j <;> simp [transferStacks, savedBeforeStacks, replaceStacks, hp]
  have hf := uniform_flatten_length earlier widthWord.length hrows
  have t := a.seq (b.seq c)
  simp only [readRegs_reset, hfinal] at t
  dsimp [replaceCmd]
  convert t using 1 ;
    simp [savedBeforeStacks, hp, hf] ; ring

/-- The compiled access program has 38 labels for every runtime width/index. -/
abbrev readProgram {r : ℕ} (value present : Fin r) : Program r 8 38 :=
  compiled (readCmd value present) 0 1

/-- The compiled replacement program has 44 labels for every runtime width/index. -/
abbrev replaceProgram {r : ℕ} (value present : Fin r) : Program r 8 44 :=
  compiled (replaceCmd value present) 0 0

/-- Complete execution, including the final halt. -/
theorem readProgram_trace {r : ℕ} (value present : Fin r) (hvp : value ≠ present)
    (earlier : List (List Bool)) (record rest widthWord indexWord : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin 8))
    (hs : stk 0 = earlier.flatten ++ (record ++ rest)) (hw : stk 3 = widthWord)
    (hi : stk 2 = indexWord) (hiLen : indexWord.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
    (hlen : record.length = widthWord.length)
    (hc : stk 4 = []) (ht : stk 5 = []) (hb : stk 6 = []) (hp : stk 7 = []) :
    @Trace r 8 (size (readCmd value present) + 1) (readProgram value present)
      (earlier.length * (14 * widthWord.length + 10) + 15 * widthWord.length + 16)
      ⟨some (readProgram value present).entry, regs, stk⟩
      ⟨none, readRegs regs value present none, readStacks record stk⟩ := by
  have h := compiled_halt_trace
    (read_eval value present hvp earlier record rest widthWord indexWord regs stk
      hs hw hi hiLen hrows hlen hc ht hb hp) 0 1
  have hp' : compiled (readCmd value present) 0 1 = readProgram value present := by rfl
  rw [hp'] at h
  simpa [StructuredProgram.State.withPC, Nat.add_assoc] using h

/-- Complete execution replaces exactly one record and preserves its source word. -/
theorem replaceProgram_trace {r : ℕ} (value present : Fin r) (hvp : value ≠ present)
    (earlier : List (List Bool)) (record replacement rest widthWord indexWord : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin 8))
    (hs : stk 0 = earlier.flatten ++ (record ++ rest)) (hn : stk 1 = replacement)
    (hw : stk 3 = widthWord) (hi : stk 2 = indexWord) (hiLen : indexWord.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
    (hlen : record.length = widthWord.length) (hnew : replacement.length = widthWord.length)
    (hc : stk 4 = []) (ht : stk 5 = []) (hb : stk 6 = []) (hp : stk 7 = []) :
    @Trace r 8 (size (replaceCmd value present) + 1) (replaceProgram value present)
      (earlier.length * (14 * widthWord.length + 10) + 20 * widthWord.length + 21)
      ⟨some (replaceProgram value present).entry, regs, stk⟩
      ⟨none, readRegs regs value present none, replaceStacks earlier replacement rest stk⟩ := by
  have h := compiled_halt_trace
    (replace_eval value present hvp earlier record replacement rest widthWord indexWord regs stk
      hs hn hw hi hiLen hrows hlen hnew hc ht hb hp) 0 0
  have hp' : compiled (replaceCmd value present) 0 0 = replaceProgram value present := by rfl
  rw [hp'] at h
  simpa [StructuredProgram.State.withPC, Nat.add_assoc] using h

@[simp] theorem readStacks_array (record : List Bool) (stk : Stacks (Fin 8)) :
    readStacks record stk 0 = stk 0 := by simp [readStacks]

@[simp] theorem readStacks_output (record : List Bool) (stk : Stacks (Fin 8)) :
    readStacks record stk 1 = record ++ stk 1 := by simp [readStacks]

@[simp] theorem readStacks_index (record : List Bool) (stk : Stacks (Fin 8)) :
    readStacks record stk 2 = [] := by simp [readStacks]

/-- This frames the complete array, width, and all four scratch stacks. -/
theorem readStacks_frame (record : List Bool) (stk : Stacks (Fin 8)) (j : Fin 8)
    (h1 : j ≠ 1) (h2 : j ≠ 2) : readStacks record stk j = stk j := by
  simp [readStacks, h1, h2]

@[simp] theorem replaceStacks_array (earlier : List (List Bool))
    (replacement rest : List Bool) (stk : Stacks (Fin 8)) :
    replaceStacks earlier replacement rest stk 0 =
      earlier.flatten ++ (replacement ++ rest) := by simp [replaceStacks]

@[simp] theorem replaceStacks_word (earlier : List (List Bool))
    (replacement rest : List Bool) (stk : Stacks (Fin 8)) :
    replaceStacks earlier replacement rest stk 1 = stk 1 := by simp [replaceStacks]

@[simp] theorem replaceStacks_index (earlier : List (List Bool))
    (replacement rest : List Bool) (stk : Stacks (Fin 8)) :
    replaceStacks earlier replacement rest stk 2 = [] := by simp [replaceStacks]

/-- This frames the replacement word, width, and all four scratch stacks. -/
theorem replaceStacks_frame (earlier : List (List Bool)) (replacement rest : List Bool)
    (stk : Stacks (Fin 8)) (j : Fin 8) (h0 : j ≠ 0) (h2 : j ≠ 2) :
    replaceStacks earlier replacement rest stk j = stk j := by
  simp [replaceStacks, h0, h2]

/-- In record-list notation the resulting array has exactly the specified
replacement, with the entire lists of preceding and following records intact. -/
theorem replaceStacks_records (earlier later : List (List Bool)) (replacement : List Bool)
    (stk : Stacks (Fin 8)) :
    replaceStacks earlier replacement later.flatten stk 0 =
      (earlier ++ replacement :: later).flatten := by
  simp [replaceStacks, List.flatten_append, List.flatten_cons]

theorem replaceStacks_length (earlier : List (List Bool)) (record replacement rest : List Bool)
    (stk : Stacks (Fin 8)) (hs : stk 0 = earlier.flatten ++ (record ++ rest))
    (hlen : replacement.length = record.length) :
    (replaceStacks earlier replacement rest stk 0).length = (stk 0).length := by
  simp [replaceStacks, hs, hlen]

theorem result_register_frame {r : ℕ} (value present j : Fin r) (regs : Fin r → Bool)
    (hv : j ≠ value) (hp : j ≠ present) :
    readRegs regs value present none j = regs j :=
  readRegs_frame regs value present j none hv hp

/-- The separate verified compiler gives an actual binary-machine execution.
Its multiplier depends only on this fixed program, not on the array data. -/
theorem readProgram_primitive {r : ℕ} (value present : Fin r) (hvp : value ≠ present)
    (earlier : List (List Bool)) (record rest widthWord indexWord : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin 8))
    (hs : stk 0 = earlier.flatten ++ (record ++ rest)) (hw : stk 3 = widthWord)
    (hi : stk 2 = indexWord) (hiLen : indexWord.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
    (hlen : record.length = widthWord.length)
    (hc : stk 4 = []) (ht : stk 5 = []) (hb : stk 6 = []) (hp : stk 7 = []) :
    Computation.RunsIn (primitive (readProgram value present)).step
      (primitiveOverhead (readProgram value present) *
        (earlier.length * (14 * widthWord.length + 10) + 15 * widthWord.length + 16))
      (primitiveCfg (readProgram value present) ⟨some (readProgram value present).entry, regs, stk⟩)
      (primitiveCfg (readProgram value present)
        ⟨none, readRegs regs value present none, readStacks record stk⟩) :=
  primitive_trace _ (readProgram_trace value present hvp earlier record rest widthWord indexWord
    regs stk hs hw hi hiLen hrows hlen hc ht hb hp)

theorem replaceProgram_primitive {r : ℕ} (value present : Fin r) (hvp : value ≠ present)
    (earlier : List (List Bool)) (record replacement rest widthWord indexWord : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin 8))
    (hs : stk 0 = earlier.flatten ++ (record ++ rest)) (hn : stk 1 = replacement)
    (hw : stk 3 = widthWord) (hi : stk 2 = indexWord) (hiLen : indexWord.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
    (hlen : record.length = widthWord.length) (hnew : replacement.length = widthWord.length)
    (hc : stk 4 = []) (ht : stk 5 = []) (hb : stk 6 = []) (hp : stk 7 = []) :
    Computation.RunsIn (primitive (replaceProgram value present)).step
      (primitiveOverhead (replaceProgram value present) *
        (earlier.length * (14 * widthWord.length + 10) + 20 * widthWord.length + 21))
      (primitiveCfg (replaceProgram value present)
        ⟨some (replaceProgram value present).entry, regs, stk⟩)
      (primitiveCfg (replaceProgram value present)
        ⟨none, readRegs regs value present none, replaceStacks earlier replacement rest stk⟩) :=
  primitive_trace _ (replaceProgram_trace value present hvp earlier record replacement rest
    widthWord indexWord regs stk hs hn hw hi hiLen hrows hlen hnew hc ht hb hp)

end SubexponentialSAT.ArrayUpdatePrograms

end OAI.Algorithms
