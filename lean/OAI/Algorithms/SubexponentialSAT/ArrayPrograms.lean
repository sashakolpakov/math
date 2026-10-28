import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace OAI.Algorithms

/-!
# Dynamic counted operations on Boolean stacks

The counter is a stack whose *length* is the requested number of bits. Its bit
values are ignored. In particular, bounds are data, not control-label counts.
-/

namespace SubexponentialSAT.ArrayPrograms

open BitProgram StackRoutines

/-- Exact result of consuming a counted segment and reversing it onto `dst`. -/
def countedTransferStacks {s : ℕ} (counter src dst : Fin s) (segment rest : List Bool)
    (stk : Stacks (Fin s)) : Stacks (Fin s) :=
  Function.update (Function.update (Function.update stk counter []) src rest)
    dst (segment.reverse ++ stk dst)

def countedTransferResult {r s l : ℕ} (exit : Fin l) (counter src dst : Fin s)
    (value present : Fin r) (segment rest : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) : Cfg r s l :=
  ⟨some exit, readRegs regs value present none,
    countedTransferStacks counter src dst segment rest stk⟩

theorem countedTransferStacks_step {s : ℕ} (counter src dst : Fin s)
    (a : Bool) (segment rest counterTail : List Bool) (stk : Stacks (Fin s))
    (hcs : counter ≠ src) (hcd : counter ≠ dst) (hsd : src ≠ dst) :
    countedTransferStacks counter src dst segment rest
        (Function.update
          (Function.update (Function.update stk counter counterTail) src (segment ++ rest))
          dst (a :: stk dst)) =
      countedTransferStacks counter src dst (a :: segment) rest stk := by
  funext j
  by_cases hd : j = dst
  · subst j
    simp [countedTransferStacks, List.reverse_cons, List.append_assoc]
  · by_cases hs : j = src
    · subst j
      simp [countedTransferStacks, hsd]
    · by_cases hc : j = counter
      · subst j
        simp [countedTransferStacks, hcs, hcd]
      · simp [countedTransferStacks, hc, hs, hd]

/-- The counter controls a fixed four-instruction loop. The precondition names
the segment it will consume, and proves the source contains enough data. -/
theorem counted_transfer_trace {r s l : ℕ} (p : Program r s l)
    (counter src dst : Fin s) (value present : Fin r)
    (loop check read put exit : Fin l)
    (hcs : counter ≠ src) (hcd : counter ≠ dst) (hsd : src ≠ dst)
    (hvp : value ≠ present)
    (hloop : p.code loop = .pop counter value present check)
    (hcheck : p.code check = .branch present read exit)
    (hread : p.code read = .pop src value present put)
    (hput : p.code put = .push dst value loop)
    (segment rest countWord : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hsrc : stk src = segment ++ rest) (hcounter : stk counter = countWord)
    (hcount : countWord.length = segment.length) :
    Trace p (4 * segment.length + 2) ⟨some loop, regs, stk⟩
      (countedTransferResult exit counter src dst value present segment rest regs stk) := by
  induction segment generalizing countWord regs stk with
  | nil =>
      have hc : countWord = [] := List.length_eq_zero_iff.mp (by simpa using hcount)
      subst countWord
      have hs : stk src = rest := by simpa using hsrc
      have hst : countedTransferStacks counter src dst [] rest stk =
          Function.update stk counter [] := by
        funext j
        by_cases hd : j = dst
        · subst j; simp [countedTransferStacks, hcd.symm]
        · by_cases hj : j = src
          · subst j; simp [countedTransferStacks, hs, hcs.symm, hsd]
          · simp [countedTransferStacks, hd, hj]
      refine .cons (b := ⟨some check, readRegs regs value present none,
        Function.update stk counter []⟩) ?_ ?_
      · simp [step, hloop, execInstr, hc]
      · refine .cons (b := countedTransferResult exit counter src dst value present [] rest regs stk)
          ?_ (.refl _)
        simp [step, hcheck, execInstr, countedTransferResult, hst, readRegs_present]
  | cons a segment ih =>
      cases countWord with
      | nil => simp at hcount
      | cons bit countTail =>
          have hlen : countTail.length = segment.length := by simpa using hcount
          let regs₁ := readRegs regs value present (some bit)
          let regs₂ := readRegs regs₁ value present (some a)
          let stk₁ := Function.update stk counter countTail
          let stk₂ := Function.update stk₁ src (segment ++ rest)
          let stk₃ := Function.update stk₂ dst (a :: stk dst)
          have hs' : stk₃ src = segment ++ rest := by simp [stk₃, stk₂, hsd]
          have hc' : stk₃ counter = countTail := by simp [stk₃, stk₂, stk₁, hcs, hcd]
          have ht := ih countTail regs₂ stk₃ hs' hc' hlen
          have hst := countedTransferStacks_step counter src dst a segment rest countTail stk
            hcs hcd hsd
          have ht' : Trace p (4 * segment.length + 2) ⟨some loop, regs₂, stk₃⟩
              (countedTransferResult exit counter src dst value present (a :: segment) rest regs stk) := by
            simpa only [countedTransferResult, regs₂, regs₁, readRegs_reset, stk₃, stk₂, stk₁,
              hst] using ht
          have total : Trace p (4 * segment.length + 2 + 1 + 1 + 1 + 1)
              ⟨some loop, regs, stk⟩
              (countedTransferResult exit counter src dst value present (a :: segment) rest regs stk) := by
            refine .cons (b := ⟨some check, regs₁, stk₁⟩) ?_ ?_
            · simp [step, hloop, execInstr, hcounter, regs₁, stk₁]
            · refine .cons (b := ⟨some read, regs₁, stk₁⟩) ?_ ?_
              · simp [step, hcheck, execInstr, regs₁, readRegs_present]
              · refine .cons (b := ⟨some put, regs₂, stk₂⟩) ?_ ?_
                · simp [step, hread, execInstr, regs₂, stk₂, stk₁, hcs.symm, hsrc]
                · refine .cons (b := ⟨some loop, regs₂, stk₃⟩) ?_ ht'
                  simp [step, hput, execInstr, regs₂, stk₃, stk₂, stk₁,
                    readRegs_value, hvp, hsd.symm, hcd.symm]
          simpa only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using total

abbrev countedTransferProgram {r s : ℕ} (counter src dst : Fin s)
    (value present : Fin r) : Program r s 5 where
  inputStack := src
  outputStack := dst
  entry := 0
  code := ![.pop counter value present 1, .branch present 2 4,
    .pop src value present 3, .push dst value 0, .halt]

theorem countedTransferProgram_trace {r s : ℕ} (counter src dst : Fin s)
    (value present : Fin r) (hcs : counter ≠ src) (hcd : counter ≠ dst) (hsd : src ≠ dst)
    (hvp : value ≠ present) (segment rest countWord : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hsrc : stk src = segment ++ rest) (hcounter : stk counter = countWord)
    (hcount : countWord.length = segment.length) :
    Trace (countedTransferProgram counter src dst value present) (4 * segment.length + 2)
      ⟨some 0, regs, stk⟩
      (countedTransferResult 4 counter src dst value present segment rest regs stk) :=
  counted_transfer_trace _ counter src dst value present 0 1 2 3 4 hcs hcd hsd hvp
    rfl rfl rfl rfl segment rest countWord regs stk hsrc hcounter hcount

def countedSkipStacks {s : ℕ} (counter src : Fin s) (rest : List Bool)
    (stk : Stacks (Fin s)) : Stacks (Fin s) :=
  Function.update (Function.update stk counter []) src rest

def countedSkipResult {r s l : ℕ} (exit : Fin l) (counter src : Fin s)
    (value present : Fin r) (rest : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) : Cfg r s l :=
  ⟨some exit, readRegs regs value present none, countedSkipStacks counter src rest stk⟩

theorem clear_after_countedTransfer {s : ℕ} (counter src tmp : Fin s)
    (segment rest : List Bool) (stk : Stacks (Fin s))
    (hct : counter ≠ tmp) (hst : src ≠ tmp) (htmp : stk tmp = []) :
    clearStacks tmp (countedTransferStacks counter src tmp segment rest stk) =
      countedSkipStacks counter src rest stk := by
  funext j
  by_cases ht : j = tmp
  · subst j; simp [clearStacks, countedTransferStacks, countedSkipStacks,
      hct.symm, hst.symm, htmp]
  · simp [clearStacks, countedTransferStacks, countedSkipStacks, ht]

/-- Skip precisely the number of data bits supplied by a unary counter,
restoring the initially empty discard buffer. -/
theorem counted_skip_trace {r s l : ℕ} (p : Program r s l)
    (counter src tmp : Fin s) (value present : Fin r)
    (loop check read put clearLoop clearCheck exit : Fin l)
    (hcs : counter ≠ src) (hct : counter ≠ tmp) (hst : src ≠ tmp) (hvp : value ≠ present)
    (h₀ : p.code loop = .pop counter value present check)
    (h₁ : p.code check = .branch present read clearLoop)
    (h₂ : p.code read = .pop src value present put)
    (h₃ : p.code put = .push tmp value loop)
    (h₄ : p.code clearLoop = .pop tmp value present clearCheck)
    (h₅ : p.code clearCheck = .branch present clearLoop exit)
    (segment rest countWord : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hsrc : stk src = segment ++ rest) (hcounter : stk counter = countWord)
    (hcount : countWord.length = segment.length) (htmp : stk tmp = []) :
    Trace p (6 * segment.length + 4) ⟨some loop, regs, stk⟩
      (countedSkipResult exit counter src value present rest regs stk) := by
  have t₁ := counted_transfer_trace p counter src tmp value present loop check read put clearLoop
    hcs hct hst hvp h₀ h₁ h₂ h₃ segment rest countWord regs stk hsrc hcounter hcount
  have t₂ := clear_trace p tmp value present clearLoop clearCheck exit h₄ h₅
    (readRegs regs value present none) (countedTransferStacks counter src tmp segment rest stk)
  have hlen : (countedTransferStacks counter src tmp segment rest stk tmp).length = segment.length := by
    simp [countedTransferStacks, htmp]
  have hfinal := clear_after_countedTransfer counter src tmp segment rest stk hct hst htmp
  have t₂' : Trace p (2 * segment.length + 2)
      (countedTransferResult clearLoop counter src tmp value present segment rest regs stk)
      (countedSkipResult exit counter src value present rest regs stk) := by
    simpa only [hlen, clearResult, countedTransferResult, countedSkipResult,
      readRegs_reset, hfinal] using t₂
  have total := t₁.trans t₂'
  convert total using 1 ; omega

abbrev countedSkipProgram {r s : ℕ} (counter src tmp : Fin s)
    (value present : Fin r) : Program r s 7 where
  inputStack := src
  outputStack := src
  entry := 0
  code := ![.pop counter value present 1, .branch present 2 4,
    .pop src value present 3, .push tmp value 0,
    .pop tmp value present 5, .branch present 4 6, .halt]

theorem countedSkipProgram_trace {r s : ℕ} (counter src tmp : Fin s)
    (value present : Fin r) (hcs : counter ≠ src) (hct : counter ≠ tmp) (hst : src ≠ tmp)
    (hvp : value ≠ present) (segment rest countWord : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hsrc : stk src = segment ++ rest) (hcounter : stk counter = countWord)
    (hcount : countWord.length = segment.length) (htmp : stk tmp = []) :
    Trace (countedSkipProgram counter src tmp value present) (6 * segment.length + 4)
      ⟨some 0, regs, stk⟩ (countedSkipResult 6 counter src value present rest regs stk) :=
  counted_skip_trace _ counter src tmp value present 0 1 2 3 4 5 6 hcs hct hst hvp
    rfl rfl rfl rfl rfl rfl segment rest countWord regs stk hsrc hcounter hcount htmp

def countedCopyStacks {s : ℕ} (counter dst : Fin s) (segment : List Bool)
    (stk : Stacks (Fin s)) : Stacks (Fin s) :=
  Function.update (Function.update stk counter []) dst (segment ++ stk dst)

def countedCopyResult {r s l : ℕ} (exit : Fin l) (counter dst : Fin s)
    (value present : Fin r) (segment : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) : Cfg r s l :=
  ⟨some exit, readRegs regs value present none, countedCopyStacks counter dst segment stk⟩

theorem fanout_after_countedTransfer {s : ℕ} (counter src dst tmp : Fin s)
    (segment rest : List Bool) (stk : Stacks (Fin s))
    (hcs : counter ≠ src) (hcd : counter ≠ dst) (hct : counter ≠ tmp)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (hsrc : stk src = segment ++ rest) (htmp : stk tmp = []) :
    fanoutStacks tmp src dst (countedTransferStacks counter src tmp segment rest stk) =
      countedCopyStacks counter dst segment stk := by
  funext j
  by_cases hd : j = dst
  · subst j
    simp [fanoutStacks, countedTransferStacks, countedCopyStacks,
      hcd.symm, hsd.symm, htd.symm, htmp]
  · by_cases hs : j = src
    · subst j
      simp [fanoutStacks, countedTransferStacks, countedCopyStacks,
        hsd, hst, hcs.symm, htmp, hsrc]
    · by_cases ht : j = tmp
      · subst j
        simp [fanoutStacks, countedTransferStacks, countedCopyStacks, hst, htd,
          hct.symm, hst.symm, htmp]
      · by_cases hc : j = counter
        · subst j
          simp [fanoutStacks, countedTransferStacks, countedCopyStacks, hcs, hcd, hct]
        · simp [fanoutStacks, countedTransferStacks, countedCopyStacks, hd, hs, ht, hc]

/-- Counted preserving copy. Only the unary counter and destination change in
the final state; the source and temporary buffer are restored exactly. -/
theorem counted_copy_trace {r s l : ℕ} (p : Program r s l)
    (counter src dst tmp : Fin s) (value present : Fin r)
    (loop check read put copyLoop copyCheck copyPut₁ copyPut₂ exit : Fin l)
    (hcs : counter ≠ src) (hcd : counter ≠ dst) (hct : counter ≠ tmp)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (hvp : value ≠ present)
    (h₀ : p.code loop = .pop counter value present check)
    (h₁ : p.code check = .branch present read copyLoop)
    (h₂ : p.code read = .pop src value present put)
    (h₃ : p.code put = .push tmp value loop)
    (h₄ : p.code copyLoop = .pop tmp value present copyCheck)
    (h₅ : p.code copyCheck = .branch present copyPut₁ exit)
    (h₆ : p.code copyPut₁ = .push src value copyPut₂)
    (h₇ : p.code copyPut₂ = .push dst value copyLoop)
    (segment rest countWord : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hsrc : stk src = segment ++ rest) (hcounter : stk counter = countWord)
    (hcount : countWord.length = segment.length) (htmp : stk tmp = []) :
    Trace p (8 * segment.length + 4) ⟨some loop, regs, stk⟩
      (countedCopyResult exit counter dst value present segment regs stk) := by
  have t₁ := counted_transfer_trace p counter src tmp value present loop check read put copyLoop
    hcs hct hst hvp h₀ h₁ h₂ h₃ segment rest countWord regs stk hsrc hcounter hcount
  have t₂ := fanout_trace p tmp src dst value present copyLoop copyCheck copyPut₁ copyPut₂ exit
    hst.symm htd hsd hvp h₄ h₅ h₆ h₇ (readRegs regs value present none)
    (countedTransferStacks counter src tmp segment rest stk)
  have hlen : (countedTransferStacks counter src tmp segment rest stk tmp).length = segment.length := by
    simp [countedTransferStacks, htmp]
  have hfinal := fanout_after_countedTransfer counter src dst tmp segment rest stk
    hcs hcd hct hsd hst htd hsrc htmp
  have t₂' : Trace p (4 * segment.length + 2)
      (countedTransferResult copyLoop counter src tmp value present segment rest regs stk)
      (countedCopyResult exit counter dst value present segment regs stk) := by
    simpa only [hlen, fanoutResult, countedTransferResult, countedCopyResult,
      readRegs_reset, hfinal] using t₂
  have total := t₁.trans t₂'
  convert total using 1 ; omega

abbrev countedCopyProgram {r s : ℕ} (counter src dst tmp : Fin s)
    (value present : Fin r) : Program r s 9 where
  inputStack := src
  outputStack := dst
  entry := 0
  code := ![.pop counter value present 1, .branch present 2 4,
    .pop src value present 3, .push tmp value 0,
    .pop tmp value present 5, .branch present 6 8,
    .push src value 7, .push dst value 4, .halt]

theorem countedCopyProgram_trace {r s : ℕ} (counter src dst tmp : Fin s)
    (value present : Fin r) (hcs : counter ≠ src) (hcd : counter ≠ dst) (hct : counter ≠ tmp)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (hvp : value ≠ present)
    (segment rest countWord : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hsrc : stk src = segment ++ rest) (hcounter : stk counter = countWord)
    (hcount : countWord.length = segment.length) (htmp : stk tmp = []) :
    Trace (countedCopyProgram counter src dst tmp value present) (8 * segment.length + 4)
      ⟨some 0, regs, stk⟩ (countedCopyResult 8 counter dst value present segment regs stk) :=
  counted_copy_trace _ counter src dst tmp value present 0 1 2 3 4 5 6 7 8
    hcs hcd hct hsd hst htd hvp rfl rfl rfl rfl rfl rfl rfl rfl
    segment rest countWord regs stk hsrc hcounter hcount htmp

/-! ## Indexed fixed-width records

The seven stacks are: source 0, output 1, unary index 2, unary width 3,
temporary counter 4, copy scratch 5, and data scratch 6. Their contents can be
arbitrarily long. The program always has exactly 31 control labels.
-/

abbrev lookupProgram {r : ℕ} (value present : Fin r) : Program r 7 31 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code := ![
    .pop 2 value present 1, .branch present 2 15,
    .pop 3 value present 3, .branch present 4 5, .push 5 value 2,
    .pop 5 value present 6, .branch present 7 9, .push 3 value 8, .push 4 value 5,
    .pop 4 value present 10, .branch present 11 13, .pop 0 value present 12,
    .push 6 value 9, .pop 6 value present 14, .branch present 13 0,
    .pop 3 value present 16, .branch present 17 18, .push 5 value 15,
    .pop 5 value present 19, .branch present 20 22, .push 3 value 21, .push 4 value 18,
    .pop 4 value present 23, .branch present 24 26, .pop 0 value present 25,
    .push 6 value 22, .pop 6 value present 27, .branch present 28 30,
    .push 0 value 29, .push 1 value 26, .halt]

/-- One dynamic-width skip inside the lookup program. The width is preserved,
and all three scratch stacks return to empty. -/
theorem lookup_skip_record_trace {r : ℕ} (value present : Fin r) (hvp : value ≠ present)
    (record rest widthWord : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin 7))
    (hsrc : stk 0 = record ++ rest) (hwidth : stk 3 = widthWord)
    (hlen : record.length = widthWord.length)
    (hc : stk 4 = []) (ht : stk 5 = []) (hb : stk 6 = []) :
    Trace (lookupProgram value present) (13 * widthWord.length + 8)
      ⟨some 2, regs, stk⟩
      ⟨some 0, readRegs regs value present none, Function.update stk 0 rest⟩ := by
  let p := lookupProgram value present
  let stk₁ := copyStacks 3 4 stk
  let regs₁ := readRegs regs value present none
  have t₁ := copy_trace p 3 4 5 value present 2 3 4 5 6 7 8 9
    (by decide) (by decide) (by decide) hvp rfl rfl rfl rfl rfl rfl rfl regs stk ht
  have hs₁ : stk₁ 0 = record ++ rest := by simpa [stk₁, copyStacks] using hsrc
  have hc₁ : stk₁ 4 = widthWord := by simp [stk₁, copyStacks, hc, hwidth]
  have hb₁ : stk₁ 6 = [] := by simpa [stk₁, copyStacks] using hb
  have t₂ := counted_skip_trace p 4 0 6 value present 9 10 11 12 13 14 0
    (by decide) (by decide) (by decide) hvp rfl rfl rfl rfl rfl rfl
    record rest widthWord regs₁ stk₁ hs₁ hc₁ hlen.symm hb₁
  have hfinal : countedSkipStacks 4 0 rest stk₁ = Function.update stk 0 rest := by
    funext j
    by_cases hj : j = 0
    · subst j; simp [countedSkipStacks]
    · by_cases h4 : j = 4
      · subst j; simp [countedSkipStacks, hc]
      · simp [countedSkipStacks, stk₁, copyStacks, hj, h4]
  have t₂' : Trace p (6 * widthWord.length + 4)
      (copyResult 9 3 4 value present regs stk)
      ⟨some 0, readRegs regs value present none, Function.update stk 0 rest⟩ := by
    simpa only [hlen, copyResult, countedSkipResult, regs₁, readRegs_reset, hfinal] using t₂
  have total := t₁.trans t₂'
  rw [hwidth] at total
  convert total using 1 ; omega

/-- Copy the selected record, preserving the width and source and restoring all
scratch stacks. The selected record is returned in forward order. -/
theorem lookup_take_record_trace {r : ℕ} (value present : Fin r) (hvp : value ≠ present)
    (record rest widthWord : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin 7))
    (hsrc : stk 0 = record ++ rest) (hwidth : stk 3 = widthWord)
    (hlen : record.length = widthWord.length)
    (hc : stk 4 = []) (ht : stk 5 = []) (hb : stk 6 = []) :
    Trace (lookupProgram value present) (15 * widthWord.length + 8)
      ⟨some 15, regs, stk⟩
      ⟨some 30, readRegs regs value present none, Function.update stk 1 (record ++ stk 1)⟩ := by
  let p := lookupProgram value present
  let stk₁ := copyStacks 3 4 stk
  let regs₁ := readRegs regs value present none
  have t₁ := copy_trace p 3 4 5 value present 15 16 17 18 19 20 21 22
    (by decide) (by decide) (by decide) hvp rfl rfl rfl rfl rfl rfl rfl regs stk ht
  have hs₁ : stk₁ 0 = record ++ rest := by simpa [stk₁, copyStacks] using hsrc
  have hc₁ : stk₁ 4 = widthWord := by simp [stk₁, copyStacks, hc, hwidth]
  have hb₁ : stk₁ 6 = [] := by simpa [stk₁, copyStacks] using hb
  have t₂ := counted_copy_trace p 4 0 1 6 value present 22 23 24 25 26 27 28 29 30
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hvp
    rfl rfl rfl rfl rfl rfl rfl rfl record rest widthWord regs₁ stk₁
    hs₁ hc₁ hlen.symm hb₁
  have hfinal : countedCopyStacks 4 1 record stk₁ = Function.update stk 1 (record ++ stk 1) := by
    funext j
    by_cases hj : j = 1
    · subst j; simp [countedCopyStacks, stk₁, copyStacks]
    · by_cases h4 : j = 4
      · subst j; simp [countedCopyStacks, hc]
      · simp [countedCopyStacks, stk₁, copyStacks, hj, h4]
  have t₂' : Trace p (8 * widthWord.length + 4)
      (copyResult 22 3 4 value present regs stk)
      ⟨some 30, readRegs regs value present none, Function.update stk 1 (record ++ stk 1)⟩ := by
    simpa only [hlen, copyResult, countedCopyResult, regs₁, readRegs_reset, hfinal] using t₂
  have total := t₁.trans t₂'
  rw [hwidth] at total
  convert total using 1 ; omega

/-- The source is left at the selected record, the selected record is prefixed
to output, and the unary index is consumed. -/
def lookupStacks (record rest : List Bool) (stk : Stacks (Fin 7)) : Stacks (Fin 7) :=
  Function.update
    (Function.update (Function.update stk 2 []) 0 (record ++ rest))
    1 (record ++ stk 1)

def lookupResult {r : ℕ} (value present : Fin r) (record rest : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin 7)) : Cfg r 7 31 :=
  ⟨some 30, readRegs regs value present none, lookupStacks record rest stk⟩

theorem lookupStacks_overwrite (record rest junk indexTail : List Bool)
    (stk : Stacks (Fin 7)) :
    lookupStacks record rest (Function.update (Function.update stk 2 indexTail) 0 junk) =
      lookupStacks record rest stk := by
  funext j
  by_cases h1 : j = 1
  · subst j; simp [lookupStacks]
  · by_cases h0 : j = 0
    · subst j; simp [lookupStacks]
    · by_cases h2 : j = 2
      · subst j; simp [lookupStacks]
      · simp [lookupStacks, h1, h0, h2]

theorem lookupStacks_at_record (record rest : List Bool) (stk : Stacks (Fin 7))
    (hs : stk 0 = record ++ rest) (hi : stk 2 = []) :
    lookupStacks record rest stk = Function.update stk 1 (record ++ stk 1) := by
  funext j
  by_cases h1 : j = 1
  · subst j; simp [lookupStacks]
  · by_cases h0 : j = 0
    · subst j; simp [lookupStacks, hs]
    · by_cases h2 : j = 2
      · subst j; simp [lookupStacks, hi]
      · simp [lookupStacks, h1, h0, h2]

/-- Actual dynamic-width, dynamic-index lookup. `earlier` describes the records
preceding the requested record. Both its length and the common record width are
represented by stack data; the program has 31 labels for every input. -/
theorem lookupProgram_trace {r : ℕ} (value present : Fin r) (hvp : value ≠ present)
    (earlier : List (List Bool)) (record rest widthWord indexWord : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin 7))
    (hsrc : stk 0 = earlier.flatten ++ (record ++ rest))
    (hwidth : stk 3 = widthWord) (hindex : stk 2 = indexWord)
    (hindexLen : indexWord.length = earlier.length)
    (hearlier : ∀ row ∈ earlier, row.length = widthWord.length)
    (hrecord : record.length = widthWord.length)
    (hc : stk 4 = []) (ht : stk 5 = []) (hb : stk 6 = []) :
    Trace (lookupProgram value present)
      (earlier.length * (13 * widthWord.length + 10) + 15 * widthWord.length + 10)
      ⟨some 0, regs, stk⟩ (lookupResult value present record rest regs stk) := by
  induction earlier generalizing indexWord regs stk with
  | nil =>
      have hnil : indexWord = [] := List.length_eq_zero_iff.mp (by simpa using hindexLen)
      have hi : stk 2 = [] := hindex.trans hnil
      have hs : stk 0 = record ++ rest := by simpa using hsrc
      have hupd : Function.update stk 2 [] = stk := by
        funext j
        by_cases hj : j = 2
        · subst j; simp [hi]
        · simp [hj]
      let regs₁ := readRegs regs value present none
      have take := lookup_take_record_trace value present hvp record rest widthWord regs₁ stk
        hs hwidth hrecord hc ht hb
      have hfinal := lookupStacks_at_record record rest stk hs hi
      have take' : Trace (lookupProgram value present) (15 * widthWord.length + 8)
          ⟨some 15, regs₁, stk⟩ (lookupResult value present record rest regs stk) := by
        simpa only [lookupResult, regs₁, readRegs_reset, hfinal] using take
      have total : Trace (lookupProgram value present) (15 * widthWord.length + 8 + 1 + 1)
          ⟨some 0, regs, stk⟩ (lookupResult value present record rest regs stk) := by
        refine .cons (b := ⟨some 1, regs₁, stk⟩) ?_ ?_
        · simp [step, execInstr, hi, hupd, regs₁]
        · refine .cons (b := ⟨some 15, regs₁, stk⟩) ?_ take'
          simp [step, execInstr, regs₁, readRegs_present]
      simpa only [List.length_nil, Nat.zero_mul, Nat.zero_add, Nat.add_assoc] using total
  | cons row earlier ih =>
      cases indexWord with
      | nil => simp at hindexLen
      | cons bit indexTail =>
          have hiLen : indexTail.length = earlier.length := by simpa using hindexLen
          have hrow : row.length = widthWord.length := hearlier row (by simp)
          have hrows : ∀ x ∈ earlier, x.length = widthWord.length := by
            intro x hx
            exact hearlier x (by simp [hx])
          let regs₁ := readRegs regs value present (some bit)
          let regs₂ := readRegs regs₁ value present none
          let stk₁ := Function.update stk 2 indexTail
          let stk₂ := Function.update stk₁ 0 (earlier.flatten ++ (record ++ rest))
          have hs₁ : stk₁ 0 = row ++ (earlier.flatten ++ (record ++ rest)) := by
            simpa [stk₁, List.flatten_cons, List.append_assoc] using hsrc
          have hw₁ : stk₁ 3 = widthWord := by simpa [stk₁] using hwidth
          have hc₁ : stk₁ 4 = [] := by simpa [stk₁] using hc
          have ht₁ : stk₁ 5 = [] := by simpa [stk₁] using ht
          have hb₁ : stk₁ 6 = [] := by simpa [stk₁] using hb
          have skip := lookup_skip_record_trace value present hvp row
            (earlier.flatten ++ (record ++ rest)) widthWord regs₁ stk₁
            hs₁ hw₁ hrow hc₁ ht₁ hb₁
          have hs₂ : stk₂ 0 = earlier.flatten ++ (record ++ rest) := by simp [stk₂]
          have hw₂ : stk₂ 3 = widthWord := by simpa [stk₂, stk₁] using hwidth
          have hi₂ : stk₂ 2 = indexTail := by simp [stk₂, stk₁]
          have hc₂ : stk₂ 4 = [] := by simpa [stk₂, stk₁] using hc
          have ht₂ : stk₂ 5 = [] := by simpa [stk₂, stk₁] using ht
          have hb₂ : stk₂ 6 = [] := by simpa [stk₂, stk₁] using hb
          have tail := ih indexTail regs₂ stk₂ hs₂ hw₂ hi₂ hiLen hrows hc₂ ht₂ hb₂
          have hfinal := lookupStacks_overwrite record rest
            (earlier.flatten ++ (record ++ rest)) indexTail stk
          have tail' : Trace (lookupProgram value present)
              (earlier.length * (13 * widthWord.length + 10) + 15 * widthWord.length + 10)
              ⟨some 0, regs₂, stk₂⟩ (lookupResult value present record rest regs stk) := by
            simpa only [lookupResult, regs₂, regs₁, readRegs_reset, stk₂, stk₁, hfinal] using tail
          have segment := skip.trans tail'
          have total : Trace (lookupProgram value present)
              ((13 * widthWord.length + 8 +
                (earlier.length * (13 * widthWord.length + 10) + 15 * widthWord.length + 10)) + 1 + 1)
              ⟨some 0, regs, stk⟩ (lookupResult value present record rest regs stk) := by
            refine .cons (b := ⟨some 1, regs₁, stk₁⟩) ?_ ?_
            · simp [step, execInstr, hindex, regs₁, stk₁]
            · refine .cons (b := ⟨some 2, regs₁, stk₁⟩) ?_ segment
              simp [step, execInstr, regs₁, readRegs_present]
          convert total using 1 ; simp only [List.length_cons] ; ring

theorem countedTransferResult_stack_frame {r s l : ℕ} (exit : Fin l)
    (counter src dst j : Fin s) (value present : Fin r) (segment rest : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hc : j ≠ counter) (hs : j ≠ src) (hd : j ≠ dst) :
    (countedTransferResult exit counter src dst value present segment rest regs stk).stacks j =
      stk j := by
  simp [countedTransferResult, countedTransferStacks, hc, hs, hd]

theorem countedSkipResult_stack_frame {r s l : ℕ} (exit : Fin l)
    (counter src j : Fin s) (value present : Fin r) (rest : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) (hc : j ≠ counter) (hs : j ≠ src) :
    (countedSkipResult exit counter src value present rest regs stk).stacks j = stk j := by
  simp [countedSkipResult, countedSkipStacks, hc, hs]

theorem countedCopyResult_stack_frame {r s l : ℕ} (exit : Fin l)
    (counter dst j : Fin s) (value present : Fin r) (segment : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) (hc : j ≠ counter) (hd : j ≠ dst) :
    (countedCopyResult exit counter dst value present segment regs stk).stacks j = stk j := by
  simp [countedCopyResult, countedCopyStacks, hc, hd]

@[simp] theorem lookupResult_source {r : ℕ} (value present : Fin r) (record rest : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin 7)) :
    (lookupResult value present record rest regs stk).stacks 0 = record ++ rest := by
  simp [lookupResult, lookupStacks]

@[simp] theorem lookupResult_output {r : ℕ} (value present : Fin r) (record rest : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin 7)) :
    (lookupResult value present record rest regs stk).stacks 1 = record ++ stk 1 := by
  simp [lookupResult, lookupStacks]

@[simp] theorem lookupResult_index {r : ℕ} (value present : Fin r) (record rest : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin 7)) :
    (lookupResult value present record rest regs stk).stacks 2 = [] := by
  simp [lookupResult, lookupStacks]

theorem lookupResult_stack_frame {r : ℕ} (value present : Fin r) (record rest : List Bool)
    (regs : Fin r → Bool) (stk : Stacks (Fin 7)) (j : Fin 7)
    (h0 : j ≠ 0) (h1 : j ≠ 1) (h2 : j ≠ 2) :
    (lookupResult value present record rest regs stk).stacks j = stk j := by
  simp [lookupResult, lookupStacks, h0, h1, h2]

theorem lookupResult_register_frame {r : ℕ} (value present j : Fin r)
    (record rest : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin 7))
    (hv : j ≠ value) (hp : j ≠ present) :
    (lookupResult value present record rest regs stk).regs j = regs j :=
  readRegs_frame regs value present j none hv hp

end SubexponentialSAT.ArrayPrograms

end OAI.Algorithms
