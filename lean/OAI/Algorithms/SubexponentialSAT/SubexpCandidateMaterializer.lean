import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ArrayUpdateLifted
import OAI.Algorithms.SubexponentialSAT.SubexpFactorProgram
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

/-!
# Actual candidate-to-assignment materialization steps

A candidate label is a little-endian bit word. The runtime unary chunk width
selects its low bits, and a finite scan checks that every higher bit is zero.
The low bits are written into the selected chunk of a packed Boolean array by
the existing finite array-update program. No semantic label test or array
update is an executable instruction.
-/

namespace SubexponentialSAT.SubexpCandidateMaterializer

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.StackRoutines SubexponentialSAT.ArrayPrograms
open SubexponentialSAT.SubexpFactorProgram

abbrev Data := StructuredProgram.State 3 10

/-- Array, replacement, unary index, unary width, four scratch stacks,
unprocessed label, and the output validity bit. -/
def store (array replacement index width counter temporary reversed saved label valid : List Bool) :
    Fin 10 → List Bool :=
  ![array, replacement, index, width, counter, temporary, reversed, saved, label, valid]

def state (array replacement index width counter temporary reversed saved label valid : List Bool) :
    Data := ⟨fun _ => false,
      store array replacement index width counter temporary reversed saved label valid⟩

abbrev inputState (array index width label : List Bool) : Data :=
  state array [] index width [] [] [] [] label []

abbrev outputState (array replacement width : List Bool) (valid : Bool) : Data :=
  state array replacement [] width [] [] [] [] [] [valid]

private theorem state_ext {r s : ℕ} {a b : StructuredProgram.State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; cases hr; cases hs; rfl

private theorem reset_false : readRegs (fun _ : Fin 3 => false) 1 2 none = fun _ => false := by
  funext i; fin_cases i <;> simp [readRegs]

private theorem copy_eval {r s : ℕ} (src dst tmp : Fin s) (value present : Fin r)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (hvp : value ≠ present)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) (ht : stk tmp = []) :
    StructuredCalls.Eval (.call (copyProgram src dst tmp value present))
      (7 * (stk src).length + 5) ⟨regs, stk⟩
      ⟨readRegs regs value present none, copyStacks src dst stk⟩ :=
  .call _ (ListRegisterProgram.copy_run src dst tmp value present hsd hst htd hvp regs stk ht)

private theorem transfer_eval {r s : ℕ} (src dst : Fin s) (value present : Fin r)
    (hsd : src ≠ dst) (hvp : value ≠ present)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    StructuredCalls.Eval (.call (transferProgram src dst value present))
      (3 * (stk src).length + 3) ⟨regs, stk⟩
      ⟨readRegs regs value present none, transferStacks src dst stk⟩ :=
  .call _ (ListRegisterProgram.transfer_run src dst value present hsd hvp regs stk)

private theorem countedTransfer_eval {r s : ℕ} (counter src dst : Fin s)
    (value present : Fin r) (hcs : counter ≠ src) (hcd : counter ≠ dst)
    (hsd : src ≠ dst) (hvp : value ≠ present)
    (segment rest countWord : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hs : stk src = segment ++ rest) (hc : stk counter = countWord)
    (hlen : countWord.length = segment.length) :
    StructuredCalls.Eval (.call (countedTransferProgram counter src dst value present))
      (4 * segment.length + 3) ⟨regs, stk⟩
      ⟨readRegs regs value present none, countedTransferStacks counter src dst segment rest stk⟩ := by
  apply StructuredCalls.Eval.call
  have h := halt_after_trace _ (countedTransferProgram_trace counter src dst value present
    hcs hcd hsd hvp segment rest countWord regs stk hs hc hlen) 4 rfl rfl
  simpa [State.withPC, countedTransferResult, countedTransferProgram, Nat.add_assoc] using h

abbrev copyWidth : StructuredCalls.Cmd 3 10 := .call (copyProgram 3 4 5 1 2)
abbrev takeLow : StructuredCalls.Cmd 3 10 := .call (countedTransferProgram 4 8 6 1 2)
abbrev restoreLow : StructuredCalls.Cmd 3 10 := .call (transferProgram 6 1 1 2)

theorem copyWidth_eval (array index width label : List Bool) :
    StructuredCalls.Eval copyWidth (7 * width.length + 5)
      (inputState array index width label)
      (state array [] index width width [] [] [] label []) := by
  have hstore : copyStacks (3 : Fin 10) 4 (store array [] index width [] [] [] [] label []) =
      store array [] index width width [] [] [] label [] := by
    funext j; fin_cases j <;> simp [copyStacks, store]
  have h := copy_eval (3 : Fin 10) 4 5 (1 : Fin 3) 2
    (by decide) (by decide) (by decide) (by decide) (fun _ => false)
    (store array [] index width [] [] [] [] label []) rfl
  rw [hstore] at h
  simpa [copyWidth, inputState, state, store, reset_false] using h

theorem takeLow_eval (array index width low high : List Bool) (hw : width.length = low.length) :
    StructuredCalls.Eval takeLow (4 * low.length + 3)
      (state array [] index width width [] [] [] (low ++ high) [])
      (state array [] index width [] [] low.reverse [] high []) := by
  have hstore : countedTransferStacks (4 : Fin 10) 8 6 low high
      (store array [] index width width [] [] [] (low ++ high) []) =
      store array [] index width [] [] low.reverse [] high [] := by
    funext j; fin_cases j <;> simp [countedTransferStacks, store]
  have h := countedTransfer_eval (4 : Fin 10) 8 6 (1 : Fin 3) 2
    (by decide) (by decide) (by decide) (by decide) low high width (fun _ => false)
    (store array [] index width width [] [] [] (low ++ high) []) rfl rfl hw
  simpa only [takeLow, state, hstore, reset_false] using h

theorem restoreLow_eval (array index width low high : List Bool) :
    StructuredCalls.Eval restoreLow (3 * low.length + 3)
      (state array [] index width [] [] low.reverse [] high [])
      (state array low index width [] [] [] [] high []) := by
  have hstore : transferStacks (6 : Fin 10) 1
      (store array [] index width [] [] low.reverse [] high []) =
      store array low index width [] [] [] [] high [] := by
    funext j; fin_cases j <;> simp [transferStacks, store]
  have h := transfer_eval (6 : Fin 10) 1 (1 : Fin 3) 2 (by decide) (by decide)
    (fun _ => false) (store array [] index width [] [] low.reverse [] high [])
  have hl : (store array [] index width [] [] low.reverse [] high [] 6).length = low.length := by
    change low.reverse.length = low.length
    simp
  rw [hl] at h
  simpa only [restoreLow, state, hstore, reset_false, List.length_reverse] using h

def zeroPorts (i : Fin 2) : Fin 10 := ![8, 9] i

theorem zeroPorts_injective : Function.Injective zeroPorts := by decide

abbrev validateHigh : StructuredCalls.Cmd 3 10 :=
  .call (ProgramLinking.liftProgram ZeroBits.program id zeroPorts)

private theorem embed_zero (array low index width label valid input output : List Bool) :
    StructuredCalls.embedState id zeroPorts (state array low index width [] [] [] [] label valid)
      ⟨fun _ => false, ParserProgram.pair input output⟩ =
      state array low index width [] [] [] [] input output := by
  apply state_ext
  · simp [StructuredCalls.embedState, state]
  · change Function.extend zeroPorts (ParserProgram.pair input output)
      (store array low index width [] [] [] [] label valid) =
      store array low index width [] [] [] [] input output
    funext j
    by_cases h₈ : j = 8
    · subst j
      exact zeroPorts_injective.extend_apply _ _ (0 : Fin 2)
    by_cases h₉ : j = 9
    · subst j
      exact zeroPorts_injective.extend_apply _ _ (1 : Fin 2)
    have hout : ¬ ∃ i, zeroPorts i = j := by
      rintro ⟨i, hi⟩
      fin_cases i
      · exact h₈ hi.symm
      · exact h₉ hi.symm
    rw [Function.extend_apply' _ _ _ hout]
    fin_cases j <;> simp_all [store]

theorem validateHigh_eval (array low index width high : List Bool) :
    StructuredCalls.Eval validateHigh (4 * high.length + 8)
      (state array low index width [] [] [] [] high [])
      (state array low index width [] [] [] [] [] [allZero high]) := by
  have ht : Trace ZeroBits.program (4 * high.length + 8)
      ((⟨fun _ => false, ParserProgram.pair high []⟩ : StructuredProgram.State 3 2).withPC
        (some ZeroBits.program.entry))
      ((⟨fun _ => false, ParserProgram.pair [] [allZero high]⟩ : StructuredProgram.State 3 2).withPC none) := by
    have hi :
        ((⟨fun _ => false, ParserProgram.pair high []⟩ : StructuredProgram.State 3 2).withPC
          (some ZeroBits.program.entry)) = BitProgram.initial ZeroBits.program high := by
      change BitProgram.Cfg.mk _ _ _ = BitProgram.Cfg.mk _ _ _
      congr 1
    have ho :
        ((⟨fun _ => false, ParserProgram.pair [] [allZero high]⟩ : StructuredProgram.State 3 2).withPC
          none) = BitProgram.terminal ZeroBits.program [allZero high] := by
      change BitProgram.Cfg.mk _ _ _ = BitProgram.Cfg.mk _ _ _
      congr 1
      funext i
      fin_cases i <;> rfl
    rw [hi, ho]
    exact ZeroBits.trace high
  have h := StructuredCalls.eval_call_lifted ZeroBits.program id zeroPorts
    (state array low index width [] [] [] [] [] []) Function.injective_id zeroPorts_injective
    (a := ⟨fun _ => false, ParserProgram.pair high []⟩)
    (b := ⟨fun _ => false, ParserProgram.pair [] [allZero high]⟩) ht
  simpa only [validateHigh, embed_zero] using h

def arrayPorts : Fin 8 ↪ Fin 10 where
  toFun i := ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
  inj' := by intro i j h; exact Fin.ext (congrArg (fun k : Fin 10 => k.val) h)

abbrev patchArray : StructuredCalls.Cmd 3 10 :=
  .call (ArrayUpdateLifted.replaceProgramAt arrayPorts 1 2)

theorem patchArray_eval (earlier : List (List Bool)) (old low rest index width : List Bool)
    (valid : Bool) (hi : index.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = width.length)
    (hold : old.length = width.length) (hlow : low.length = width.length) :
    StructuredCalls.Eval patchArray
      (earlier.length * (14 * width.length + 10) + 20 * width.length + 21)
      (state (earlier.flatten ++ (old ++ rest)) low index width [] [] [] [] [] [valid])
      (outputState (earlier.flatten ++ (low ++ rest)) low width valid) := by
  have hstore : ArrayUpdateLifted.replaceStacksAt arrayPorts earlier low rest
      (store (earlier.flatten ++ (old ++ rest)) low index width [] [] [] [] [] [valid]) =
      store (earlier.flatten ++ (low ++ rest)) low [] width [] [] [] [] [] [valid] := by
    funext j
    fin_cases j <;> simp [ArrayUpdateLifted.replaceStacksAt, arrayPorts, store] <;> rfl
  have h := ArrayUpdateLifted.replaceProgramAt_eval arrayPorts (1 : Fin 3) 2
    (by decide) earlier old low rest width index (fun _ => false)
    (store (earlier.flatten ++ (old ++ rest)) low index width [] [] [] [] [] [valid])
    rfl rfl rfl rfl hi hrows hold hlow rfl rfl rfl rfl
  simpa only [patchArray, outputState, state, hstore, reset_false] using h

/-- Fixed finite code, independent of the chunk index, label width, and array size. -/
abbrev command : StructuredCalls.Cmd 3 10 :=
  .seq copyWidth (.seq takeLow (.seq restoreLow (.seq validateHigh patchArray)))

def program := StructuredCalls.compiled command (8 : Fin 10) 0

theorem command_size : StructuredCalls.size command = 71 := rfl

def workCost (indexWidth chunkWidth highWidth : ℕ) : ℕ :=
  indexWidth * (14 * chunkWidth + 10) + 34 * chunkWidth + 4 * highWidth + 40

theorem command_eval (earlier : List (List Bool)) (old low high rest index width : List Bool)
    (hi : index.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = width.length)
    (hold : old.length = width.length) (hlow : low.length = width.length) :
    StructuredCalls.Eval command (workCost index.length width.length high.length)
      (inputState (earlier.flatten ++ (old ++ rest)) index width (low ++ high))
      (outputState (earlier.flatten ++ (low ++ rest)) low width (allZero high)) := by
  have h := (copyWidth_eval (earlier.flatten ++ (old ++ rest)) index width (low ++ high)).seq
    ((takeLow_eval (earlier.flatten ++ (old ++ rest)) index width low high hlow.symm).seq
      ((restoreLow_eval (earlier.flatten ++ (old ++ rest)) index width low high).seq
        ((validateHigh_eval (earlier.flatten ++ (old ++ rest)) low index width high).seq
          (patchArray_eval earlier old low rest index width (allZero high) hi hrows hold hlow))))
  convert h using 1
  simp only [workCost, hi, hlow]
  ring

theorem trace (earlier : List (List Bool)) (old low high rest index width : List Bool)
    (hi : index.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = width.length)
    (hold : old.length = width.length) (hlow : low.length = width.length) :
    Trace program (workCost index.length width.length high.length + 1)
      ((inputState (earlier.flatten ++ (old ++ rest)) index width (low ++ high)).withPC
        (some program.entry))
      ((outputState (earlier.flatten ++ (low ++ rest)) low width (allZero high)).withPC none) :=
  StructuredCalls.compiled_halt_trace (command_eval earlier old low high rest index width
    hi hrows hold hlow) 8 0

theorem validity (low high width : List Bool) (hlow : low.length = width.length) :
    allZero high = decide (BinaryArithmetic.toNat (low ++ high) < 2 ^ width.length) := by
  simpa only [hlow] using UnaryValidity.result_correct low high

theorem array_length (earlier : List (List Bool)) (old low rest : List Bool)
    (hlen : low.length = old.length) :
    (earlier.flatten ++ (low ++ rest)).length = (earlier.flatten ++ (old ++ rest)).length := by
  simp [hlen]

theorem primitive_execution (earlier : List (List Bool))
    (old low high rest index width : List Bool) (hi : index.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = width.length)
    (hold : old.length = width.length) (hlow : low.length = width.length) :
    Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * (workCost index.length width.length high.length + 1))
      (BitProgram.primitiveCfg program
        ((inputState (earlier.flatten ++ (old ++ rest)) index width (low ++ high)).withPC
          (some program.entry)))
      (BitProgram.primitiveCfg program
        ((outputState (earlier.flatten ++ (low ++ rest)) low width (allZero high)).withPC none)) :=
  BitProgram.primitive_trace program (trace earlier old low high rest index width hi hrows hold hlow)

theorem lifted_eval {R S : ℕ} (register : Fin 3 → Fin R) (stack : Fin 10 → Fin S)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (frame : StructuredProgram.State R S) (earlier : List (List Bool))
    (old low high rest index width : List Bool) (hi : index.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = width.length)
    (hold : old.length = width.length) (hlow : low.length = width.length) :
    StructuredCalls.Eval (.call (ProgramLinking.liftProgram program register stack))
      (workCost index.length width.length high.length + 1)
      (StructuredCalls.embedState register stack frame
        (inputState (earlier.flatten ++ (old ++ rest)) index width (low ++ high)))
      (StructuredCalls.embedState register stack frame
        (outputState (earlier.flatten ++ (low ++ rest)) low width (allZero high))) :=
  StructuredCalls.eval_call_lifted program register stack frame hregister hstack
    (trace earlier old low high rest index width hi hrows hold hlow)

end SubexponentialSAT.SubexpCandidateMaterializer

end OAI.Algorithms
