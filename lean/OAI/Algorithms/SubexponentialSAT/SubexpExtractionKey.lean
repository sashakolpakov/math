import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpKeyPadProgram
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! Fixed-control construction of an extraction key from a forward X-exponent
word, unary U/Z counters, and a preserved unary width. -/

namespace SubexponentialSAT.SubexpExtractionKey

open BitProgram StructuredCalls
open scoped BigOperators

abbrev Data := StructuredProgram.State 2 8
abbrev Code := StructuredCalls.Cmd 2 8

def storage (xs us zs width raw count output tmp : List Bool) : Fin 8 → List Bool :=
  ![xs, us, zs, width, raw, count, output, tmp]

def state (regs : Fin 2 → Bool) (xs us zs width raw count output tmp : List Bool) : Data :=
  ⟨regs, storage xs us zs width raw count output tmp⟩

def rawKey (xs : List Bool) (u z : ℕ) : List Bool :=
  xs ++ SymbolicCost.unaryWord u ++ SymbolicCost.unaryWord z

def pushFalse (dst : Fin 8) : Code :=
  .seq (.base (.atom (.set 0 false))) (.base (.atom (.push dst 0)))

def pushed (dst : Fin 8) (d : Data) : Data :=
  ⟨Function.update d.regs 0 false, Function.update d.stacks dst (false :: d.stacks dst)⟩

theorem pushFalse_eval (dst : Fin 8) (d : Data) : Eval (pushFalse dst) 2 d (pushed dst d) := by
  have h₁ := StructuredProgram.Eval.atom (StructuredProgram.Atom.set (0 : Fin 2) false) d
  have h₂ := StructuredProgram.Eval.atom (StructuredProgram.Atom.push dst (0 : Fin 2))
    ((StructuredProgram.Atom.set (0 : Fin 2) false).eval d)
  simpa [pushFalse, pushed, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using
    (Eval.seq (Eval.base h₁) (Eval.base h₂))

def copy (src dst : Fin 8) : Code := .call (StackRoutines.copyProgram src dst 7 0 1)

def copied (src dst : Fin 8) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩

theorem copy_eval (src dst : Fin 8) (d : Data)
    (hsd : src ≠ dst) (hs : src ≠ 7) (hd : (7 : Fin 8) ≠ dst)
    (htmp : d.stacks 7 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (copied src dst d) := by
  apply Eval.call
  exact ListRegisterProgram.copy_run src dst 7 0 1 hsd hs hd (by decide)
    d.regs d.stacks htmp

def prepareKey : Code := .seq (pushFalse 4)
  (.seq (copy 2 4) (.seq (pushFalse 4)
    (.seq (copy 1 4) (.seq (copy 0 4) (copy 3 5)))))

theorem prepareKey_eval (regs : Fin 2 → Bool) (xs : List Bool) (u z width : ℕ) :
    Eval prepareKey (7 * (xs.length + u + z + width) + 24)
      (state regs xs (List.replicate u true) (List.replicate z true)
        (List.replicate width true) [] [] [] [])
      (state (fun _ => false) xs (List.replicate u true) (List.replicate z true)
        (List.replicate width true) (rawKey xs u z) (List.replicate width true) [] []) := by
  let a := state regs xs (List.replicate u true) (List.replicate z true)
    (List.replicate width true) [] [] [] []
  let b := pushed 4 a
  let c := copied 2 4 b
  let d := pushed 4 c
  let e := copied 1 4 d
  let f := copied 0 4 e
  let g := copied 3 5 f
  have h₁ := pushFalse_eval 4 a
  have h₂ := copy_eval 2 4 b (by decide) (by decide) (by decide) (by
    simp [b, a, pushed, state, storage])
  have h₃ := pushFalse_eval 4 c
  have h₄ := copy_eval 1 4 d (by decide) (by decide) (by decide) (by
    simp [d, c, b, a, copied, pushed, StackRoutines.copyStacks, state, storage])
  have h₅ := copy_eval 0 4 e (by decide) (by decide) (by decide) (by
    simp [e, d, c, b, a, copied, pushed, StackRoutines.copyStacks, state, storage])
  have h₆ := copy_eval 3 5 f (by decide) (by decide) (by decide) (by
    simp [f, e, d, c, b, a, copied, pushed, StackRoutines.copyStacks, state, storage])
  have hg : g = state (fun _ => false) xs (List.replicate u true)
      (List.replicate z true) (List.replicate width true)
      (rawKey xs u z) (List.replicate width true) [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [f, e, d, c, b, a, copied, pushed, state, readRegs]
    · funext i; fin_cases i <;>
        simp [f, e, d, c, b, a, copied, pushed, state, storage,
          StackRoutines.copyStacks, rawKey, SymbolicCost.unaryWord, List.append_assoc]
  have total := h₁.seq (h₂.seq (h₃.seq (h₄.seq (h₅.seq h₆))))
  change Eval prepareKey _ a g at total
  rw [hg] at total
  convert total using 1
  · simp [f, e, d, c, b, a, copied, pushed, state, storage,
      StackRoutines.copyStacks]
    omega

def padPorts : Fin 3 → Fin 8 := ![4, 5, 6]

theorem padPorts_injective : Function.Injective padPorts := by decide

def padCall : Code := .call
  (ProgramLinking.liftProgram SubexpKeyPadProgram.program id padPorts)

private theorem pad_embed (frameRegs regs : Fin 2 → Bool)
    (xs us zs width raw count output raw' count' output' : List Bool) :
    embedState id padPorts (state frameRegs xs us zs width raw count output [])
      ⟨regs, SubexpKeyPadProgram.storage raw' count' output'⟩ =
      state regs xs us zs width raw' count' output' [] := by
  let frame := state frameRegs xs us zs width raw count output []
  let inner : StructuredProgram.State 2 3 :=
    ⟨regs, SubexpKeyPadProgram.storage raw' count' output'⟩
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    exact embedState_register id padPorts frame inner Function.injective_id i
  · funext i
    fin_cases i
    · exact embedState_stack_frame id padPorts frame inner 0 (by decide)
    · exact embedState_stack_frame id padPorts frame inner 1 (by decide)
    · exact embedState_stack_frame id padPorts frame inner 2 (by decide)
    · exact embedState_stack_frame id padPorts frame inner 3 (by decide)
    · exact embedState_stack id padPorts frame inner padPorts_injective 0
    · exact embedState_stack id padPorts frame inner padPorts_injective 1
    · exact embedState_stack id padPorts frame inner padPorts_injective 2
    · exact embedState_stack_frame id padPorts frame inner 7 (by decide)

theorem padCall_eval (n : ℕ) (regs : Fin 2 → Bool) (xs us zs width raw : List Bool) :
    ∃ finalRegs, Eval padCall (4 * n + 3)
      (state regs xs us zs width raw (List.replicate n true) [] [])
      (state finalRegs xs us zs width (raw.drop n) []
        (SubexpExponentProgram.padTake n raw).reverse []) := by
  obtain ⟨finalRegs, ht⟩ := SubexpKeyPadProgram.pad_trace n regs raw []
  refine ⟨finalRegs, ?_⟩
  change Trace SubexpKeyPadProgram.program (4 * n + 3)
    ((⟨regs, SubexpKeyPadProgram.storage raw (List.replicate n true) []⟩ :
      StructuredProgram.State 2 3).withPC (some SubexpKeyPadProgram.program.entry))
    ((⟨finalRegs, SubexpKeyPadProgram.storage (raw.drop n) []
      ((SubexpExponentProgram.padTake n raw).reverse ++ [])⟩ :
      StructuredProgram.State 2 3).withPC none) at ht
  have h := eval_call_lifted SubexpKeyPadProgram.program id padPorts
    (state regs xs us zs width raw (List.replicate n true) [] [])
    Function.injective_id padPorts_injective ht
  simpa only [padCall, pad_embed, List.append_nil] using h

def build : Code := .seq prepareKey padCall

def program := StructuredCalls.compiled build 0 6

theorem build_eval (regs : Fin 2 → Bool) (xs : List Bool) (u z width : ℕ) :
    ∃ finalRegs, Eval build (7 * (xs.length + u + z) + 11 * width + 27)
      (state regs xs (List.replicate u true) (List.replicate z true)
        (List.replicate width true) [] [] [] [])
      (state finalRegs xs (List.replicate u true) (List.replicate z true)
        (List.replicate width true) ((rawKey xs u z).drop width) []
        (SubexpExponentProgram.padTake width (rawKey xs u z)).reverse []) := by
  have hp := prepareKey_eval regs xs u z width
  obtain ⟨finalRegs, hpad⟩ := padCall_eval width (fun _ => false) xs
    (List.replicate u true) (List.replicate z true) (List.replicate width true) (rawKey xs u z)
  refine ⟨finalRegs, ?_⟩
  have total := hp.seq hpad
  change Eval build _ _ _ at total
  convert total using 1
  omega

theorem rawKey_eq {D : ℕ} (a : Fin D → ℕ) (u z : ℕ) :
    rawKey (SymbolicCost.unaryWords (List.ofFn a)) u z =
      SymbolicCost.encodeIndex (a, u, z) := by
  simp [rawKey, SymbolicCost.encodeIndex, SymbolicCost.indexData,
    SymbolicCost.unaryWords, List.flatMap_append]

theorem build_fixedKey {D : ℕ} (a : Fin D → ℕ) (u z : ℕ)
    (ha : ∑ i, a i ≤ 2 * D + 1) (hu : u < D + 1) (hz : z < D)
    (regs : Fin 2 → Bool) :
    ∃ finalRegs, RunsIn program (18 * SubexpSymbolicCost.indexBits D + 28)
      ((state regs (SymbolicCost.unaryWords (List.ofFn a))
        (List.replicate u true) (List.replicate z true)
        (List.replicate (SubexpSymbolicCost.indexBits D) true) [] [] [] []).withPC
          (some program.entry))
      ((state finalRegs (SymbolicCost.unaryWords (List.ofFn a))
        (List.replicate u true) (List.replicate z true)
        (List.replicate (SubexpSymbolicCost.indexBits D) true) [] []
        (SubexpSymbolicCost.fixedKey (a, u, z)).reverse []).withPC none) := by
  have retained : SymbolicCost.Retained D (a, u, z) := ⟨ha, hu, hz⟩
  have hlen := SubexpSymbolicCost.retained_index_bits (a, u, z) retained
  have hraw : (rawKey (SymbolicCost.unaryWords (List.ofFn a)) u z).length ≤
      SubexpSymbolicCost.indexBits D := by simpa only [rawKey_eq] using hlen
  obtain ⟨finalRegs, he⟩ := build_eval regs (SymbolicCost.unaryWords (List.ofFn a))
    u z (SubexpSymbolicCost.indexBits D)
  have hdrop := List.drop_eq_nil_iff.mpr hraw
  have hpad : SubexpExponentProgram.padTake (SubexpSymbolicCost.indexBits D)
      (rawKey (SymbolicCost.unaryWords (List.ofFn a)) u z) =
      SubexpSymbolicCost.fixedKey (a, u, z) := by
    rw [SubexpExponentProgram.padTake, List.take_of_length_le hraw, rawKey_eq]
    rfl
  rw [hdrop, hpad] at he
  have ht := StructuredCalls.compiled_halt_trace he 0 6
  refine ⟨finalRegs, _, ?_, ht⟩
  simp only [rawKey, List.length_append, SymbolicCost.unaryWord,
    List.length_replicate, List.length_singleton] at hraw
  omega

end SubexponentialSAT.SubexpExtractionKey

end OAI.Algorithms
