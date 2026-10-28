import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticProducerControl
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram

namespace OAI.Algorithms

/-! Fixed copying and cleanup around the concrete quartic producer. -/

namespace SubexponentialSAT.SubexpQuarticSelectorControl

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 14 38

def producerPorts : Fin 35 → Fin 38 := Fin.castAdd 3

theorem producerPorts_injective : Function.Injective producerPorts := by
  intro i j h
  exact Fin.ext (congrArg (fun q : Fin 38 => q.val) h)

def extendState (lower : State 14 35) (prime output temporary : List Bool) : Data :=
  ⟨lower.regs, Fin.addCases (m := 35) (n := 3) (motive := fun _ => List Bool)
    lower.stacks ![prime, output, temporary]⟩

def localInput (regs : Fin 14 → Bool) (bits : List Bool) : State 14 35 :=
  ⟨regs, fun i => if i = 34 then bits else []⟩

def localOutput (regs : Fin 14 → Bool) (bits : List Bool) : State 14 35 :=
  ⟨regs, fun i => if i = 33 then bits else []⟩

def ready (regs : Fin 14 → Bool) (prime output : List Bool) : Data :=
  extendState ⟨regs, fun _ => []⟩ prime output []

def callInput (regs : Fin 14 → Bool) (prime : List Bool) : Data :=
  extendState (localInput regs prime) prime [] []

def callOutput (regs : Fin 14 → Bool) (prime output : List Bool) : Data :=
  extendState (localOutput regs output) prime [] []

abbrev clearOutput : Cmd 14 38 := .call (StackRoutines.clearProgram 36 0 1)
abbrev copyInput : Cmd 14 38 := .call (StackRoutines.copyProgram 35 34 37 0 1)
abbrev producerCall : Cmd 14 38 := .call (ProgramLinking.liftProgram
  SubexpQuarticProducerControl.program id producerPorts)
abbrev saveOutput : Cmd 14 38 :=
  .seq (.call (StackRoutines.transferProgram 33 37 0 1))
    (.call (StackRoutines.transferProgram 37 36 0 1))

/-- Old selected bytes are explicitly erased before the new result is saved. -/
abbrev command : Cmd 14 38 :=
  .seq clearOutput (.seq copyInput (.seq producerCall (.seq saveOutput RegisterResetProgram.all)))

def program := compiled command 35 36

def producerRegs (regs : Fin 14 → Bool) : Fin 14 → Bool :=
  readRegs (readRegs regs 0 1 none) 0 1 none

theorem embed_producer (a b : State 14 35) (prime output temporary : List Bool) :
    embedState id producerPorts (extendState a prime output temporary) b =
      extendState b prime output temporary := by
  apply state_ext
  · simp [embedState, extendState]
  · funext i
    refine Fin.addCases (m := 35) (n := 3) (fun j => ?_) (fun j => ?_) i
    · simpa only [producerPorts, extendState, Fin.addCases_left] using
        (embedState_stack id producerPorts (extendState a prime output temporary) b
          producerPorts_injective j)
    · rw [embedState_stack_frame]
      · simp only [extendState, Fin.addCases_right]
      · rintro ⟨k, hk⟩
        have hv := congrArg Fin.val hk
        change k.val = 35 + j.val at hv
        omega

theorem clearOutput_eval (regs : Fin 14 → Bool) (prime old : List Bool) :
    Eval clearOutput (2 * old.length + 3) (ready regs prime old)
      (ready (readRegs regs 0 1 none) prime []) := by
  let d := ready regs prime old
  let e : Data := ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks 36 d.stacks⟩
  have ht := StackRoutines.clearProgram_trace (36 : Fin 38) (0 : Fin 14) 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ ht 2 rfl rfl
  have he : Eval clearOutput (2 * (d.stacks 36).length + 3) d e := by
    apply Eval.call
    simpa [e, StackRoutines.clearResult, StructuredProgram.State.withPC,
      Nat.add_assoc] using hh
  have hend : e = ready (readRegs regs 0 1 none) prime [] := by
    apply state_ext
    · rfl
    · funext i
      fin_cases i <;> simp [e, d, ready, extendState, StackRoutines.clearStacks,
        Fin.addCases, Fin.coe_ofNat_eq_mod]
  rw [hend] at he
  simpa [d, ready, extendState, Fin.addCases, Fin.coe_ofNat_eq_mod] using he

theorem copyInput_eval (regs : Fin 14 → Bool) (prime : List Bool) :
    Eval copyInput (7 * prime.length + 5) (ready regs prime [])
      (callInput (readRegs regs 0 1 none) prime) := by
  let d := ready regs prime []
  have h := copy_eval d 35 34 37 0 1 (by decide) (by decide) (by decide) (by decide) rfl
  have hend : afterCopy d 35 34 0 1 = callInput (readRegs regs 0 1 none) prime := by
    apply state_ext
    · rfl
    · funext i
      fin_cases i <;> simp [afterCopy, d, ready, callInput, localInput, extendState,
        StackRoutines.copyStacks, Fin.addCases, Fin.coe_ofNat_eq_mod]
  rw [hend] at h
  simpa [copyInput, d, ready, extendState, Fin.addCases, Fin.coe_ofNat_eq_mod] using h

theorem producerCall_eval (regs finalRegs : Fin 14 → Bool) (prime output : List Bool)
    (n : ℕ) (h : Trace SubexpQuarticProducerControl.program n
      ((localInput regs prime).withPC (some SubexpQuarticProducerControl.program.entry))
      ((localOutput finalRegs output).withPC none)) :
    Eval producerCall n (callInput regs prime) (callOutput finalRegs prime output) := by
  have ht := eval_call_lifted SubexpQuarticProducerControl.program id producerPorts
    (callInput regs prime) Function.injective_id producerPorts_injective h
  simpa only [callInput, callOutput, embed_producer, producerCall] using ht

theorem saveOutput_eval (regs : Fin 14 → Bool) (prime output : List Bool) :
    Eval saveOutput (6 * output.length + 6) (callOutput regs prime output)
      (ready (readRegs (readRegs regs 0 1 none) 0 1 none) prime output) := by
  let d := callOutput regs prime output
  let e := afterTransfer d 33 37 0 1
  have h1 := transfer_eval d 33 37 0 1 (by decide) (by decide)
  have h2 := transfer_eval e 37 36 0 1 (by decide) (by decide)
  have hend : afterTransfer e 37 36 0 1 =
      ready (readRegs (readRegs regs 0 1 none) 0 1 none) prime output := by
    apply state_ext
    · rfl
    · funext i
      fin_cases i <;> simp [e, d, afterTransfer, callOutput, localOutput, ready,
        extendState, StackRoutines.transferStacks, Fin.addCases, Fin.coe_ofNat_eq_mod]
  have h := h1.seq h2
  rw [hend] at h
  convert h using 1
  · simp [e, d, afterTransfer, callOutput, localOutput, extendState,
      StackRoutines.transferStacks, Fin.addCases, Fin.coe_ofNat_eq_mod]
    omega

/-- This plumbing lemma consumes a trace of the fixed concrete producer.
The public adapter discharges that trace with the proved selector theorem. -/
theorem command_eval (regs finalRegs : Fin 14 → Bool) (prime old output : List Bool)
    (n : ℕ) (h : Trace SubexpQuarticProducerControl.program n
      ((localInput (producerRegs regs) prime).withPC
        (some SubexpQuarticProducerControl.program.entry))
      ((localOutput finalRegs output).withPC none)) :
    Eval command (n + 7 * prime.length + 6 * output.length + 2 * old.length + 28)
      (ready regs prime old) (ready (fun _ => false) prime output) := by
  have hclear := clearOutput_eval regs prime old
  have hcopy := copyInput_eval (readRegs regs 0 1 none) prime
  have hproduce := producerCall_eval (producerRegs regs) finalRegs prime output n h
  have hsave := saveOutput_eval finalRegs prime output
  have hreset := RegisterResetProgram.all_eval
    (ready (readRegs (readRegs finalRegs 0 1 none) 0 1 none) prime output)
  have he := hclear.seq (hcopy.seq (hproduce.seq (hsave.seq hreset)))
  convert he using 1 <;> first
  | omega
  | simp [RegisterResetProgram.zeroed, ready, extendState]

end SubexponentialSAT.SubexpQuarticSelectorControl

end OAI.Algorithms
