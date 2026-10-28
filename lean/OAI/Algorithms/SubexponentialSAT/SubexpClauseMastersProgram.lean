import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFullShapeCapture
import OAI.Algorithms.SubexponentialSAT.CounterConversions

namespace OAI.Algorithms

/-!
# Physical preparation of the shared clause-factor masters

Four preserved binary input words supply the declared variable count, chunk
width, field modulus, and chunk count. Copies of the three counts are converted
by the checked binary-to-unary program. The checked full-shape capture then
builds the padded-array shape. No desired shape is an input assumption.

The modulus-width shape is a physical copy of the modulus word: its consumers
use its length, not its bits. The other two copies supply the binary chunk
width and field modulus at the clause-family's own persistent ports.
-/

namespace SubexponentialSAT.SubexpClauseMastersProgram

open BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 3 14

structure Inputs where
  n : List Bool
  ell : List Bool
  modulus : List Bool
  dimension : List Bool

def zeroRegs : Fin 3 → Bool := fun _ => false

def unary (bits : List Bool) : List Bool := List.replicate (CounterPrograms.value bits) true

/-- Inputs 0--3, six outputs 4--9, and four initially empty work ports 10--13. -/
def initialState (regs : Fin 3 → Bool) (m : Inputs) : Data :=
  ⟨regs, ![m.n, m.ell, m.modulus, m.dimension, [], [], [], [], [], [], [], [], [], []]⟩

/-- Outputs: n-shape 4, ell-shape 5, full-shape 6, modulus-width 7,
binary ell 8, and modulus 9. All four original binary words are preserved. -/
def outputState (m : Inputs) : Data :=
  ⟨zeroRegs, ![m.n, m.ell, m.modulus, m.dimension, unary m.n, unary m.ell,
    SubexpFullShapeProgram.fullShape (CounterPrograms.value m.dimension) (unary m.ell),
    m.modulus, m.ell, m.modulus, [], [], [], []]⟩

def write (d : Data) (dst : Fin 14) (word : List Bool) : Data :=
  ⟨zeroRegs, Function.update d.stacks dst word⟩

def copied (d : Data) (src dst : Fin 14) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks dst (d.stacks src)⟩

private theorem readRegs_zero : readRegs zeroRegs 0 1 none = zeroRegs := by
  funext i; fin_cases i <;> rfl

private theorem resetRegs_zero :
    SubexpFullShapeCapture.resetRegs (Function.Embedding.refl (Fin 3)) zeroRegs =
      zeroRegs := by
  funext i; fin_cases i <;> rfl

abbrev copy (src dst : Fin 14) : Cmd 3 14 :=
  .call (StackRoutines.copyProgram src dst 13 0 1)

theorem copy_eval (src dst : Fin 14) (d : Data)
    (hsd : src ≠ dst) (hs : src ≠ 13) (hd : (13 : Fin 14) ≠ dst)
    (hempty : d.stacks dst = []) (htmp : d.stacks 13 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (copied d src dst) := by
  have h := ListRegisterProgram.copy_run src dst 13 (0 : Fin 3) 1
    hsd hs hd (by decide) d.regs d.stacks htmp
  apply Eval.call
  simpa only [copied, ListRegisterProgram.Run, StructuredProgram.State.withPC,
    StackRoutines.copyStacks, hempty, List.append_nil] using h

theorem copy_zero_eval (src dst : Fin 14) (d : Data)
    (hsd : src ≠ dst) (hs : src ≠ 13) (hd : (13 : Fin 14) ≠ dst)
    (hempty : d.stacks dst = []) (htmp : d.stacks 13 = []) (hr : d.regs = zeroRegs) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5)
      d (write d dst (d.stacks src)) := by
  simpa only [copied, hr, readRegs_zero, write] using
    copy_eval src dst d hsd hs hd hempty htmp

def unaryPorts (dst : Fin 14) : Fin 3 → Fin 14 := ![11, dst, 12]

theorem unaryPorts_injective (dst : Fin 14) (h11 : dst ≠ 11) (h12 : dst ≠ 12) :
    Function.Injective (unaryPorts dst) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [unaryPorts]

abbrev makeUnary (dst : Fin 14) : Cmd 3 14 :=
  .call (ProgramLinking.liftProgram CounterConversions.unaryProgram id (unaryPorts dst))

abbrev unaryCopy (src dst : Fin 14) : Cmd 3 14 :=
  .seq (copy src 11) (makeUnary dst)

def unaryCopyBound (bits : List Bool) : ℕ :=
  7 * bits.length + 5 + CounterConversions.runtimeBound bits

private theorem embed_unary_input (src dst : Fin 14) (d : Data)
    (hd11 : dst ≠ 11) (hd12 : dst ≠ 12)
    (hd : d.stacks dst = []) (h12 : d.stacks 12 = []) :
    embedState id (unaryPorts dst) (copied d src 11)
      (CounterConversions.state (readRegs d.regs 0 1 none) (d.stacks src) []) =
      copied d src 11 := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id
    (unaryPorts_injective dst hd11 hd12)
  · intro i; rfl
  · intro i hi; rfl
  · intro i
    fin_cases i <;>
      simp [unaryPorts, copied, CounterConversions.state, hd11, hd, h12]
  · intro i hi; rfl

private theorem embed_unary_output (src dst : Fin 14) (d : Data)
    (hd11 : dst ≠ 11) (hd12 : dst ≠ 12)
    (h11 : d.stacks 11 = []) (h12 : d.stacks 12 = []) :
    embedState id (unaryPorts dst) (copied d src 11)
      (CounterConversions.state CounterConversions.zeroRegs [] (unary (d.stacks src))) =
      write d dst (unary (d.stacks src)) := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id
    (unaryPorts_injective dst hd11 hd12)
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;>
      simp [unaryPorts, write, CounterConversions.state,
        Ne.symm hd11, Ne.symm hd12, h11, h12]
  · intro i hi
    have hi11 : i ≠ 11 := fun h => hi ⟨0, h.symm⟩
    have hid : i ≠ dst := fun h => hi ⟨1, h.symm⟩
    simp [write, copied, hi11, hid]

/-- A preserving binary-to-unary call using fixed work ports 11--13. -/
theorem unaryCopy_eval (src dst : Fin 14) (d : Data)
    (hs11 : src ≠ 11) (hs13 : src ≠ 13)
    (hd11 : dst ≠ 11) (hd12 : dst ≠ 12)
    (hd : d.stacks dst = []) (h11 : d.stacks 11 = [])
    (h12 : d.stacks 12 = []) (h13 : d.stacks 13 = []) :
    ∃ t ≤ unaryCopyBound (d.stacks src),
      Eval (unaryCopy src dst) t d (write d dst (unary (d.stacks src))) := by
  have hc := copy_eval src 11 d hs11 hs13 (by decide) h11 h13
  obtain ⟨t, ht, htrace⟩ := CounterConversions.unary_runs
    (readRegs d.regs 0 1 none) (d.stacks src) []
  simp only [List.append_nil] at htrace
  have hu := eval_call_lifted CounterConversions.unaryProgram id (unaryPorts dst)
    (copied d src 11) Function.injective_id (unaryPorts_injective dst hd11 hd12) htrace
  rw [embed_unary_input src dst d hd11 hd12 hd h12] at hu
  have hout := embed_unary_output src dst d hd11 hd12 h11 h12
  unfold unary at hout
  rw [hout] at hu
  refine ⟨7 * (d.stacks src).length + 5 + t, ?_, hc.seq hu⟩
  exact Nat.add_le_add_left ht _

def capturePorts : Fin 6 ↪ Fin 14 := ⟨![5, 6, 12, 10, 11, 13], by decide⟩

abbrev capture : Cmd 3 14 := .call
  (SubexpFullShapeCapture.program (Function.Embedding.refl _) capturePorts)

abbrev clearCount : Cmd 3 14 := .call (StackRoutines.clearProgram 10 0 1)

theorem clearCount_eval (d : Data) (hr : d.regs = zeroRegs) :
    Eval clearCount (2 * (d.stacks 10).length + 3) d (write d 10 []) := by
  apply Eval.call
  simpa only [ListRegisterProgram.Run, StructuredProgram.State.withPC,
    StackRoutines.clearStacks, write, hr, readRegs_zero] using
    ListRegisterProgram.clear_run (10 : Fin 14) (0 : Fin 3) 1 d.regs d.stacks

abbrev command : Cmd 3 14 :=
  .seq (unaryCopy 0 4) (.seq (unaryCopy 1 5) (.seq (unaryCopy 3 10)
    (.seq capture (.seq clearCount (.seq (copy 2 7) (.seq (copy 2 9) (copy 1 8)))))))

def workBound (m : Inputs) : ℕ :=
  unaryCopyBound m.n + unaryCopyBound m.ell + unaryCopyBound m.dimension +
  (CounterPrograms.value m.dimension * (7 * CounterPrograms.value m.ell + 14) + 10) +
  (2 * CounterPrograms.value m.dimension + 3) +
  (7 * m.modulus.length + 5) + (7 * m.modulus.length + 5) + (7 * m.ell.length + 5)

private def afterN (m : Inputs) := write (initialState zeroRegs m) 4 (unary m.n)
private def afterEll (m : Inputs) := write (afterN m) 5 (unary m.ell)
private def afterD (m : Inputs) := write (afterEll m) 10 (unary m.dimension)
private def afterFull (m : Inputs) := write (afterD m) 6
  (SubexpFullShapeProgram.fullShape (CounterPrograms.value m.dimension) (unary m.ell))
private def afterClear (m : Inputs) := write (afterFull m) 10 []
private def afterWidth (m : Inputs) := write (afterClear m) 7 m.modulus
private def afterModulus (m : Inputs) := write (afterWidth m) 9 m.modulus

private theorem after_output (m : Inputs) :
    write (afterModulus m) 8 m.ell = outputState m := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;> rfl

/-- All six requested masters are produced by actual instructions from four
binary words; the original words and all scratch-clear postconditions remain. -/
theorem command_eval (regs : Fin 3 → Bool) (m : Inputs) :
    ∃ t ≤ workBound m, Eval command t (initialState regs m) (outputState m) := by
  obtain ⟨tn, htn, hn⟩ := unaryCopy_eval 0 4 (initialState regs m)
    (by decide) (by decide) (by decide) (by decide) rfl rfl rfl rfl
  change Eval (unaryCopy 0 4) tn (initialState regs m) (afterN m) at hn
  change tn ≤ unaryCopyBound m.n at htn
  obtain ⟨te, hte, he⟩ := unaryCopy_eval 1 5 (afterN m)
    (by decide) (by decide) (by decide) (by decide) rfl rfl rfl rfl
  change Eval (unaryCopy 1 5) te (afterN m) (afterEll m) at he
  change te ≤ unaryCopyBound m.ell at hte
  obtain ⟨td, htd, hd⟩ := unaryCopy_eval 3 10 (afterEll m)
    (by decide) (by decide) (by decide) (by decide) rfl rfl rfl rfl
  change Eval (unaryCopy 3 10) td (afterEll m) (afterD m) at hd
  change td ≤ unaryCopyBound m.dimension at htd
  have hf := SubexpFullShapeCapture.caller_eval (Function.Embedding.refl (Fin 3))
    capturePorts (afterD m) (CounterPrograms.value m.dimension) rfl rfl rfl rfl rfl
  have hrf : SubexpFullShapeCapture.output (Function.Embedding.refl (Fin 3))
      capturePorts (afterD m) (CounterPrograms.value m.dimension) = afterFull m := by
    apply congrArg₂ StructuredProgram.State.mk
    · exact resetRegs_zero
    · rfl
  rw [hrf] at hf
  change Eval capture
    (CounterPrograms.value m.dimension * (7 * (unary m.ell).length + 14) + 10)
    (afterD m) (afterFull m) at hf
  simp only [unary, List.length_replicate] at hf
  have hclear := clearCount_eval (afterFull m) rfl
  change Eval clearCount (2 * (unary m.dimension).length + 3)
    (afterFull m) (afterClear m) at hclear
  simp only [unary, List.length_replicate] at hclear
  have hw := copy_zero_eval 2 7 (afterClear m) (by decide) (by decide) (by decide) rfl rfl rfl
  change Eval (copy 2 7) (7 * m.modulus.length + 5) (afterClear m) (afterWidth m) at hw
  have hm := copy_zero_eval 2 9 (afterWidth m) (by decide) (by decide) (by decide) rfl rfl rfl
  change Eval (copy 2 9) (7 * m.modulus.length + 5) (afterWidth m) (afterModulus m) at hm
  have hb := copy_zero_eval 1 8 (afterModulus m) (by decide) (by decide) (by decide) rfl rfl rfl
  change Eval (copy 1 8) (7 * m.ell.length + 5)
    (afterModulus m) (write (afterModulus m) 8 m.ell) at hb
  rw [after_output] at hb
  refine ⟨_, ?_, hn.seq (he.seq (hd.seq (hf.seq (hclear.seq (hw.seq (hm.seq hb))))))⟩
  unfold workBound
  omega

def program := compiled command (0 : Fin 14) 6

theorem runs (regs : Fin 3 → Bool) (m : Inputs) :
    RunsIn program (workBound m + 1)
      ((initialState regs m).withPC (some program.entry)) ((outputState m).withPC none) := by
  obtain ⟨t, ht, he⟩ := command_eval regs m
  exact ⟨t + 1, Nat.add_le_add_right ht 1, compiled_halt_trace he 0 6⟩

theorem lifted_execution {R S : ℕ} (register : Fin 3 → Fin R) (stack : Fin 14 → Fin S)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (frame : StructuredProgram.State R S) (regs : Fin 3 → Bool) (m : Inputs) :
    ∃ t ≤ workBound m + 1,
      Eval (.call (ProgramLinking.liftProgram program register stack)) t
        (embedState register stack frame (initialState regs m))
        (embedState register stack frame (outputState m)) := by
  obtain ⟨t, ht, he⟩ := runs regs m
  exact ⟨t, ht, eval_call_lifted program register stack frame hregister hstack he⟩

theorem primitive_execution (regs : Fin 3 → Bool) (m : Inputs) :
    Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (workBound m + 1))
      (primitiveCfg program ((initialState regs m).withPC (some program.entry)))
      (primitiveCfg program ((outputState m).withPC none)) :=
  BitProgram.primitive_execution program (runs regs m)

theorem output_lengths (m : Inputs) :
    ((outputState m).stacks 4).length = CounterPrograms.value m.n ∧
    ((outputState m).stacks 5).length = CounterPrograms.value m.ell ∧
    ((outputState m).stacks 6).length =
      CounterPrograms.value m.dimension * CounterPrograms.value m.ell ∧
    ((outputState m).stacks 7).length = m.modulus.length := by
  simp [outputState, unary]

theorem output_binary_ell (m : Inputs) : (outputState m).stacks 8 = m.ell := rfl
theorem output_modulus (m : Inputs) : (outputState m).stacks 9 = m.modulus := rfl

theorem output_inputs (m : Inputs) :
    (outputState m).stacks 0 = m.n ∧ (outputState m).stacks 1 = m.ell ∧
    (outputState m).stacks 2 = m.modulus ∧ (outputState m).stacks 3 = m.dimension :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem output_scratch (m : Inputs) :
    (outputState m).stacks 10 = [] ∧ (outputState m).stacks 11 = [] ∧
    (outputState m).stacks 12 = [] ∧ (outputState m).stacks 13 = [] :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem output_covers (m : Inputs) (hell : 0 < CounterPrograms.value m.ell)
    (hD : CounterPrograms.value m.dimension =
      ChunkPartition.count (CounterPrograms.value m.n) (CounterPrograms.value m.ell)) :
    CounterPrograms.value m.n ≤ ((outputState m).stacks 6).length ∧
    ((outputState m).stacks 6).length < CounterPrograms.value m.n + CounterPrograms.value m.ell := by
  change CounterPrograms.value m.n ≤
      (SubexpFullShapeProgram.fullShape (CounterPrograms.value m.dimension) (unary m.ell)).length ∧
    (SubexpFullShapeProgram.fullShape (CounterPrograms.value m.dimension) (unary m.ell)).length <
      CounterPrograms.value m.n + CounterPrograms.value m.ell
  rw [hD]
  simpa only [unary, List.length_replicate] using
    SubexpFullShapeProgram.canonical_length_bounds (CounterPrograms.value m.n)
      (unary m.ell) (by simpa [unary] using hell)

end SubexponentialSAT.SubexpClauseMastersProgram

end OAI.Algorithms
