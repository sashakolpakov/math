import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.RecordPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-!
# Ordered physical iteration over the lifted node table

The input is the actual framed node table. The iterator sends each forward
node word to the installed finite per-node program and collects both the
node words and the fixed-length jets as unframed arrays in the same order.

The per-node program is a real Boolean instruction table. Its local trace
contract remains an explicit integration obligation until the dense row,
Taylor cache, template, job builder, and moment-phase tables are joined.
The outer iterator itself does not supply any of those outputs by oracle.
-/

namespace SubexponentialSAT.SubexpNodeMomentLoop

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 16 320
abbrev LocalData := State 16 256
abbrev Store := Fin 320 → List Bool
abbrev LocalStore := Fin 256 → List Bool
abbrev Code := Cmd 16 320

/-- Ordinary source caches 128--137 belong to the persistent caller frame. -/
def SourceBank (i : Fin 256) : Prop := 128 ≤ i.val ∧ i.val < 138

def localPorts : Fin 256 → Fin 320 := Fin.castAdd 64

theorem localPorts_injective : Function.Injective localPorts := Fin.castAdd_injective _ _

def restrict (s : Store) : LocalStore := s ∘ localPorts

@[simp] theorem localPorts_val (i : Fin 256) : (localPorts i).val = i.val := rfl

theorem localPorts_ne_high (i : Fin 256) (j : Fin 320) (hj : 256 ≤ j.val) :
    localPorts i ≠ j := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = j.val at hv
  omega

theorem restrict_update_high (s : Store) (j : Fin 320) (v : List Bool)
    (hj : 256 ≤ j.val) : restrict (Function.update s j v) = restrict s := by
  funext i
  exact Function.update_of_ne (localPorts_ne_high i j hj) _ _

theorem restrict_update (s : Store) (j : Fin 256) (v : List Bool) :
    restrict (Function.update s (localPorts j) v) = Function.update (restrict s) j v := by
  funext i
  by_cases h : i = j
  · subst i; simp [restrict]
  · have h' : localPorts i ≠ localPorts j := localPorts_injective.ne h
    simp [restrict, h, h']

def ports : RecordPrograms.Ports 16 320 where
  tag := 13
  present := 14
  found := 15
  source := 301
  payload := 302
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def clear (src : Fin 320) : Code := .call (StackRoutines.clearProgram src 0 1)
def transfer (src dst : Fin 320) : Code := .call (StackRoutines.transferProgram src dst 0 1)
def copy (src dst : Fin 320) : Code := .call (StackRoutines.copyProgram src dst 305 0 1)

def clearOut (d : Data) (src : Fin 320) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks src []⟩

theorem clear_eval (d : Data) (src : Fin 320) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (clearOut d src) := by
  apply Eval.call
  have h := StackRoutines.halt_after_trace _
    (StackRoutines.clearProgram_trace src (0 : Fin 16) 1 d.regs d.stacks) 2 rfl rfl
  simpa [clear, clearOut, StackRoutines.clearResult, StackRoutines.clearProgram,
    StackRoutines.clearStacks, StructuredProgram.State.withPC, Nat.add_assoc] using h

def resetFlags : Code :=
  .seq (RecordPrograms.atom (.set 13 false))
    (.seq (RecordPrograms.atom (.set 14 true)) (RecordPrograms.atom (.set 15 false)))

def resetState (d : Data) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 13 false) 14 true) 15 false, d.stacks⟩

theorem resetFlags_eval (d : Data) : Eval resetFlags 3 d (resetState d) := by
  have h₀ := Eval.base (StructuredProgram.Eval.atom (.set (13 : Fin 16) false) d)
  have h₁ := Eval.base (StructuredProgram.Eval.atom (.set (14 : Fin 16) true)
    ((StructuredProgram.Atom.set 13 false).eval d))
  have h₂ := Eval.base (StructuredProgram.Eval.atom (.set (15 : Fin 16) false)
    ((StructuredProgram.Atom.set 14 true).eval ((StructuredProgram.Atom.set 13 false).eval d)))
  simpa [resetFlags, resetState, RecordPrograms.atom, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, StructuredProgram.State.withPC,
    execInstr] using Eval.seq h₀ (Eval.seq h₁ h₂)

/-- A stage is an installed finite table, independent of the number of nodes. -/
structure Stage where
  labels : ℕ
  program : Program 16 256 labels

/-- The intended per-node producer has four separately linked finite stages.
The actual stage traces must be installed; this definition supplies no semantic
cache, source-code, or jet data. -/
abbrev pipeline (cache template jobs phase : Stage) : Cmd 16 256 :=
  .seq (.call cache.program) (.seq (.call template.program)
    (.seq (.call jobs.program) (.call phase.program)))

abbrev pipelineProgram (cache template jobs phase : Stage) :
    Program 16 256 (size (pipeline cache template jobs phase) + 1) :=
  compiled (pipeline cache template jobs phase) 78 102

/-- The local moment phase can be linked without relocating its existing ports. -/
abbrev stage128 {l : ℕ} (p : Program 16 128 l) : Stage :=
  ⟨l, ProgramLinking.liftProgram p id (Fin.castAdd 128)⟩

abbrev workerCall {l : ℕ} (worker : Program 16 256 l) : Code :=
  .call (ProgramLinking.liftProgram worker id localPorts)

/-- Copy the parsed reversed node into the node accumulator, activate the
forward word on 78, execute its finite producer, consume its jet, and clear
the width shape before the next zero-jet initialization. -/
abbrev callback {l : ℕ} (worker : Program 16 256 l) : Code :=
  .seq (.seq (copy 302 303) (transfer 302 78)) (.seq (workerCall worker)
    (.seq (transfer 102 304) (.seq (clear 104) resetFlags)))

abbrev loop {l : ℕ} (worker : Program 16 256 l) : Code :=
  RecordPrograms.iterate ports (callback worker)

/-- The master framed node table is preserved. Two final reversals restore
both arrays to the original node order expected by CRT. -/
abbrev command {l : ℕ} (worker : Program 16 256 l) : Code :=
  .seq (copy 300 301) (.seq (loop worker)
    (.seq (transfer 303 256) (transfer 304 265)))

abbrev program {l : ℕ} (worker : Program 16 256 l) :
    Program 16 320 (size (command worker) + 1) := compiled (command worker) 300 265

/-- Readiness concerns reusable local workspace, not loop data on 300+. -/
structure Ready (workspace : LocalStore → Prop) (d : Data) : Prop where
  ok : workspace (restrict d.stacks)
  theta : d.stacks 78 = []
  jet : d.stacks 102 = []
  shape : d.stacks 104 = []
  temporary : d.stacks 305 = []

/-- A local, measured trace contract for the installed per-node table. The
input is a real node word on 78; the output jet must be produced on 102.
The finite producer consumes 78, preserves the source cache bank, and restores
its workspace once the physical collector clears 102 and 104. -/
abbrev NodeContract {l : ℕ} (worker : Program 16 256 l)
    (validNode : List Bool → Prop) (workspace : LocalStore → Prop)
    (shape : List Bool) (jet : List Bool → List Bool) (cost : List Bool → ℕ) : Prop :=
  ∀ (bits : List Bool) (d : LocalData), validNode bits →
    workspace (Function.update d.stacks 78 []) →
    d.stacks 78 = bits → d.stacks 102 = [] → d.stacks 104 = [] →
    ∃ n ≤ cost bits, ∃ out : LocalData,
      Trace worker n (d.withPC (some worker.entry)) (out.withPC none) ∧
      out.stacks 78 = [] ∧ out.stacks 102 = jet bits ∧ out.stacks 104 = shape ∧
      workspace (Function.update (Function.update out.stacks 102 []) 104 []) ∧
      (∀ i, SourceBank i → out.stacks i = d.stacks i)

def callbackCost (cost : List Bool → ℕ) (shape : List Bool)
    (jet : List Bool → List Bool) (bits : List Bool) : ℕ :=
  cost bits + 10 * bits.length + 3 * (jet bits).length + 2 * shape.length + 17

/-- The only auxiliary effects are reversed concatenations in visit order.
The source bank and all higher stacks except loop ports/accumulators are framed. -/
def Effect (jet : List Bool → List Bool) (bits : List Bool) (d out : Data) : Prop :=
  out.stacks 303 = bits.reverse ++ d.stacks 303 ∧
  out.stacks 304 = (jet bits).reverse ++ d.stacks 304 ∧
  (∀ i : Fin 256, SourceBank i → out.stacks (localPorts i) = d.stacks (localPorts i)) ∧
  (∀ i : Fin 320, 256 ≤ i.val → i ≠ 301 → i ≠ 302 → i ≠ 303 → i ≠ 304 →
    out.stacks i = d.stacks i)

theorem restrict_recordState (d : Data) (v pr f : Bool) (src payload : List Bool) :
    restrict (RecordPrograms.state ports d v pr f src payload).stacks = restrict d.stacks := by
  change restrict (Function.update (Function.update d.stacks 301 src) 302 payload) = _
  rw [restrict_update_high _ _ _ (by decide), restrict_update_high _ _ _ (by decide)]

/-- Lift a concrete local producer without touching the outer accumulators. -/
theorem worker_eval {l : ℕ} (worker : Program 16 256 l)
    (validNode : List Bool → Prop) (workspace : LocalStore → Prop)
    (shape : List Bool) (jet : List Bool → List Bool) (cost : List Bool → ℕ)
    (contract : NodeContract worker validNode workspace shape jet cost)
    (bits : List Bool) (d : Data) (hv : validNode bits)
    (hw : workspace (Function.update (restrict d.stacks) 78 []))
    (ht : d.stacks 78 = bits) (hj : d.stacks 102 = []) (hs : d.stacks 104 = []) :
    ∃ n ≤ cost bits, ∃ out : Data, Eval (workerCall worker) n d out ∧
      out.stacks 78 = [] ∧ out.stacks 102 = jet bits ∧ out.stacks 104 = shape ∧
      workspace (Function.update (Function.update (restrict out.stacks) 102 []) 104 []) ∧
      (∀ i : Fin 256, SourceBank i → out.stacks (localPorts i) = d.stacks (localPorts i)) ∧
      (∀ i : Fin 320, 256 ≤ i.val → out.stacks i = d.stacks i) := by
  let low : LocalData := ⟨d.regs, restrict d.stacks⟩
  obtain ⟨n, hn, out, he, h78, h102, h104, hr, hb⟩ :=
    contract bits low hv hw ht hj hs
  let lifted := embedState id localPorts d out
  have hin : embedState id localPorts d low = d := by
    apply embedState_eq _ _ Function.injective_id localPorts_injective
    · intro i; rfl
    · intro i; rfl
    · intros; rfl
    · intros; rfl
  have hl : restrict lifted.stacks = out.stacks := by
    funext i
    exact embedState_stack id localPorts d out localPorts_injective i
  refine ⟨n, hn, lifted, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := eval_call_lifted worker id localPorts d Function.injective_id localPorts_injective he
    simpa only [workerCall, hin] using h
  · exact (congrFun hl 78).trans h78
  · exact (congrFun hl 102).trans h102
  · exact (congrFun hl 104).trans h104
  · simpa only [hl] using hr
  · intro i hi
    exact (congrFun hl i).trans (hb i hi)
  · intro i hi
    exact embedState_stack_frame id localPorts d out i (by
      rintro ⟨j, hj⟩
      exact localPorts_ne_high j i hi hj)

end SubexponentialSAT.SubexpNodeMomentLoop

end OAI.Algorithms
