import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionStore
import OAI.Algorithms.SubexponentialSAT.SubexpLinearFactorProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockCopyProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.CounterConversions
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-!
# Physical preparation for the target Lagrange cache

Eight runtime words occupy fixed preserved ports. The fixed program copies
the arithmetic parameters, builds a zero scalar, converts the binary prime
to a unary counter, allocates the zero polynomial, and initializes the cache
and outer-loop fuel. No prepared arithmetic workspace is an input.
-/

namespace SubexponentialSAT.SubexpLagrangeCachePreparation

open BitProgram StructuredCalls SubexpConvolutionControl

abbrev Word := List Bool

structure Inputs where
  prime : Word
  unit : Word
  modulus : Word
  width : Word
  reduction : Word
  minusOne : Word
  precision : Word
  exponent : Word

def sourcePorts : Fin 8 → Fin 256 := ![206, 207, 208, 209, 210, 211, 224, 225]
def inputWords (x : Inputs) : Fin 8 → Word :=
  ![x.prime, x.unit, x.modulus, x.width, x.reduction, x.minusOne, x.precision, x.exponent]

def rawStore (x : Inputs) (i : Fin 256) : Word :=
  if i = 206 then x.prime else if i = 207 then x.unit else
  if i = 208 then x.modulus else if i = 209 then x.width else
  if i = 210 then x.reduction else if i = 211 then x.minusOne else
  if i = 224 then x.precision else if i = 225 then x.exponent else []

def rawState (x : Inputs) (regs : Fin 16 → Bool) : Data := ⟨regs, rawStore x⟩
def primeValue (x : Inputs) : ℕ := CounterPrograms.value x.prime
def zeroCell (x : Inputs) : Word := List.replicate (4 * x.width.length) false
def unaryPrime (x : Inputs) : Word := List.replicate (primeValue x) true
def zeroArray (x : Inputs) : Word :=
  Subexp.BlockCopyProgram.copies (primeValue x) (zeroCell x)

def parameterStore (x : Inputs) : Store :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (rawStore x) 5 x.modulus) 194 x.modulus) 10 x.width)
      202 x.width) 201 x.reduction

def cellStore (x : Inputs) : Store := Function.update (parameterStore x) 104 (zeroCell x)
def allocatedStore (x : Inputs) : Store :=
  Function.update (Function.update (cellStore x) 243 (unaryPrime x)) 242 (zeroArray x)
def preparedStore (x : Inputs) : Store :=
  Function.update (Function.update (Function.update (Function.update
    (allocatedStore x) 213 (zeroCell x)) 217 (zeroCell x)) 250 [false]) 246 (unaryPrime x)
def preparedState (x : Inputs) (regs : Fin 16 → Bool) : Data := ⟨regs, preparedStore x⟩

def threeRegisters : Fin 3 ↪ Fin 16 := ⟨Fin.castAdd 13, Fin.castAdd_injective _ _⟩
def conversionPorts : Fin 3 ↪ Fin 256 := ⟨![0, 243, 1], by decide⟩
def allocationPorts : Fin 4 ↪ Fin 256 := ⟨![104, 242, 228, 227], by decide⟩
def initializePorts : Fin 128 ↪ Fin 256 := ⟨Fin.castAdd 128, Fin.castAdd_injective _ _⟩

def initializeZero : Code :=
  .call (ProgramLinking.liftProgram
    (compiled SubexpLinearFactorProgram.initializeCell 10 104) id initializePorts)
def convertPrime : Code :=
  .call (ProgramLinking.liftProgram CounterConversions.unaryProgram
    threeRegisters conversionPorts)
def allocate : Code :=
  .call (ProgramLinking.liftProgram Subexp.BlockCopyProgram.program
    threeRegisters allocationPorts)

private def seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

def parameters : Code := copy 208 5 ;; copy 208 194 ;; copy 209 10 ;;
  copy 209 202 ;; copy 210 201
def convertAllocate : Code := convertPrime ;; copy 243 227 ;; allocate
def finish : Code := copy 104 213 ;; copy 213 217 ;;
  Subexp.TupleProgram.pushConst 250 0 false ;; copy 243 246
def command : Code := parameters ;; initializeZero ;; copy 206 0 ;; convertAllocate ;; finish
def program := compiled command 206 250

theorem initializeZero_run (s : Store) (B : ℕ)
    (hB : (s 10).length = B) (h104 : s 104 = [])
    (h106 : s 106 = []) (h107 : s 107 = []) :
    ExecutesIn initializeZero (14 * B + 9) s
      (Function.update s 104 (List.replicate (4 * B) false)) := by
  intro regs
  let d : Data := ⟨regs, s⟩
  let native := projectState id initializePorts d
  have he := SubexpLinearFactorProgram.initializeCell_eval native B hB h104 h106 h107
  have hc := eval_liftCommand_from_state SubexpLinearFactorProgram.initializeCell
    10 104 id initializePorts d Function.injective_id initializePorts.injective he
  let last := embedState id initializePorts d (SubexpLinearFactorProgram.cellInitialized native B)
  have hext : Function.extend initializePorts (s ∘ initializePorts) s = s :=
    congrArg StructuredProgram.State.stacks
      (embedState_project id initializePorts d Function.injective_id initializePorts.injective)
  have hs : last.stacks = Function.update s 104 (List.replicate (4 * B) false) := by
    change Function.extend initializePorts
      (Function.update (s ∘ initializePorts) 104 (List.replicate (4 * B) false)) s = _
    rw [ProgramLinking.extend_update initializePorts.injective, hext]
    rfl
  have hl : last = (⟨last.regs, Function.update s 104 (List.replicate (4 * B) false)⟩ : Data) :=
    SubexpScanPrimitives.state_ext rfl hs
  refine ⟨14 * B + 9, last.regs, le_rfl, ?_⟩
  change Eval initializeZero (14 * B + 8 + 1) d last at hc
  rw [hl] at hc
  simpa only [Nat.add_assoc] using hc

theorem convertPrime_eval (d : Data) (h243 : d.stacks 243 = []) (h1 : d.stacks 1 = []) :
    ∃ n e, n ≤ CounterConversions.runtimeBound (d.stacks 0) ∧
      Eval convertPrime n d e ∧
      e.stacks = Function.update (Function.update d.stacks 0 []) 243
        (List.replicate (CounterPrograms.value (d.stacks 0)) true) ∧
      (∀ i : Fin 3, e.regs (threeRegisters i) = false) := by
  let input := CounterConversions.state (d.regs ∘ threeRegisters) (d.stacks 0) []
  let output := CounterConversions.state CounterConversions.zeroRegs []
    (List.replicate (CounterPrograms.value (d.stacks 0)) true)
  have hi : embedState threeRegisters conversionPorts d input = d := by
    apply embedState_eq_of_ports _ _ _ _ _ threeRegisters.injective conversionPorts.injective
    · intro i; rfl
    · intros; rfl
    · intro i
      fin_cases i <;> simp [input, CounterConversions.state, conversionPorts, h243, h1]
    · intros; rfl
  obtain ⟨n, hn, ht⟩ := CounterConversions.unary_runs (d.regs ∘ threeRegisters) (d.stacks 0) []
  simp only [List.append_nil] at ht
  let e := embedState threeRegisters conversionPorts d output
  have he := eval_call_lifted CounterConversions.unaryProgram threeRegisters conversionPorts
    d threeRegisters.injective conversionPorts.injective ht
  change Eval convertPrime n (embedState threeRegisters conversionPorts d input) e at he
  rw [hi] at he
  refine ⟨n, e, hn, he, ?_, ?_⟩
  · funext i
    by_cases hi0 : i = 0
    · subst i
      simpa [e, output, conversionPorts, CounterConversions.state] using
        embedState_stack threeRegisters conversionPorts d output conversionPorts.injective 0
    by_cases hi243 : i = 243
    · subst i
      simpa [e, output, conversionPorts, CounterConversions.state] using
        embedState_stack threeRegisters conversionPorts d output conversionPorts.injective 1
    by_cases hi1 : i = 1
    · subst i
      simpa [e, output, conversionPorts, CounterConversions.state, h1] using
        embedState_stack threeRegisters conversionPorts d output conversionPorts.injective 2
    · have hout : ¬ ∃ j, conversionPorts j = i := by
        rintro ⟨j, hj⟩
        fin_cases j
        · exact hi0 hj.symm
        · exact hi243 hj.symm
        · exact hi1 hj.symm
      simpa [e, hi0, hi243] using embedState_stack_frame threeRegisters conversionPorts d output i hout
  · intro i
    exact (embedState_register threeRegisters conversionPorts d output threeRegisters.injective i).trans rfl

theorem allocate_eval (d : Data) (p : ℕ) (cell : Word)
    (hr : ∀ i : Fin 3, d.regs (threeRegisters i) = false)
    (h104 : d.stacks 104 = cell) (h242 : d.stacks 242 = [])
    (h228 : d.stacks 228 = []) (h227 : d.stacks 227 = List.replicate p true) :
    ∃ e, Eval allocate (p * (7 * cell.length + 7) + 3) d e ∧
      e.stacks = Function.update (Function.update d.stacks 227 []) 242
        (Subexp.BlockCopyProgram.copies p cell) := by
  let input := Subexp.BlockCopyProgram.initialState p cell []
  let output := Subexp.BlockCopyProgram.data false false cell
    (Subexp.BlockCopyProgram.copies p cell) []
  have hi : projectState threeRegisters allocationPorts d = input := by
    apply SubexpScanPrimitives.state_ext
    · funext i
      fin_cases i
      · simpa [projectState, input, Subexp.BlockCopyProgram.initialState,
          Subexp.BlockCopyProgram.data] using hr 0
      · simpa [projectState, input, Subexp.BlockCopyProgram.initialState,
          Subexp.BlockCopyProgram.data] using hr 1
      · simpa [projectState, input, Subexp.BlockCopyProgram.initialState,
          Subexp.BlockCopyProgram.data] using hr 2
    · funext i
      fin_cases i <;> simp [input, Subexp.BlockCopyProgram.initialState,
        Subexp.BlockCopyProgram.data, projectState, allocationPorts, h104, h242, h228, h227]
  have ht := Subexp.BlockCopyProgram.program_trace p cell []
  simp only [List.append_nil] at ht
  dsimp only [input] at hi
  rw [← hi] at ht
  let e := embedState threeRegisters allocationPorts d output
  have he := eval_call_from_state Subexp.BlockCopyProgram.program threeRegisters allocationPorts
    d threeRegisters.injective allocationPorts.injective ht
  refine ⟨e, he, ?_⟩
  have hlocal : output.stacks = Function.update (Function.update
      (d.stacks ∘ allocationPorts) 3 []) 1 (Subexp.BlockCopyProgram.copies p cell) := by
    funext i
    fin_cases i <;> simp [output, Subexp.BlockCopyProgram.data, allocationPorts, h104, h228]
  have hext : Function.extend allocationPorts (d.stacks ∘ allocationPorts) d.stacks = d.stacks :=
    congrArg StructuredProgram.State.stacks
      (embedState_project threeRegisters allocationPorts d threeRegisters.injective allocationPorts.injective)
  change Function.extend allocationPorts output.stacks d.stacks = _
  rw [hlocal, ProgramLinking.extend_update allocationPorts.injective,
    ProgramLinking.extend_update allocationPorts.injective, hext]
  rfl

theorem convertAllocate_run (s : Store) (cell : Word)
    (h104 : s 104 = cell) (h243 : s 243 = []) (h1 : s 1 = [])
    (h227 : s 227 = []) (h228 : s 228 = []) (h242 : s 242 = []) (h120 : s 120 = []) :
    ExecutesIn convertAllocate
      (CounterConversions.runtimeBound (s 0) + (7 * CounterPrograms.value (s 0) + 5) +
        (CounterPrograms.value (s 0) * (7 * cell.length + 7) + 3)) s
      (Function.update (Function.update (Function.update s 0 []) 243
        (List.replicate (CounterPrograms.value (s 0)) true)) 242
          (Subexp.BlockCopyProgram.copies (CounterPrograms.value (s 0)) cell)) := by
  intro regs
  let d : Data := ⟨regs, s⟩
  obtain ⟨n, e, hn, he, hs, hr⟩ := convertPrime_eval d h243 h1
  let copied := SubexpScanPrimitives.afterCopy e 243 227 0 1
  have hc := SubexpScanPrimitives.copy_eval e 243 227 120 0 1
    (by decide) (by decide) (by decide) (by decide) (by simp [hs, d, h120])
  have hcopied : copied.stacks = Function.update
      (Function.update (Function.update s 0 []) 243
        (List.replicate (CounterPrograms.value (s 0)) true)) 227
          (List.replicate (CounterPrograms.value (s 0)) true) := by
    simp [copied, SubexpScanPrimitives.afterCopy, StackRoutines.copyStacks, hs, d, h227]
  have hregs : ∀ i : Fin 3, copied.regs (threeRegisters i) = false := by
    intro i
    fin_cases i
    · simp [copied, SubexpScanPrimitives.afterCopy, threeRegisters, readRegs]
    · simp [copied, SubexpScanPrimitives.afterCopy, threeRegisters, readRegs]
    · simpa [copied, SubexpScanPrimitives.afterCopy, threeRegisters, readRegs] using hr 2
  obtain ⟨out, ha, hout⟩ := allocate_eval copied (CounterPrograms.value (s 0)) cell hregs
    (by simp [hcopied, h104]) (by simp [hcopied, h242])
    (by simp [hcopied, h228]) (by simp [hcopied])
  have hsout : out.stacks = Function.update (Function.update (Function.update s 0 []) 243
      (List.replicate (CounterPrograms.value (s 0)) true)) 242
        (Subexp.BlockCopyProgram.copies (CounterPrograms.value (s 0)) cell) := by
    rw [hout, hcopied]
    funext i
    by_cases hi : i = 227 <;> simp [Function.update_apply, hi, h227]
  have hend : out = (⟨out.regs, Function.update (Function.update (Function.update s 0 []) 243
      (List.replicate (CounterPrograms.value (s 0)) true)) 242
        (Subexp.BlockCopyProgram.copies (CounterPrograms.value (s 0)) cell)⟩ : Data) :=
    SubexpScanPrimitives.state_ext rfl hsout
  have hc' : Eval (copy 243 227) (7 * CounterPrograms.value (s 0) + 5) e copied := by
    simpa [copy, hs, d] using hc
  have hall := he.seq (hc'.seq ha)
  rw [hend] at hall
  change n ≤ CounterConversions.runtimeBound (s 0) at hn
  exact ⟨_, out.regs, by omega, hall⟩

theorem parameters_run (x : Inputs) :
    ExecutesIn parameters
      (14 * x.modulus.length + 14 * x.width.length + 7 * x.reduction.length + 25)
      (rawStore x) (parameterStore x) := by
  let s1 := Function.update (rawStore x) 5 x.modulus
  let s2 := Function.update s1 194 x.modulus
  let s3 := Function.update s2 10 x.width
  let s4 := Function.update s3 202 x.width
  have h1 : ExecutesIn (copy 208 5) (7 * x.modulus.length + 5) (rawStore x) s1 := by
    simpa [s1, rawStore] using copy_run 208 5 (rawStore x) (by decide) (by decide) (by decide) (by simp [rawStore])
  have h2 : ExecutesIn (copy 208 194) (7 * x.modulus.length + 5) s1 s2 := by
    simpa [s2, s1, rawStore] using copy_run 208 194 s1 (by decide) (by decide) (by decide) (by simp [s1, rawStore])
  have h3 : ExecutesIn (copy 209 10) (7 * x.width.length + 5) s2 s3 := by
    simpa [s3, s2, s1, rawStore] using copy_run 209 10 s2 (by decide) (by decide) (by decide) (by simp [s2, s1, rawStore])
  have h4 : ExecutesIn (copy 209 202) (7 * x.width.length + 5) s3 s4 := by
    simpa [s4, s3, s2, s1, rawStore] using copy_run 209 202 s3 (by decide) (by decide) (by decide) (by simp [s3, s2, s1, rawStore])
  have h5 : ExecutesIn (copy 210 201) (7 * x.reduction.length + 5) s4 (parameterStore x) := by
    simpa [parameterStore, s4, s3, s2, s1, rawStore] using copy_run 210 201 s4 (by decide) (by decide) (by decide) (by simp [s4, s3, s2, s1, rawStore])
  convert h1.seq (h2.seq (h3.seq (h4.seq h5))) using 1
  dsimp [parameters, seq]
  ring

theorem finish_run (x : Inputs) :
    ExecutesIn finish (56 * x.width.length + 7 * primeValue x + 17)
      (allocatedStore x) (preparedStore x) := by
  let s1 := Function.update (allocatedStore x) 213 (zeroCell x)
  let s2 := Function.update s1 217 (zeroCell x)
  let s3 := Function.update s2 250 [false]
  have h1 : ExecutesIn (copy 104 213) (28 * x.width.length + 5) (allocatedStore x) s1 := by
    simpa [s1, allocatedStore, cellStore, parameterStore, rawStore, zeroCell, ← Nat.mul_assoc]
      using copy_run 104 213 (allocatedStore x) (by decide) (by decide) (by decide)
        (by simp [allocatedStore, cellStore, parameterStore, rawStore])
  have h2 : ExecutesIn (copy 213 217) (28 * x.width.length + 5) s1 s2 := by
    simpa [s2, s1, allocatedStore, cellStore, parameterStore, rawStore, zeroCell, ← Nat.mul_assoc]
      using copy_run 213 217 s1 (by decide) (by decide) (by decide)
        (by simp [s1, allocatedStore, cellStore, parameterStore, rawStore])
  have h3 : ExecutesIn (Subexp.TupleProgram.pushConst 250 0 false) 2 s2 s3 := by
    intro regs
    refine ⟨2, Function.update regs 0 false, le_rfl, ?_⟩
    simpa [Subexp.TupleProgram.pushedState, s3, s2, s1, allocatedStore,
      cellStore, parameterStore, rawStore] using
      Subexp.TupleProgram.pushConst_eval (250 : Fin 256) (0 : Fin 16) false ⟨regs, s2⟩
  have h4 : ExecutesIn (copy 243 246) (7 * primeValue x + 5) s3 (preparedStore x) := by
    simpa [preparedStore, s3, s2, s1, allocatedStore, cellStore, parameterStore, rawStore, unaryPrime]
      using copy_run 243 246 s3 (by decide) (by decide) (by decide)
        (by simp [s3, s2, s1, allocatedStore, cellStore, parameterStore, rawStore])
  convert h1.seq (h2.seq (h3.seq h4)) using 1
  dsimp [finish, seq]
  ring

def exactBudget (x : Inputs) : ℕ :=
  14 * x.modulus.length + 14 * x.width.length + 7 * x.reduction.length + 25 +
    (14 * x.width.length + 9) + (7 * x.prime.length + 5) +
    (CounterConversions.runtimeBound x.prime + (7 * primeValue x + 5) +
      (primeValue x * (28 * x.width.length + 7) + 3)) +
    (56 * x.width.length + 7 * primeValue x + 17)

theorem command_run (x : Inputs) : ExecutesIn command (exactBudget x) (rawStore x) (preparedStore x) := by
  let s := Function.update (cellStore x) 0 x.prime
  have h1 := parameters_run x
  have h2 : ExecutesIn initializeZero (14 * x.width.length + 9) (parameterStore x) (cellStore x) := by
    exact initializeZero_run _ _ (by simp [parameterStore]) (by simp [parameterStore, rawStore])
      (by simp [parameterStore, rawStore]) (by simp [parameterStore, rawStore])
  have h3 : ExecutesIn (copy 206 0) (7 * x.prime.length + 5) (cellStore x) s := by
    simpa [s, cellStore, parameterStore, rawStore] using copy_run 206 0 (cellStore x)
      (by decide) (by decide) (by decide) (by simp [cellStore, parameterStore, rawStore])
  have h4 : ExecutesIn convertAllocate
      (CounterConversions.runtimeBound x.prime + (7 * primeValue x + 5) +
        (primeValue x * (28 * x.width.length + 7) + 3)) s (allocatedStore x) := by
    have h := convertAllocate_run s (zeroCell x) (by simp [s, cellStore])
      (by simp [s, cellStore, parameterStore, rawStore])
      (by simp [s, cellStore, parameterStore, rawStore])
      (by simp [s, cellStore, parameterStore, rawStore])
      (by simp [s, cellStore, parameterStore, rawStore])
      (by simp [s, cellStore, parameterStore, rawStore])
      (by simp [s, cellStore, parameterStore, rawStore])
    have hz : Function.update s 0 [] = cellStore x := by
      funext i
      by_cases hi : i = 0 <;> simp [s, Function.update_apply, hi, cellStore, parameterStore, rawStore]
    rw [hz] at h
    simpa [s, allocatedStore, unaryPrime, zeroArray, zeroCell, primeValue, ← Nat.mul_assoc] using h
  have h5 := finish_run x
  convert h1.seq (h2.seq (h3.seq (h4.seq h5))) using 1
  · dsimp [command, seq]
  · unfold exactBudget
    ring

def inputLength (x : Inputs) : ℕ := x.prime.length + x.unit.length + x.modulus.length +
  x.width.length + x.reduction.length + x.minusOne.length + x.precision.length + x.exponent.length
def runtimeBound (x : Inputs) : ℕ := 200 * (primeValue x + 1) * (inputLength x + 1)

theorem budget_le (x : Inputs) : exactBudget x ≤ runtimeBound x := by
  have hprime : x.prime.length ≤ inputLength x := by unfold inputLength; omega
  have hmodulus : x.modulus.length ≤ inputLength x := by unfold inputLength; omega
  have hwidth : x.width.length ≤ inputLength x := by unfold inputLength; omega
  have hreduction : x.reduction.length ≤ inputLength x := by unfold inputLength; omega
  have hp := Nat.mul_le_mul_left (primeValue x) hprime
  have hw := Nat.mul_le_mul_left (primeValue x) hwidth
  unfold exactBudget runtimeBound CounterConversions.runtimeBound
  dsimp only [primeValue] at *
  nlinarith [Nat.zero_le (primeValue x * inputLength x)]

theorem command_correct (x : Inputs) :
    ExecutesIn command (runtimeBound x) (rawStore x) (preparedStore x) :=
  (command_run x).mono (budget_le x)

theorem program_runs (x : Inputs) (regs : Fin 16 → Bool) :
    ∃ rf, RunsIn program (runtimeBound x + 1)
      ((rawState x regs).withPC (some program.entry)) ((preparedState x rf).withPC none) := by
  obtain ⟨n, rf, hn, he⟩ := command_correct x regs
  exact ⟨rf, n + 1, Nat.add_le_add_right hn 1, compiled_halt_trace he 206 250⟩

theorem raw_master (x : Inputs) (i : Fin 8) : rawStore x (sourcePorts i) = inputWords x i := by
  fin_cases i <;> simp [rawStore, sourcePorts, inputWords]

theorem prepared_master (x : Inputs) (i : Fin 8) :
    preparedStore x (sourcePorts i) = inputWords x i := by
  fin_cases i <;> simp [preparedStore, allocatedStore, cellStore, parameterStore, rawStore,
    sourcePorts, inputWords]

theorem zeroArray_eq (x : Inputs) :
    zeroArray x = List.replicate (primeValue x * (4 * x.width.length)) false := by
  suffices ∀ p : ℕ, Subexp.BlockCopyProgram.copies p (zeroCell x) =
      List.replicate (p * (4 * x.width.length)) false from this _
  intro p
  induction p with
  | zero => simp
  | succ p ih =>
      rw [Subexp.BlockCopyProgram.copies_succ, ih]
      simp only [zeroCell, ← List.replicate_add]
      congr 1
      ring

theorem prepared_widths (x : Inputs) :
    (preparedStore x 104).length = 4 * x.width.length ∧
    (preparedStore x 242).length = primeValue x * (4 * x.width.length) ∧
    (preparedStore x 243).length = primeValue x ∧
    (preparedStore x 246).length = primeValue x := by
  simp [preparedStore, allocatedStore, cellStore, zeroCell, zeroArray, unaryPrime]

theorem prepared_contents (x : Inputs) :
    preparedStore x 5 = x.modulus ∧ preparedStore x 194 = x.modulus ∧
    preparedStore x 10 = x.width ∧ preparedStore x 202 = x.width ∧
    preparedStore x 201 = x.reduction ∧ preparedStore x 104 = zeroCell x ∧
    preparedStore x 213 = zeroCell x ∧ preparedStore x 217 = zeroCell x ∧
    preparedStore x 243 = unaryPrime x ∧ preparedStore x 246 = unaryPrime x ∧
    preparedStore x 242 = zeroArray x ∧ preparedStore x 250 = [false] := by
  simp [preparedStore, allocatedStore, cellStore, parameterStore]

theorem raw_word_length (x : Inputs) (i : Fin 256) :
    (rawStore x i).length ≤ inputLength x := by
  unfold rawStore
  split_ifs <;> (try simp only [List.length_nil]) <;> unfold inputLength <;> omega

def wordBound (x : Inputs) : ℕ := 4 * (primeValue x + 1) * (inputLength x + 1)

private theorem word_length_update (port : Fin 256) {s : Store} {w : Word} {B : ℕ}
    (hs : ∀ i, (s i).length ≤ B) (hw : w.length ≤ B) :
    ∀ i, (Function.update s port w i).length ≤ B := by
  intro i
  by_cases hi : i = port
  · subst i
    simpa only [Function.update_self] using hw
  · simpa only [Function.update_of_ne hi] using hs i

/-- Every returned stack, including the allocated polynomial, has a uniform
bound in the numeric prime value and the total raw input length. -/
theorem prepared_word_length (x : Inputs) (i : Fin 256) :
    (preparedStore x i).length ≤ wordBound x := by
  have hwidth : x.width.length ≤ inputLength x := by unfold inputLength; omega
  have hmodulus : x.modulus.length ≤ inputLength x := by unfold inputLength; omega
  have hreduction : x.reduction.length ≤ inputLength x := by unfold inputLength; omega
  have hproduct := Nat.mul_le_mul_left (primeValue x) hwidth
  have hsize : inputLength x ≤ wordBound x := by
    unfold wordBound
    nlinarith only [Nat.zero_le (primeValue x * inputLength x)]
  have hcell : (zeroCell x).length ≤ wordBound x := by
    simp only [zeroCell, List.length_replicate]
    unfold wordBound
    nlinarith only [hwidth, Nat.zero_le (primeValue x * inputLength x)]
  have hunary : (unaryPrime x).length ≤ wordBound x := by
    simp only [unaryPrime, List.length_replicate]
    unfold wordBound
    nlinarith only [Nat.zero_le (primeValue x * inputLength x)]
  have harray : (zeroArray x).length ≤ wordBound x := by
    simp only [zeroArray, Subexp.BlockCopyProgram.copies_length, zeroCell,
      List.length_replicate]
    unfold wordBound
    nlinarith only [hproduct]
  have hone : ([false] : Word).length ≤ wordBound x := by
    simp only [List.length_cons, List.length_nil]
    unfold wordBound
    nlinarith only [Nat.zero_le (primeValue x * inputLength x)]
  have hm := hmodulus.trans hsize
  have hw := hwidth.trans hsize
  have hr := hreduction.trans hsize
  have hraw : ∀ j, (rawStore x j).length ≤ wordBound x :=
    fun j => (raw_word_length x j).trans hsize
  have hparams : ∀ j, (parameterStore x j).length ≤ wordBound x :=
    word_length_update 201 (word_length_update 202 (word_length_update 10
      (word_length_update 194 (word_length_update 5 hraw hm) hm) hw) hw) hr
  have hcells : ∀ j, (cellStore x j).length ≤ wordBound x :=
    word_length_update 104 hparams hcell
  have halloc : ∀ j, (allocatedStore x j).length ≤ wordBound x :=
    word_length_update 242 (word_length_update 243 hcells hunary) harray
  exact word_length_update 246 (word_length_update 250 (word_length_update 217
    (word_length_update 213 halloc hcell) hcell) hone) hunary i

end SubexponentialSAT.SubexpLagrangeCachePreparation

end OAI.Algorithms
