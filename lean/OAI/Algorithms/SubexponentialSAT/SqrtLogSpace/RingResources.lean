import OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgramServices
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyRingBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgramDegree
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTableModel
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources

/-! Native ternary arithmetic retains fixed-width residues and polynomial-size
multiplication tables. The local time bound controls temporary stack growth;
the initial sum includes every persistent caller stack. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingResources

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog

/-- From the binary precision alone, the native preparation constructs the
modulus, canonical scalar caches, inverse of two, and Newton workspace. -/
theorem scalar_prepare_run_space (bits : List Bool) (t : ℕ)
    (hbits : CounterPrograms.value bits = t) (ht : 0 < t) :
    ∃ out : IdempotentPreparationProgram.Data,
      ∃ (M : SubexpPreparedQuartic.Modulus 3 t)
        (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t) (steps : ℕ),
      steps ≤ 100000000*(t+bits.length+2)^4+1 ∧
      Trace IdempotentPreparationProgram.program steps
        ((IdempotentPreparationProgram.inputData bits).withPC
          (some IdempotentPreparationProgram.program.entry)) (out.withPC none) ∧
      IdempotentPreparationProgram.Ready t bits.length M cache u out ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace IdempotentPreparationProgram.program prefixSteps
          ((IdempotentPreparationProgram.inputData bits).withPC
            (some IdempotentPreparationProgram.program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          bits.length + (100000000*(t+bits.length+2)^4+1) := by
  obtain ⟨out, M, cache, u, ⟨steps, hsteps, htrace⟩, hready⟩ :=
    IdempotentPreparationProgram.program_runs bits t hbits ht
  have hbudget : steps ≤ 100000000*(t+bits.length+2)^4+1 :=
    hsteps.trans (Nat.add_le_add_right
      (IdempotentPreparationProgram.preparationBudget_polynomial t bits.length) 1)
  have hinput : dataBits
      ((IdempotentPreparationProgram.inputData bits).withPC
        (some IdempotentPreparationProgram.program.entry)) ≤ bits.length := by
    change stackBits (Function.update (fun _ : Fin 41 => []) 31 bits) ≤ bits.length
    have h := stackBits_update (fun _ : Fin 41 => []) 31 bits
    simpa [stackBits] using h.le
  refine ⟨out, M, cache, u, steps, hbudget, htrace, hready, ?_⟩
  intro prefixSteps intermediate hprefix hp
  exact StructuredSpace.local_stack_bound _
    (steps := 100000000*(t+bits.length+2)^4+1) hinput
    prefixSteps intermediate (hprefix.trans hbudget) hp

/-- Extension coefficients use the supplied ternary residue representation. -/
theorem coefficient_length {t d : ℕ}
    (x : RingProgram.Code (RingProgram.ScalarCode 3 t) d) :
    (RingProgram.flat x).length = 2 * d * t := by
  rw [RingProgram.flat_length, RingProgram.ternary_baseWidth]
  ring

/-- All cubic structure constants are stored, each with its actual bit width. -/
theorem table_length {t d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth 3 t)) :
    (RingTriple.tableEncoding table).length = 2 * d^3 * t := by
  rw [RingTriple.tableEncoding_length, RingProgram.ternary_baseWidth]
  ring

/-- Addition preserves both operands and every caller port except output 244. -/
theorem add_run_space (t : ℕ) {d : ℕ}
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (table : Fin d → Fin d → Fin d → Word (baseWidth 3 t))
    (base s : SubexpConvolutionControl.Store)
    (hready : HornerProgram.Services.NativeReady 3 t M cache table base)
    (x y : RingProgram.Code (RingProgram.ScalarCode 3 t) d)
    (hframe : CRTLocalProgram.LowFrame base s)
    (hx : s 240 = RingProgram.flat x) (hy : s 241 = RingProgram.flat y)
    (hout : s 244 = []) (htmp : s 245 = []) (regs : Fin 16 → Bool) :
    ∃ steps rf,
      steps ≤ 50000 * (d+1)^3 * (2*t+1)^2 ∧
      Eval HornerProgram.Services.add steps (⟨regs, s⟩ : State 16 256)
        ⟨rf, Function.update s 244
          (RingProgram.flat (RingProgram.addRun (RingProgram.scalarProgram 3 t M cache) x y).1)⟩ ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps+1 →
        Trace (compiled HornerProgram.Services.add 240 244) prefixSteps
          ((⟨regs, s⟩ : State 16 256).withPC
            (some (compiled HornerProgram.Services.add 240 244).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          stackBits s + 50000 * (d+1)^3 * (2*t+1)^2 := by
  obtain ⟨steps, rf, hsteps, heval⟩ :=
    HornerProgram.Services.add_spec 3 t M cache table base hready s x y
      hframe hx hy hout htmp regs
  have hbudget : steps ≤ 50000 * (d+1)^3 * (2*t+1)^2 := by
    simpa only [RingProgram.ternary_baseWidth] using
      hsteps.trans (HornerProgram.Services.addBudget_polynomial (baseWidth 3 t) d)
  refine ⟨steps, rf, hbudget, heval, ?_⟩
  apply StructuredSpace.compiled_halt_stack_bound heval 240 244
  intro prefixSteps intermediate hprefix htrace
  exact StructuredSpace.local_stack_bound _ (steps := 50000 * (d+1)^3 * (2*t+1)^2)
    (initialBound := stackBits s) (by rfl) prefixSteps intermediate
    (hprefix.trans hbudget) htrace

/-- Multiplication has the same preserved-operand ABI as addition. -/
theorem multiply_run_space (t : ℕ) {d : ℕ}
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (table : Fin d → Fin d → Fin d → Word (baseWidth 3 t))
    (base s : SubexpConvolutionControl.Store)
    (hready : HornerProgram.Services.NativeReady 3 t M cache table base)
    (x y : RingProgram.Code (RingProgram.ScalarCode 3 t) d)
    (hframe : CRTLocalProgram.LowFrame base s)
    (hx : s 240 = RingProgram.flat x) (hy : s 241 = RingProgram.flat y)
    (hout : s 244 = []) (htmp : s 245 = []) (regs : Fin 16 → Bool) :
    ∃ steps rf,
      steps ≤ 50000 * (d+1)^3 * (2*t+1)^2 ∧
      Eval HornerProgram.Services.multiply steps (⟨regs, s⟩ : State 16 256)
        ⟨rf, Function.update s 244
          (RingProgram.flat
            (RingProgram.mulRun (RingProgram.scalarProgram 3 t M cache) table x y).1)⟩ ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps+1 →
        Trace (compiled HornerProgram.Services.multiply 240 244) prefixSteps
          ((⟨regs, s⟩ : State 16 256).withPC
            (some (compiled HornerProgram.Services.multiply 240 244).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          stackBits s + 50000 * (d+1)^3 * (2*t+1)^2 := by
  obtain ⟨steps, rf, hsteps, heval⟩ :=
    HornerProgram.Services.multiply_spec 3 t M cache hz table base hready s x y
      hframe hx hy hout htmp regs
  have hbudget : steps ≤ 50000 * (d+1)^3 * (2*t+1)^2 := by
    simpa only [RingProgram.ternary_baseWidth] using
      hsteps.trans (HornerProgram.Services.mulBudget_polynomial (baseWidth 3 t) d)
  refine ⟨steps, rf, hbudget, heval, ?_⟩
  apply StructuredSpace.compiled_halt_stack_bound heval 240 244
  intro prefixSteps intermediate hprefix htrace
  exact StructuredSpace.local_stack_bound _ (steps := 50000 * (d+1)^3 * (2*t+1)^2)
    (initialBound := stackBits s) (by rfl) prefixSteps intermediate
    (hprefix.trans hbudget) htrace

/-- Actual multiplication-table preparation, including its retained power
records, coefficient caches, and every temporary stack. -/
theorem prepare_run_space (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (s : RingProgramTable.Store) (regs : Fin 8 → Bool)
    (hmod : s.modulus = M.bits) (hw : s.width.length = baseWidth 3 t)
    (hdegree : s.degree.length = d) :
    let cache := (RingProgram.prepareScalarCache 3 t M ht).1
    let c := RingProgramTable.modelCoefficients t a
    let start := RingProgramTable.Machine.state regs
      (RingProgramTable.initialStore s c cache.one cache.zero cache.minusOne) []
    ∃ steps rf, steps ≤ 208000*(d+1)^5*(t+1)^2 ∧
      Trace RingProgramTable.Machine.program steps
        (start.withPC (some RingProgramTable.Machine.program.entry))
        ((RingProgramTable.Machine.state rf
          (RingProgramTable.preparedStore 3 t M cache c s)
          (RingProgramTable.modelTable t a M cache)).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace RingProgramTable.Machine.program prefixSteps
          (start.withPC (some RingProgramTable.Machine.program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          stackBits start.stacks + 208000*(d+1)^5*(t+1)^2 := by
  dsimp only
  obtain ⟨rf, steps, hsteps, htrace⟩ :=
    RingProgramTable.model_program_run t ht hd a M s regs hmod hw hdegree
  refine ⟨steps, rf, hsteps, htrace, ?_⟩
  intro prefixSteps intermediate hprefix hp
  exact StructuredSpace.local_stack_bound _ (steps := 208000*(d+1)^5*(t+1)^2)
    (by rfl) prefixSteps intermediate (hprefix.trans hsteps) hp


/-- The complete fixed producer searches the extension polynomial and builds
all native caches from the physical numeric bank. Its all-prefix bound counts
all 640 input, persistent, and temporary stacks. -/
theorem producer_run_space (a : LeafRingSetupProgram.Data)
    (m : LeafParametersProgram.Circuit.Model)
    (w : LeafParametersProgram.Bank.Words) (r : LeafParametersProgram.Bank.Regs)
    (hs : LeafParametersProgram.Circuit.Shape m w)
    (ha : projectState (LeafRingSetupProgram.registers 8 (by decide))
      LeafRingSetupProgram.parameters a = LeafParametersProgram.Bank.state r w)
    (initialWidth V bankWidth S : ℕ)
    (hinit : ∀ i, (a.stacks i).length ≤ initialWidth)
    (hv : ∀ i, (LeafParametersProgram.Circuit.result
      LeafParametersProgram.Serialization.code m).val i ≤ V)
    (hw : ∀ i, (LeafParametersProgram.Circuit.result
      LeafParametersProgram.Serialization.code m).len i ≤ bankWidth)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (hisize : initialWidth ≤ S) (hvsize : V ≤ S) (hwsize : bankWidth ≤ S)
    (hlsize : ∀ i, m.len i ≤ S)
    (htsize : m.val 33 ≤ S) (hdsize : m.val 34 ≤ S) (hqsize : m.val 21 ≤ S)
    (hfield : 3^(m.val 34) ≤ 16*(m.val 21+1)^2) :
    ∃ out : LeafRingSetupProgram.Data,
      ∃ (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
        (cache : RingProgram.ScalarCache 3 (m.val 33))
        (u : RingProgram.ScalarCode 3 (m.val 33)) (steps : ℕ),
      steps ≤ CostAssembly.RingSetup.polynomialEnvelope S+1 ∧
      Trace LeafRingSetupProgram.producerProgram steps
        (a.withPC (some LeafRingSetupProgram.producerProgram.entry)) (out.withPC none) ∧
      LeafRingSetupProgram.Produced m hd M cache u out ∧
      out.stacks 204 = List.replicate (m.val 34) true ∧
      (∀ i, 320 ≤ i.val → i.val < 340 → out.stacks i = a.stacks i) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace LeafRingSetupProgram.producerProgram prefixSteps
          (a.withPC (some LeafRingSetupProgram.producerProgram.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          640*initialWidth + (CostAssembly.RingSetup.polynomialEnvelope S+1) := by
  obtain ⟨steps, hsteps, out, M, cache, u, heval, hproduced, hframe, hdegree⟩ :=
    LeafRingSetupProgram.producerCommand_eval_degree a m w r hs ha initialWidth V bankWidth
      hinit hv hw ht hd
  have htrace := compiled_halt_trace heval (LeafRingSetupProgram.parameters 0) 300
  have hbudget : steps+1 ≤ CostAssembly.RingSetup.polynomialEnvelope S+1 :=
    Nat.add_le_add_right (hsteps.trans
      (CostAssembly.RingSetup.producerBudget_le m initialWidth V bankWidth S
        hisize hvsize hwsize hlsize htsize hdsize hqsize hfield)) 1
  have hinput : dataBits
      (a.withPC (some LeafRingSetupProgram.producerProgram.entry)) ≤ 640*initialWidth :=
    StreamResources.dataBits_le_mul _ hinit
  refine ⟨out, M, cache, u, steps+1, hbudget, htrace, hproduced, hdegree, hframe, ?_⟩
  intro prefixSteps intermediate hprefix hp
  exact StructuredSpace.local_stack_bound _
    (steps := CostAssembly.RingSetup.polynomialEnvelope S+1) hinput
    prefixSteps intermediate (hprefix.trans hbudget) hp

section ProducedLengths

variable {m : LeafParametersProgram.Circuit.Model} {hd : 0 < m.val 34}
    {M : SubexpPreparedQuartic.Modulus 3 (m.val 33)}
    {cache : RingProgram.ScalarCache 3 (m.val 33)}
    {half : RingProgram.ScalarCode 3 (m.val 33)} {out : LeafRingSetupProgram.Data}
    (hp : LeafRingSetupProgram.Produced m hd M cache half out)

include hp

/-- These are the actual retained scalar words, including a binary modulus
whose numerical value is never charged as a unary allocation. -/
theorem produced_scalar_lengths :
    (out.stacks 194).length ≤ 2*m.val 33+1 ∧
    (out.stacks 202).length = 2*m.val 33 ∧
    (out.stacks 203).length = 2*m.val 33 ∧
    (out.stacks 253).length = 2*m.val 33 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hp.caches.modulus]
    simpa only [RingProgram.ternary_baseWidth] using M.length_le
  · simpa only [RingProgram.ternary_baseWidth] using hp.caches.width
  · rw [hp.caches.scalarZero, cache.zero.property, RingProgram.ternary_baseWidth]
  · rw [hp.caches.half, half.property, RingProgram.ternary_baseWidth]

/-- Persistent full coefficients and the cubic table have their physical
widths; the idempotent lift retains only its 3t scalar coefficients. -/
theorem produced_array_lengths :
    (out.stacks 201).length = 2*(m.val 34)^3*m.val 33 ∧
    (out.stacks 207).length = 2*m.val 34*m.val 33 ∧
    (out.stacks 211).length = 2*m.val 34*m.val 33 ∧
    (out.stacks 280).length = 2*m.val 34*m.val 33 ∧
    (out.stacks 281).length = 6*(m.val 33)^2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hp.native.table]
    exact table_length _
  · rw [hp.caches.fullOne_model]
    exact coefficient_length _
  · rw [hp.caches.fullMinusOne, RingProgramTable.literalBits_length,
      RingProgram.ternary_baseWidth]
    ring
  · rw [hp.caches.fullZero_model]
    exact coefficient_length _
  · obtain ⟨M', cache', half', hword, _⟩ := hp.idempotent
    rw [hword, coefficient_length]
    ring

/-- Numeric bank bounds apply to precisely these retained unary masters. -/
theorem produced_unary_lengths :
    (out.stacks 191).length = m.val 0 ∧
    (out.stacks 204).length = m.val 34 ∧
    (out.stacks 212).length = m.val 33 ∧
    (out.stacks 243).length = m.val 42 ∧
    (out.stacks 209).length = (LeafParametersProgram.Circuit.result
      LeafParametersProgram.Serialization.code m).val 44 := by
  exact ⟨by simp [hp.ambient], hp.caches.degree, by simp [hp.caches.precision],
    by simp [hp.jetOrder], by simp [hp.exponent]⟩

/-- Both real node serializations have polynomial length in Q,d,t. -/
theorem produced_node_lengths :
    (out.stacks 256).length = 2*m.val 21*m.val 34*m.val 33 ∧
    (out.stacks 300).length ≤ 1+(4*m.val 34*m.val 33+2)*m.val 21 := by
  constructor
  · rw [hp.flatNodes, LeafRingSetupProgram.nodeWords_flat_length,
      RingProgram.ternary_baseWidth]
    ring
  · rw [hp.framedNodes]
    have h := Encoding.length_encodeList_upper id
      ((LeafRingSetupProgram.nodeWords (m.val 33) (m.val 34) (m.val 21)).map
        RingProgram.flat) (2*m.val 34*m.val 33) (by
          intro word hw
          obtain ⟨code, _, rfl⟩ := List.mem_map.mp hw
          exact (coefficient_length (x := code)).le)
    simp only [List.length_map, LeafRingSetupProgram.nodeWords_length] at h
    convert h using 1
    ring

end ProducedLengths

/-- The producer occupies the original low 640 stacks in the shared leaf ABI.
Its register map retains the original parser/branch register frame. -/
def producerLeafStacks (i : Fin 640) : Fin 896 := i.castAdd 256

theorem producerLeafStacks_injective : Function.Injective producerLeafStacks := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 896 => x.val) h)

def producerLeafCall : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram LeafRingSetupProgram.producerProgram
    LeafRingSetupProgram.wideRegisters producerLeafStacks)

noncomputable def producerLeafResult (base : State 40 896)
    (out : LeafRingSetupProgram.Data) : State 40 896 :=
  embedState LeafRingSetupProgram.wideRegisters producerLeafStacks base out

theorem producerLeafResult_frame (base : State 40 896)
    (out : LeafRingSetupProgram.Data) (i : Fin 896) (hi : 640 ≤ i.val) :
    (producerLeafResult base out).stacks i = base.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  change j.val = i.val at hv
  omega

theorem producerLeafResult_project (base : State 40 896)
    (out : LeafRingSetupProgram.Data) :
    projectState LeafRingSetupProgram.wideRegisters producerLeafStacks
      (producerLeafResult base out) = out :=
  projectState_embed _ _ _ _ LeafRingSetupProgram.wideRegisters_injective
    producerLeafStacks_injective

theorem producerLeafResult_register_frame (base : State 40 896)
    (out : LeafRingSetupProgram.Data) (i : Fin 40)
    (hlo : 16 ≤ i.val) (hhi : i.val < 24) :
    (producerLeafResult base out).regs i = base.regs i := by
  apply embedState_register_frame
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  dsimp [LeafRingSetupProgram.wideRegisters] at hv
  split_ifs at hv <;> simp only at hv <;> omega

/-- This fixed call runs the actual ring search and cache producer in the
shared leaf state. Every caller stack, including the untouched high frame,
is charged in the bound on the same compiled trace. -/
theorem producer_leaf_run_space (base : State 40 896)
    (m : LeafParametersProgram.Circuit.Model)
    (w : LeafParametersProgram.Bank.Words) (r : LeafParametersProgram.Bank.Regs)
    (hs : LeafParametersProgram.Circuit.Shape m w)
    (ha : projectState (LeafRingSetupProgram.registers 8 (by decide))
      LeafRingSetupProgram.parameters
      (projectState LeafRingSetupProgram.wideRegisters producerLeafStacks base) =
        LeafParametersProgram.Bank.state r w)
    (initialWidth V bankWidth S : ℕ)
    (hinit : ∀ i, (base.stacks i).length ≤ initialWidth)
    (hv : ∀ i, (LeafParametersProgram.Circuit.result
      LeafParametersProgram.Serialization.code m).val i ≤ V)
    (hw : ∀ i, (LeafParametersProgram.Circuit.result
      LeafParametersProgram.Serialization.code m).len i ≤ bankWidth)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (hisize : initialWidth ≤ S) (hvsize : V ≤ S) (hwsize : bankWidth ≤ S)
    (hlsize : ∀ i, m.len i ≤ S)
    (htsize : m.val 33 ≤ S) (hdsize : m.val 34 ≤ S) (hqsize : m.val 21 ≤ S)
    (hfield : 3^(m.val 34) ≤ 16*(m.val 21+1)^2) :
    ∃ out : LeafRingSetupProgram.Data,
      ∃ (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
        (cache : RingProgram.ScalarCache 3 (m.val 33))
        (u : RingProgram.ScalarCode 3 (m.val 33)) (steps : ℕ),
      steps ≤ CostAssembly.RingSetup.polynomialEnvelope S+1 ∧
      Eval producerLeafCall steps base (producerLeafResult base out) ∧
      Trace (compiled producerLeafCall 0 300) (steps+1)
        (base.withPC (some (compiled producerLeafCall 0 300).entry))
        ((producerLeafResult base out).withPC none) ∧
      LeafRingSetupProgram.Produced m hd M cache u out ∧
      out.stacks 204 = List.replicate (m.val 34) true ∧
      (∀ i : Fin 640, 320 ≤ i.val → i.val < 340 →
        (producerLeafResult base out).stacks (producerLeafStacks i) =
          base.stacks (producerLeafStacks i)) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps+1 →
        Trace (compiled producerLeafCall 0 300) prefixSteps
          (base.withPC (some (compiled producerLeafCall 0 300).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          896*initialWidth + (CostAssembly.RingSetup.polynomialEnvelope S+1) := by
  obtain ⟨out, M, cache, u, steps, hsteps, htrace, hp, hdegree, hf, _⟩ :=
    producer_run_space
      (projectState LeafRingSetupProgram.wideRegisters producerLeafStacks base)
      m w r hs ha initialWidth V bankWidth S
      (fun i => hinit (producerLeafStacks i)) hv hw ht hd
      hisize hvsize hwsize hlsize htsize hdsize hqsize hfield
  have he : Eval producerLeafCall steps base (producerLeafResult base out) :=
    eval_call_from_state LeafRingSetupProgram.producerProgram
      LeafRingSetupProgram.wideRegisters producerLeafStacks base
      LeafRingSetupProgram.wideRegisters_injective producerLeafStacks_injective htrace
  refine ⟨out, M, cache, u, steps, hsteps, he,
    compiled_halt_trace he 0 300, hp, hdegree, ?_, ?_⟩
  · intro i hlo hhi
    exact (embedState_stack _ _ _ _ producerLeafStacks_injective i).trans (hf i hlo hhi)
  · apply StructuredSpace.compiled_halt_stack_bound he 0 300
    intro prefixSteps intermediate hprefix hpre
    exact StructuredSpace.local_stack_bound _
      (steps := CostAssembly.RingSetup.polynomialEnvelope S+1)
      (StreamResources.dataBits_le_mul _ hinit) prefixSteps intermediate
      (hprefix.trans hsteps) hpre

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingResources
