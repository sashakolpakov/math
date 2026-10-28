import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramCorrect
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramPolynomialCost
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryReadback
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CanonicalWordProgram

/-! Concrete CRT reconstruction and full-word modular readback. The same actual
native traces satisfy correctness, polynomial local time, and every-prefix
bounds on all source stacks, including the persistent caller frame. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace

open OAI BitProgram StructuredCalls SubexpCRTOuterProgram
open SubexpLiftRing SubexpQuarticRing OAI.Algorithms.SubexponentialSAT.SqrtLog
open DensePolynomialProgram ReconstructionProgram.Native

/-- Correct Hasse jets give the actual residue output, with all-prefix local
workspace bounded by the fixed-degree polynomial native runtime. -/
theorem reconstruct_run_space (t : ℕ) (ht : 0 < t) {d Q : ℕ} [NeZero Q] (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (hcanon : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (hzbits : cache.zero.val = List.replicate (baseWidth 3 t) false)
    (J : ℕ) (hJpos : 0 < J) (hB : 0 < baseWidth 3 t)
    (nodes : Fin Q → ReconstructionProgram.Native.Coeff t d) (jets : Fin Q → CRTLocalProgram.Model.Poly (baseWidth 3 t) d J)
    (minusOne : ReconstructionProgram.Native.Coeff t d)
    (hminus : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (input : SubexpCRTOuterProgram.Data)
    (hscalar : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache)
      (ReconstructionProgram.NativeState.arithmeticBase input))
    (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (hpoly : PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t a M cache)
      (ReconstructionProgram.NativeState.arithmeticBase input) scalarWidth frame)
    (hclean : ∀ j ∈ ReconstructionProgram.NativeState.cleanPorts, input.stacks j = [])
    (hzero : input.stacks 280 = RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hone : input.stacks 207 = RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1)
    (hneg : input.stacks 211 = RingProgram.flat minusOne)
    (hJ : input.stacks 243 = List.replicate J true)
    (hnodes : input.stacks 256 = (List.finRange Q).flatMap (fun i => RingProgram.flat (nodes i)))
    (hjets : input.stacks 265 = (List.finRange Q).flatMap (fun i => Fixed.encode (jets i)))
    (hexponent : (input.stacks 209).length = 3^d-2)
    (hprecision : (input.stacks 212).length = t)
    (hdistinct : Function.Injective (fun i => a.rho t ht
      ((RingProgram.modelRing t ht hd a M cache).decode (nodes i))))
    (target : Polynomial (a.O t)) (hdegree : target.natDegree < Q*J)
    (htargetJets : Reconstruction.HasJets (RingProgram.modelRing t ht hd a M cache)
      nodes J (fun i => (jets i).1) target)
    (S : ℕ) (hQsize : Q ≤ S) (hJsize : J ≤ S) (htsize : t ≤ S)
    (hdsize : d ≤ S) (hqsize : 3^d ≤ S)
    (hmodsize : (input.stacks 194).length ≤ S)
    (hwidthsize : (input.stacks 202).length ≤ S)
    (count m n : ℕ) (hcount : count ≤ m*2^n) (hlarge : m*2^n < 3^t)
    (htarget : target.eval 0 = (count : a.O t)) :
    ∃ (b : ReconstructionProgram.Native.Coeff t d) (rf : Fin 16 → Bool) (steps : ℕ),
      steps ≤ 2400*(ReconstructionProgram.Native.costConstant+1)^4*(S+1)^96+1 ∧
      Trace ReconstructionProgram.Native.program steps (input.withPC (some ReconstructionProgram.Native.program.entry))
        ((⟨rf, Function.update (ReconstructionProgram.Entry.prepared input.stacks) 261
          (RingProgram.flat b)⟩ : Data).withPC none) ∧
      (RingProgram.modelRing t ht hd a M cache).decode b = (count : a.O t) ∧
      a.decodeCount t ht ((RingProgram.modelRing t ht hd a M cache).decode b) = count ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace ReconstructionProgram.Native.program prefixSteps (input.withPC (some ReconstructionProgram.Native.program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          stackBits input.stacks + (2400*(ReconstructionProgram.Native.costConstant+1)^4*(S+1)^96+1) := by
  obtain ⟨b, rf, ⟨steps, hsteps, htrace⟩, hvalue, hdecode⟩ :=
    ReconstructionProgram.Native.program_correct t ht hd a M cache hcanon hzbits J hJpos hB nodes jets
      minusOne hminus input hscalar scalarWidth frame hpoly hclean hzero hone hneg
      hJ hnodes hjets hexponent hprecision hdistinct target hdegree htargetJets
      count m n hcount hlarge htarget
  have hbudget : steps ≤ 2400*(ReconstructionProgram.Native.costConstant+1)^4*(S+1)^96+1 :=
    hsteps.trans (ReconstructionProgram.Native.budget_polynomial S Q J t d (input.stacks 194).length
      (input.stacks 202).length hQsize hJsize htsize hdsize hqsize hmodsize hwidthsize)
  refine ⟨b, rf, steps, hbudget, htrace, hvalue, hdecode, ?_⟩
  intro prefixSteps intermediate hprefix hp
  exact StructuredSpace.local_stack_bound _
    (steps := 2400*(ReconstructionProgram.Native.costConstant+1)^4*(S+1)^96+1) (by rfl)
    prefixSteps intermediate (hprefix.trans hbudget) hp


/-- Modular reduction and extraction remain polynomial even when the residue
vector contains noncanonical representatives. -/
theorem readback_budget_le (B S : ℕ) (modulus input : List Bool)
    (hB : B ≤ S) (hmodulus : modulus.length ≤ S) (hinput : input.length ≤ S) :
    SubexpFlatCount.budget B modulus input ≤ 500*(S+1)^2 := by
  unfold SubexpFlatCount.budget
  nlinarith [Nat.mul_self_le_mul_self
    (show modulus.length + B + 1 ≤ 2*S+1 by omega)]

/-- The actual reader produces a complete little-endian count word; its Boolean
head is not used as a satisfiability answer. The caller later normalizes this
word and computes positivity on the separate answer stack. -/
theorem readback_run_space (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (x : RingProgram.Code (RingProgram.ScalarCode 3 t) d) (count : ℕ)
    (hcount : count < 3^t)
    (hx : (RingProgram.modelRing t ht hd a M cache).decode x = (count : a.O t))
    (regs : Fin 8 → Bool) (modulus width : List Bool)
    (hm : BinaryArithmetic.toNat modulus = 3^t)
    (hw : width.length = baseWidth 3 t)
    (S : ℕ) (hB : baseWidth 3 t ≤ S) (hmodulus : modulus.length ≤ S)
    (hinput : (RingProgram.flat x).length ≤ S) :
    ∃ finalRegs word steps, BinaryArithmetic.toNat word = count ∧
      word.length = modulus.length + baseWidth 3 t ∧ steps ≤ 500*(S+1)^2 ∧
      Trace LeafProgram.Readback.countProgram steps
        ((SubexpFlatCount.start regs modulus width (RingProgram.flat x)).withPC
          (some LeafProgram.Readback.countProgram.entry))
        (⟨none, finalRegs, SubexpFlatCount.store word modulus [] width⟩ : Cfg 8 8 _) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace LeafProgram.Readback.countProgram prefixSteps
          ((SubexpFlatCount.start regs modulus width (RingProgram.flat x)).withPC
            (some LeafProgram.Readback.countProgram.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          stackBits (SubexpFlatCount.start regs modulus width (RingProgram.flat x)).stacks +
            500*(S+1)^2 := by
  obtain ⟨finalRegs, word, hvalue, hlength, steps, hsteps, htrace⟩ :=
    LeafProgram.Readback.model_countProgram_run t ht hd a M cache x count hcount hx
      regs modulus width hm hw
  have hbudget : steps ≤ 500*(S+1)^2 := hsteps.trans
    (readback_budget_le (baseWidth 3 t) S modulus (RingProgram.flat x) hB hmodulus hinput)
  refine ⟨finalRegs, word, steps, hvalue, hlength, hbudget, htrace, ?_⟩
  intro prefixSteps intermediate hprefix hp
  exact StructuredSpace.local_stack_bound _ (steps := 500*(S+1)^2)
    (by rfl) prefixSteps intermediate (hprefix.trans hbudget) hp

/-- The normalizer uses the count port and two empty low scratch ports.
Modulus and width remain in their existing high ports. -/
def normalizationPorts : Fin 3 ↪ Fin 8 :=
  ⟨Fin.castAdd 5, Fin.castAdd_injective _ _⟩

def normalizeReadback : Cmd 8 8 :=
  .call (ProgramLinking.liftProgram
    DisjointReuse.CanonicalWordProgram.normalizeUnsignedProgram
    normalizationPorts normalizationPorts)

theorem normalize_readback_eval (regs : Fin 8 → Bool)
    (word modulus width : List Bool) :
    ∃ finalRegs steps, steps ≤ 17*word.length+29 ∧
      Eval normalizeReadback steps
        (SubexpFlatCount.start regs modulus width word)
        (SubexpFlatCount.start finalRegs modulus width
          (DisjointReuse.binaryNat (BinaryArithmetic.toNat word))) := by
  let initialState := SubexpFlatCount.start regs modulus width word
  let localInput := DisjointReuse.CanonicalWordProgram.state
    (regs ∘ normalizationPorts) word []
  let localOutput := DisjointReuse.CanonicalWordProgram.state
    DisjointReuse.CanonicalWordProgram.zeroRegs
    (DisjointReuse.binaryNat (CounterPrograms.value word)) []
  have hproject : projectState normalizationPorts normalizationPorts initialState =
      localInput := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> rfl
  obtain ⟨steps, hsteps, hrun⟩ :=
    DisjointReuse.CanonicalWordProgram.normalizeUnsigned_call
      normalizationPorts normalizationPorts initialState
      (regs ∘ normalizationPorts) word
  change Eval normalizeReadback steps
    (embedState normalizationPorts normalizationPorts initialState localInput)
    (embedState normalizationPorts normalizationPorts initialState localOutput) at hrun
  rw [← hproject, embedState_project _ _ _ normalizationPorts.injective
    normalizationPorts.injective] at hrun
  let finalState := embedState normalizationPorts normalizationPorts initialState localOutput
  have hstack : finalState.stacks = SubexpFlatCount.store
      (DisjointReuse.binaryNat (BinaryArithmetic.toNat word)) modulus [] width := by
    funext i
    by_cases hi : i.val < 3
    · let j : Fin 3 := ⟨i.val, hi⟩
      have hij : normalizationPorts j = i := Fin.ext rfl
      rw [← hij]
      change (embedState normalizationPorts normalizationPorts initialState localOutput).stacks
          (normalizationPorts j) = _
      rw [embedState_stack _ _ _ _ normalizationPorts.injective]
      clear_value j
      clear hij hi i
      fin_cases j <;>
        simp [localOutput, DisjointReuse.CanonicalWordProgram.state,
          normalizationPorts, SubexpFlatCount.store, CounterPrograms.value_eq_toNat]
    · have hframe : ¬ ∃ j, normalizationPorts j = i := by
        rintro ⟨j, hj⟩
        apply hi
        rw [← hj]
        exact j.isLt
      change (embedState normalizationPorts normalizationPorts initialState localOutput).stacks i = _
      rw [embedState_stack_frame _ _ _ _ i hframe]
      fin_cases i <;> simp_all [initialState, SubexpFlatCount.start, SubexpFlatCount.store]
  have hfinal : finalState = SubexpFlatCount.start finalState.regs modulus width
      (DisjointReuse.binaryNat (BinaryArithmetic.toNat word)) := by
    exact congrArg₂ StructuredProgram.State.mk rfl hstack
  refine ⟨finalState.regs, steps, hsteps, ?_⟩
  change Eval normalizeReadback steps initialState finalState at hrun
  rwa [hfinal] at hrun

/-- A fixed reader followed by the actual unsigned normalizer. Zero has the
canonical one-bit output `[false]`, and positive counts retain all their bits. -/
def canonicalReadback : Cmd 8 8 :=
  .seq (.call LeafProgram.Readback.countProgram) normalizeReadback

def canonicalReadbackProgram := compiled canonicalReadback 0 0

/-- Native reconstruction readback returns precisely the frozen binary word.
The same trace has polynomial local time and bounds every source stack at
every prefix, including modulus, width, and normalization scratch. -/
theorem canonical_readback_run_space (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (x : RingProgram.Code (RingProgram.ScalarCode 3 t) d) (count : ℕ)
    (hcount : count < 3^t)
    (hx : (RingProgram.modelRing t ht hd a M cache).decode x = (count : a.O t))
    (regs : Fin 8 → Bool) (modulus width : List Bool)
    (hm : BinaryArithmetic.toNat modulus = 3^t)
    (hw : width.length = baseWidth 3 t)
    (S : ℕ) (hB : baseWidth 3 t ≤ S) (hmodulus : modulus.length ≤ S)
    (hinput : (RingProgram.flat x).length ≤ S) :
    ∃ finalRegs steps, steps ≤ 600*(S+1)^2 ∧
      Trace canonicalReadbackProgram steps
        ((SubexpFlatCount.start regs modulus width (RingProgram.flat x)).withPC
          (some canonicalReadbackProgram.entry))
        ((SubexpFlatCount.start finalRegs modulus width
          (DisjointReuse.binaryNat count)).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace canonicalReadbackProgram prefixSteps
          ((SubexpFlatCount.start regs modulus width (RingProgram.flat x)).withPC
            (some canonicalReadbackProgram.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          stackBits (SubexpFlatCount.start regs modulus width (RingProgram.flat x)).stacks +
            600*(S+1)^2 := by
  obtain ⟨readerRegs, word, readerSteps, hvalue, hlength, hsteps, hreader, _⟩ :=
    readback_run_space t ht hd a M cache x count hcount hx regs modulus width hm hw
      S hB hmodulus hinput
  obtain ⟨finalRegs, normalSteps, hnormalSteps, hnormal⟩ :=
    normalize_readback_eval readerRegs word modulus width
  rw [hvalue] at hnormal
  have heval : Eval canonicalReadback (readerSteps+normalSteps)
      (SubexpFlatCount.start regs modulus width (RingProgram.flat x))
      (SubexpFlatCount.start finalRegs modulus width (DisjointReuse.binaryNat count)) :=
    (Eval.call LeafProgram.Readback.countProgram hreader).seq hnormal
  have hbudget : readerSteps+normalSteps+1 ≤ 600*(S+1)^2 := by
    rw [hlength] at hnormalSteps
    nlinarith only [hsteps, hnormalSteps, hB, hmodulus]
  refine ⟨finalRegs, readerSteps+normalSteps+1, hbudget,
    compiled_halt_trace heval 0 0, ?_⟩
  intro prefixSteps intermediate hprefix hp
  exact StructuredSpace.local_stack_bound _ (steps := 600*(S+1)^2)
    (by rfl) prefixSteps intermediate (hprefix.trans hbudget) hp

/-- Only the eight explicitly assigned ports participate in the reader call.
The enclosing streaming machine may keep its tuple and signature frame on any
other ports, independently of the number of calls. -/
def canonicalReadbackCall {R S : ℕ}
    (register : Fin 8 ↪ Fin R) (stack : Fin 8 ↪ Fin S) : Cmd R S :=
  .call (ProgramLinking.liftProgram canonicalReadbackProgram register stack)

theorem canonical_readback_call {R S : ℕ}
    (register : Fin 8 ↪ Fin R) (stack : Fin 8 ↪ Fin S) (frame : State R S)
    (regs finalRegs : Fin 8 → Bool) (input modulus width : List Bool)
    (count steps : ℕ)
    (htrace : Trace canonicalReadbackProgram steps
      ((SubexpFlatCount.start regs modulus width input).withPC
        (some canonicalReadbackProgram.entry))
      ((SubexpFlatCount.start finalRegs modulus width
        (DisjointReuse.binaryNat count)).withPC none)) :
    Eval (canonicalReadbackCall register stack) steps
      (embedState register stack frame (SubexpFlatCount.start regs modulus width input))
      (embedState register stack frame (SubexpFlatCount.start finalRegs modulus width
        (DisjointReuse.binaryNat count))) ∧
    (embedState register stack frame (SubexpFlatCount.start finalRegs modulus width
      (DisjointReuse.binaryNat count))).stacks (stack 0) = DisjointReuse.binaryNat count ∧
    ∀ i, (¬ ∃ j, stack j = i) →
      (embedState register stack frame (SubexpFlatCount.start finalRegs modulus width
        (DisjointReuse.binaryNat count))).stacks i = frame.stacks i := by
  refine ⟨eval_call_lifted canonicalReadbackProgram register stack frame
    register.injective stack.injective htrace, ?_, ?_⟩
  · exact embedState_stack register stack frame _ stack.injective 0
  · intro i hi
    exact embedState_stack_frame register stack frame _ i hi

theorem readback_input_bits (regs : Fin 8 → Bool) (input modulus width : List Bool) :
    stackBits (SubexpFlatCount.start regs modulus width input).stacks =
      input.length + modulus.length + width.length := by
  simp [stackBits, SubexpFlatCount.start, SubexpFlatCount.store, Fin.sum_univ_succ,
    Nat.add_assoc]

/-- The existing query ABI is retained: reconstructed coefficients enter on
261, the canonical count leaves on 323, and 324 is the transfer scratch. -/
def canonicalQueryReadCommand : Cmd 19 330 :=
  .call (ProgramLinking.liftProgram canonicalReadbackProgram
    LeafProgram.QueryReadback.regMap LeafProgram.QueryReadback.stackMap)

def canonicalQueryCommand : Cmd 19 330 :=
  .seq canonicalQueryReadCommand LeafProgram.QueryReadback.moveCommand

def canonicalQueryProgram := compiled canonicalQueryCommand 261 323

theorem canonical_query_run_space (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (model : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (x : RingProgram.Code (RingProgram.ScalarCode 3 t) d) (count : ℕ)
    (hcount : count < 3^t)
    (hx : (RingProgram.modelRing t ht hd model M cache).decode x = (count : model.O t))
    (a : LeafProgram.QueryReadback.Data) (regs : Fin 8 → Bool) (modulus width : List Bool)
    (hm : BinaryArithmetic.toNat modulus = 3^t) (hw : width.length = baseWidth 3 t)
    (ready : LeafProgram.QueryReadback.project a =
      SubexpFlatCount.start regs modulus width (RingProgram.flat x))
    (hs : a.stacks 323 = []) (ha : a.stacks 324 = [])
    (S : ℕ) (hB : baseWidth 3 t ≤ S) (hmodulus : modulus.length ≤ S)
    (hinput : (RingProgram.flat x).length ≤ S) :
    ∃ steps b, steps+1 ≤ 4400*(S+1)^2 ∧
      Eval canonicalQueryCommand steps a b ∧
      Trace canonicalQueryProgram (steps+1)
        (a.withPC (some canonicalQueryProgram.entry)) (b.withPC none) ∧
      b.stacks 323 = DisjointReuse.binaryNat count ∧ b.stacks 324 = [] ∧
      (∀ i, (¬ ∃ j, LeafProgram.QueryReadback.stackMap j = i) →
        i ≠ 323 → i ≠ 324 → b.stacks i = a.stacks i) ∧
      (∃ finalRegs : Fin 8 → Bool, b = LeafProgram.QueryReadback.afterMove
        (LeafProgram.QueryReadback.install a (SubexpFlatCount.start finalRegs modulus width
          (DisjointReuse.binaryNat count)))) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps+1 →
        Trace canonicalQueryProgram prefixSteps
          (a.withPC (some canonicalQueryProgram.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ stackBits a.stacks + 4400*(S+1)^2 := by
  obtain ⟨finalRegs, readSteps, hreadSteps, htrace, hlocal⟩ :=
    canonical_readback_run_space t ht hd model M cache x count hcount hx
      regs modulus width hm hw S hB hmodulus hinput
  let localFinal := SubexpFlatCount.start finalRegs modulus width (DisjointReuse.binaryNat count)
  let middle := LeafProgram.QueryReadback.install a localFinal
  have hread : Eval canonicalQueryReadCommand readSteps a middle := by
    have hh := eval_call_lifted canonicalReadbackProgram
      LeafProgram.QueryReadback.regMap LeafProgram.QueryReadback.stackMap a
      LeafProgram.QueryReadback.regMap_injective LeafProgram.QueryReadback.stackMap_injective htrace
    change Eval canonicalQueryReadCommand readSteps
      (LeafProgram.QueryReadback.install a
        (SubexpFlatCount.start regs modulus width (RingProgram.flat x))) middle at hh
    rw [← ready, LeafProgram.QueryReadback.install_project] at hh
    exact hh
  have hframe : ∀ i, (¬ ∃ j, LeafProgram.QueryReadback.stackMap j = i) →
      middle.stacks i = a.stacks i := by
    intro i hi
    exact embedState_stack_frame _ _ _ _ i hi
  have hs' : middle.stacks 323 = [] := (hframe 323 (by decide)).trans hs
  have ha' : middle.stacks 324 = [] := (hframe 324 (by decide)).trans ha
  have hword : middle.stacks 261 = DisjointReuse.binaryNat count :=
    embedState_stack LeafProgram.QueryReadback.regMap LeafProgram.QueryReadback.stackMap
      a localFinal LeafProgram.QueryReadback.stackMap_injective 0
  have hlength := hlocal readSteps _ le_rfl htrace (0 : Fin 8)
  change (DisjointReuse.binaryNat count).length ≤
    stackBits (SubexpFlatCount.start regs modulus width (RingProgram.flat x)).stacks +
      600*(S+1)^2 at hlength
  rw [readback_input_bits, hw] at hlength
  have heval := hread.seq (LeafProgram.QueryReadback.move_eval middle ha')
  have hbudget : readSteps+(6*(middle.stacks 261).length+6)+1 ≤ 4400*(S+1)^2 := by
    rw [hword]
    nlinarith only [hreadSteps, hlength, hB, hmodulus, hinput]
  refine ⟨readSteps+(6*(middle.stacks 261).length+6),
    LeafProgram.QueryReadback.afterMove middle, hbudget, heval,
    compiled_halt_trace heval 261 323, ?_, LeafProgram.QueryReadback.afterMove_scratch _, ?_,
    ⟨finalRegs, rfl⟩, ?_⟩
  · rw [LeafProgram.QueryReadback.afterMove_output _ hs' ha', hword]
  · intro i hi hi323 hi324
    have hi261 : i ≠ 261 := by
      intro h
      apply hi
      exact ⟨0, h.symm⟩
    rw [LeafProgram.QueryReadback.afterMove_frame _ _ hi261 hi323 hi324]
    exact hframe i hi
  · intro prefixSteps intermediate hprefix hp
    exact StructuredSpace.local_stack_bound _ (steps := 4400*(S+1)^2)
      (by rfl) prefixSteps intermediate (hprefix.trans hbudget) hp

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace
