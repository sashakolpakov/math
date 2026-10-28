import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.EncodingBounds

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls

theorem positivity_eval {r s : ℕ} (ports : CounterForPrograms.Ports r s)
    (answer : Fin s) (a : State r s) (hs : a.stacks ports.scratch = []) :
    Eval (positivity ports answer) (8 * (a.stacks ports.counter).length + 8)
      a (positivityResult ports answer a) := by
  simpa only [positivity, positivityResult, Nat.add_assoc] using
    Eval.seq (CounterForPrograms.test_eval ports a hs)
      (Eval.base (StructuredProgram.Eval.atom
        (.push answer (ports.register 2)) (CounterForPrograms.testResult ports a)))

theorem positivityResult_stacks {r s : ℕ} (ports : CounterForPrograms.Ports r s)
    (answer : Fin s) (a : State r s) (hs : a.stacks ports.scratch = []) :
    (positivityResult ports answer a).stacks = Function.update a.stacks answer
      ((!CounterPrograms.isZero (a.stacks ports.counter)) :: a.stacks answer) := by
  simp only [positivityResult, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr,
    CounterForPrograms.testResult_flag, CounterForPrograms.testResult_stacks ports a hs]

theorem positivityResult_count {r s : ℕ} (ports : CounterForPrograms.Ports r s)
    (answer : Fin s) (a : State r s) (hs : a.stacks ports.scratch = [])
    (ha : ports.counter ≠ answer) :
    (positivityResult ports answer a).stacks ports.counter = a.stacks ports.counter := by
  rw [positivityResult_stacks ports answer a hs, Function.update_of_ne ha]

theorem positivityResult_answer {r s : ℕ} (ports : CounterForPrograms.Ports r s)
    (answer : Fin s) (a : State r s) (hs : a.stacks ports.scratch = [])
    (ha : a.stacks answer = []) :
    (positivityResult ports answer a).stacks answer =
      [decide (0 < BinaryArithmetic.toNat (a.stacks ports.counter))] := by
  rw [positivityResult_stacks ports answer a hs, Function.update_self, ha]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp [CounterPrograms.isZero_eq_false_iff, CounterPrograms.value_eq_toNat]

theorem clearOutput_eval (port : Fin 1220) (a : State 80 1220) :
    Eval (clearOutput port) (2 * (a.stacks port).length + 3) a
      (clearOutputState port a) :=
  .call _ (ListRegisterProgram.clear_run port 72 73 a.regs a.stacks)

theorem answerReady_count (a : State 80 1220) :
    (answerReady a).stacks ABI.countStack = a.stacks ABI.countStack := by
  simp [answerReady, clearOutputState, ABI.countStack, ABI.answerStack, ABI.positivityScratch]

theorem answerReady_scratch (a : State 80 1220) :
    (answerReady a).stacks ABI.positivityScratch = [] := by
  simp [answerReady, clearOutputState]

theorem answerReady_answer (a : State 80 1220) :
    (answerReady a).stacks ABI.answerStack = [] := by
  simp [answerReady, clearOutputState, ABI.answerStack, ABI.positivityScratch]

theorem answerCommand_eval (a : State 80 1220) :
    Eval answerCommand (answerSteps a - 1) a (answerResult a) := by
  have hp := positivity_eval positivityPorts ABI.answerStack (answerReady a)
    (answerReady_scratch a)
  have hs := clearOutput_eval ABI.positivityScratch (clearOutputState ABI.answerStack a)
  have ha := clearOutput_eval ABI.answerStack a
  have h := ha.seq (hs.seq hp)
  have he : (clearOutputState ABI.answerStack a).stacks ABI.positivityScratch =
      a.stacks ABI.positivityScratch := by
    simp [clearOutputState, ABI.answerStack, ABI.positivityScratch]
  convert h using 1
  · rfl
  · simp only [answerSteps, positivityPorts, answerReady_count, he]
    omega
  · rfl

theorem answerResult_count (a : State 80 1220) :
    (answerResult a).stacks ABI.countStack = a.stacks ABI.countStack := by
  exact (positivityResult_count positivityPorts ABI.answerStack (answerReady a)
    (answerReady_scratch a) ABI.countStack_ne_answerStack).trans (answerReady_count a)

theorem answerResult_answer (a : State 80 1220) :
    (answerResult a).stacks ABI.answerStack =
      [decide (0 < BinaryArithmetic.toNat (a.stacks ABI.countStack))] := by
  have h := positivityResult_answer positivityPorts ABI.answerStack (answerReady a)
    (answerReady_scratch a) (answerReady_answer a)
  simpa only [answerResult, positivityPorts, answerReady_count] using h

theorem answer_trace (a : State 80 1220) :
    Trace answerProgram (answerSteps a) (a.withPC (some answerProgram.entry))
      ((answerResult a).withPC none) := by
  have h := compiled_halt_trace (answerCommand_eval a) ABI.countStack ABI.answerStack
  have hsteps : 1 ≤ answerSteps a := by simp [answerSteps]
  simpa only [answerProgram, Nat.sub_add_cancel hsteps] using h

theorem powerBody_eval (n : ℕ) (output : List Bool) :
    Eval powerBody 3 (powerBoundary (n + 1) output)
      (powerBoundary n (false :: output)) := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 2) false)
      (powerBoundary (n + 1) output)).seq
    ((StructuredProgram.Eval.atom (.push (1 : Fin 2) 0) _).seq
      (StructuredProgram.Eval.atom (.pop (0 : Fin 2) 0 1) _))
  apply Eval.base
  convert h using 1
  cases n <;> apply CounterForPrograms.data_ext <;> funext i <;> fin_cases i <;>
    simp [powerBoundary, powerState, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
      execInstr, readRegs, Encoding.encodeNat,
      List.replicate_succ]

theorem powerLoop_eval (n : ℕ) (output : List Bool) :
    Eval (.while 0 powerBody) (4 * n + 1) (powerBoundary n output)
      (powerState false [] (List.replicate n false ++ output)) := by
  induction n generalizing output with
  | zero => exact .while_false rfl
  | succ n ih =>
      have h := Eval.while_true (test := (0 : Fin 2)) (by rfl)
        (powerBody_eval n output) (ih (false :: output))
      convert h using 1
      · omega
      · congr 1
        simp [List.replicate_succ', List.append_assoc]

theorem powerSeed_eval (regs : Fin 2 → Bool) (n : ℕ) :
    Eval powerSeed 3 ⟨regs, ![Encoding.encodeNat n, []]⟩ (powerBoundary n [true]) := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 2) true)
      (⟨regs, ![Encoding.encodeNat n, []]⟩ : State 2 2)).seq
    ((StructuredProgram.Eval.atom (.push (1 : Fin 2) 0) _).seq
      (StructuredProgram.Eval.atom (.pop (0 : Fin 2) 0 1) _))
  apply Eval.base
  convert h using 1
  cases n <;> apply CounterForPrograms.data_ext <;> funext i <;> fin_cases i <;>
    simp [powerBoundary, powerState, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
      execInstr, readRegs, Encoding.encodeNat,
      List.replicate_succ]

theorem powerCommand_eval (regs : Fin 2 → Bool) (n : ℕ) :
    Eval powerCommand (4 * n + 4) ⟨regs, ![Encoding.encodeNat n, []]⟩
      (powerState false [] (List.replicate n false ++ [true])) := by
  convert (powerSeed_eval regs n).seq (powerLoop_eval n [true]) using 1
  · rfl
  · omega

theorem power_count_trace (regs : Fin 2 → Bool) (n : ℕ) :
    Trace powerProgram (4 * n + 5)
      ((⟨regs, ![Encoding.encodeNat n, []]⟩ : State 2 2).withPC
        (some powerProgram.entry))
      ((powerState false [] (countWord (2 ^ n))).withPC none) := by
  simpa only [powerProgram, powerWord_countWord, Nat.add_assoc] using
    compiled_halt_trace (powerCommand_eval regs n) 0 1

theorem copyInput_eval (input : List Bool) :
    Eval copyInput (7 * input.length + 5) (StructuredProgram.ioState ABI.countStack input)
      (copiedInput input) := by
  have h := ListRegisterProgram.copy_run (r := 80) ABI.countStack
    (1218 : Fin 1220) 1219 72 73 (by decide) (by decide) (by decide) (by decide)
    (fun _ => false) (StructuredProgram.ioState (r := 80) ABI.countStack input).stacks
    (by simp [ABI.countStack])
  apply Eval.call
  simpa [copiedInput, StructuredProgram.ioState, ABI.countStack, readRegs,
    StackRoutines.copyStacks, ListRegisterProgram.Run, StructuredProgram.State.withPC] using h

theorem copiedInput_projection (input : List Bool) :
    (projectState ABI.positivityRegisters headerStacks (copiedInput input)).withPC
      (some FrontendProgram.initializeProgram.entry) =
      initial FrontendProgram.initializeProgram input := by
  rw [FrontendProgram.initialize_initial]
  apply congrArg₂ (Cfg.mk (some 0))
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> simp [projectState, copiedInput, headerStacks,
      ABI.countStack, FrontendProgram.storage]

theorem header_eval (n : ℕ) (body : List Bool) :
    ∃ binary steps, BinaryArithmetic.toNat binary = n ∧ binary.length ≤ n ∧
      steps ≤ 7 * (Encoding.encodeNat n ++ body).length + 5 +
        FrontendProgram.initializeBound n ∧
      Eval headerCommand steps
        (StructuredProgram.ioState ABI.countStack (Encoding.encodeNat n ++ body))
        (headerResult (Encoding.encodeNat n ++ body) body binary) := by
  obtain ⟨binary, hv, hl, steps, hs, ht⟩ := FrontendProgram.initialize_raw n body
  have he := eval_call_from_state FrontendProgram.initializeProgram ABI.positivityRegisters
    headerStacks (copiedInput (Encoding.encodeNat n ++ body))
    ABI.positivityRegisters.injective headerStacks.injective
    (n := steps) (b := StructuredProgram.State.ofCfg
      (FrontendProgram.cfg none false false body [] binary []))
    (by
      rw [copiedInput_projection]
      exact ht)
  refine ⟨binary, (7 * (Encoding.encodeNat n ++ body).length + 5) + steps,
    ?_, hl, by omega, (copyInput_eval _).seq he⟩
  exact (CounterPrograms.value_eq_toNat binary).symm.trans hv

theorem headerResult_input (input body binary : List Bool) :
    (headerResult input body binary).stacks ABI.countStack = input := by
  rw [headerResult, embedState_stack_frame]
  · simp [copiedInput, ABI.countStack]
  · rintro ⟨i, hi⟩
    fin_cases i <;> simp [headerStacks, ABI.countStack] at hi

theorem headerResult_binary (input body binary : List Bool) :
    (headerResult input body binary).stacks 267 = binary :=
  embedState_stack ABI.positivityRegisters headerStacks (copiedInput input) _
    headerStacks.injective 2

theorem headerResult_body (input body binary : List Bool) :
    (headerResult input body binary).stacks 1218 = body :=
  embedState_stack ABI.positivityRegisters headerStacks (copiedInput input) _
    headerStacks.injective 0

theorem headerResult_other (input body binary : List Bool) (i : Fin 1220)
    (hc : i ≠ ABI.countStack) (hn : i ≠ 267) (hb : i ≠ 1218) :
    (headerResult input body binary).stacks i = [] := by
  by_cases hi : ∃ j, headerStacks j = i
  · obtain ⟨j, rfl⟩ := hi
    change StructuredProgram.State.stacks
      (embedState ABI.positivityRegisters headerStacks (copiedInput input)
        (StructuredProgram.State.ofCfg (FrontendProgram.cfg none false false body [] binary [])))
      (headerStacks j) = []
    rw [embedState_stack _ _ _ _ headerStacks.injective]
    fin_cases j <;> simp [headerStacks] at hn hb ⊢ <;> rfl
  · rw [headerResult, embedState_stack_frame _ _ _ _ i hi]
    simp [copiedInput, Function.update_of_ne hb, hc]

theorem header_trace (n : ℕ) (body : List Bool) :
    ∃ binary steps, BinaryArithmetic.toNat binary = n ∧ binary.length ≤ n ∧
      steps ≤ 7 * (Encoding.encodeNat n ++ body).length + 6 +
        FrontendProgram.initializeBound n ∧
      Trace headerProgram steps
        (initial headerProgram (Encoding.encodeNat n ++ body))
        ((headerResult (Encoding.encodeNat n ++ body) body binary).withPC none) := by
  obtain ⟨binary, steps, hv, hl, hs, he⟩ := header_eval n body
  exact ⟨binary, steps + 1, hv, hl, by omega,
    compiled_halt_trace he ABI.countStack ABI.answerStack⟩

theorem copyWord_eval (src dst scratch : Fin 1220) (a : State 80 1220)
    (hsd : src ≠ dst) (hst : src ≠ scratch) (htd : scratch ≠ dst)
    (hblank : a.stacks scratch = []) :
    Eval (copyWord src dst scratch) (7 * (a.stacks src).length + 5) a
      (copiedWord src dst a) :=
  Eval.call _ (ListRegisterProgram.copy_run src dst scratch 72 73 hsd hst htd
    (by decide) a.regs a.stacks hblank)

theorem clearSequence_eval (ports : List (Fin 1220)) (a : State 80 1220) (B : ℕ)
    (hbound : ∀ i, (a.stacks i).length ≤ B) :
    ∃ steps b, steps ≤ (2 * B + 3) * ports.length ∧
      Eval (clearSequence ports) steps a b ∧
      (∀ i ∈ ports, b.stacks i = []) ∧
      (∀ i, i ∉ ports → b.stacks i = a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ B) := by
  induction ports generalizing a with
  | nil => exact ⟨0, a, by simp, .base (.skip a), by simp, by simp, hbound⟩
  | cons port rest ih =>
    have hlocal : ∀ i, ((clearOutputState port a).stacks i).length ≤ B := by
      intro i
      by_cases hi : i = port
      · subst i; simp [clearOutputState]
      · simpa [clearOutputState, hi] using hbound i
    obtain ⟨steps, b, hs, he, hc, hf, hb⟩ := ih (clearOutputState port a) hlocal
    refine ⟨2 * (a.stacks port).length + 3 + steps, b, ?_,
      (clearOutput_eval port a).seq he, ?_, ?_, hb⟩
    · have := hbound port
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega
    · intro i hi
      rcases List.mem_cons.mp hi with hip | hi
      · subst i
        by_cases hp : port ∈ rest
        · exact hc port hp
        · rw [hf port hp]; simp [clearOutputState]
      · exact hc i hi
    · intro i hi
      have hip : i ≠ port := fun h => hi (List.mem_cons.mpr (.inl h))
      have hir : i ∉ rest := fun h => hi (List.mem_cons.mpr (.inr h))
      rw [hf i hir]
      simp [clearOutputState, hip]

theorem clearLeaf_eval (a : State 80 1220) (B : ℕ)
    (hbound : ∀ i, (a.stacks i).length ≤ B) :
    ∃ steps b, steps ≤ 896 * (2 * B + 3) ∧ Eval clearLeaf steps a b ∧
      (∀ j : Fin 896, b.stacks (ABI.leafStacks j) = []) ∧
      (∀ i, (¬ ∃ j, ABI.leafStacks j = i) → b.stacks i = a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ B) := by
  obtain ⟨steps, b, hs, he, hc, hf, hb⟩ := clearSequence_eval leafPorts a B hbound
  refine ⟨steps, b, ?_, he, ?_, ?_, hb⟩
  · simpa [leafPorts_eq, Nat.mul_comm] using hs
  · intro j; exact hc _ (by simp [leafPorts_eq])
  · intro i hi
    exact hf i (by simpa [leafPorts_eq] using hi)

theorem copyWord_bound (src dst : Fin 1220) (a : State 80 1220) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) (hd : a.stacks dst = []) :
    ∀ i, ((copiedWord src dst a).stacks i).length ≤ B := by
  intro i
  by_cases hi : i = dst
  · subst i; simpa [copiedWord, StackRoutines.copyStacks, hd] using ha src
  · simpa [copiedWord, StackRoutines.copyStacks, hi] using ha i

theorem clearOutput_bound (port : Fin 1220) (a : State 80 1220) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((clearOutputState port a).stacks i).length ≤ B := by
  intro i
  by_cases hi : i = port
  · subst i; simp [clearOutputState]
  · simpa [clearOutputState, hi] using ha i

theorem resetRegisters_eval (ports : List (Fin 80)) (a : State 80 1220) :
    Eval (resetRegisters ports) ports.length a (resetRegisterState ports a) := by
  induction ports generalizing a with
  | nil => simpa [resetRegisters, resetRegisterState] using (Eval.base (.skip a))
  | cons i rest ih =>
    have h := (Eval.base (StructuredProgram.Eval.atom (.set i false) a)).seq
      (ih ((StructuredProgram.Atom.set i false).eval a))
    convert h using 1
    · rfl
    · simp only [List.length_cons, Nat.add_comm]
    · apply CounterForPrograms.data_ext
      · funext j
        by_cases hj : j = i <;> by_cases hr : j ∈ rest <;>
          simp [resetRegisterState, StructuredProgram.Atom.eval,
            StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
            execInstr, hj, hr]
      · rfl

theorem resetLeafRegisters_eval (a : State 80 1220) :
    Eval resetLeafRegisters 40 a (resetLeafState a) := by
  simpa [resetLeafRegisters, resetLeafState, leafRegisterPorts] using
    resetRegisters_eval leafRegisterPorts a

theorem loadLeaf_eval (a : State 80 1220) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∃ steps b, steps ≤ 1815 * B + 2746 ∧ Eval loadLeaf steps a b ∧
      b.stacks 1104 = a.stacks 265 ∧ b.stacks 1105 = a.stacks 267 ∧
      b.stacks 1106 = a.stacks 264 ∧ b.stacks 1219 = [] ∧
      (∀ j : Fin 896, ABI.leafStacks j ≠ 1104 → ABI.leafStacks j ≠ 1105 →
        ABI.leafStacks j ≠ 1106 → b.stacks (ABI.leafStacks j) = []) ∧
      (∀ i, (¬ ∃ j, ABI.leafStacks j = i) → i ≠ 1219 → b.stacks i = a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ B) ∧ (∀ j, b.regs (ABI.leafRegisters j) = false) := by
  obtain ⟨t, e, ht, he, hempty, hframe, hb⟩ := clearLeaf_eval a B ha
  let d0 := clearOutputState 1219 (resetLeafState e)
  let d1 := copiedWord 265 1104 d0
  let d2 := copiedWord 267 1105 d1
  let d3 := copiedWord 264 1106 d2
  have hfr (i : Fin 1220) (hi : i.val < 320) : e.stacks i = a.stacks i := by
    apply hframe
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change 320 + j.val = i.val at hv
    omega
  have h1104 : e.stacks 1104 = [] := hempty 784
  have h1105 : e.stacks 1105 = [] := hempty 785
  have h1106 : e.stacks 1106 = [] := hempty 786
  have hreset := resetLeafRegisters_eval e
  have h0 := clearOutput_eval 1219 (resetLeafState e)
  have h1 := copyWord_eval 265 1104 1219 d0 (by decide) (by decide) (by decide)
    (by simp [d0, clearOutputState])
  have h2 := copyWord_eval 267 1105 1219 d1 (by decide) (by decide) (by decide)
    (by simp [d1, d0, copiedWord, clearOutputState, StackRoutines.copyStacks])
  have h3 := copyWord_eval 264 1106 1219 d2 (by decide) (by decide) (by decide)
    (by simp [d2, d1, d0, copiedWord, clearOutputState, StackRoutines.copyStacks])
  have hb0 := clearOutput_bound 1219 (resetLeafState e) B hb
  have hb1 := copyWord_bound 265 1104 d0 B hb0 (by simp [d0, clearOutputState, resetLeafState, resetRegisterState, h1104])
  have hb2 := copyWord_bound 267 1105 d1 B hb1
    (by simp [d1, d0, copiedWord, clearOutputState, StackRoutines.copyStacks, resetLeafState, resetRegisterState, h1105])
  have hb3 := copyWord_bound 264 1106 d2 B hb2
    (by simp [d2, d1, d0, copiedWord, clearOutputState, StackRoutines.copyStacks, resetLeafState, resetRegisterState, h1106])
  refine ⟨t + (40 + (2 * (e.stacks 1219).length + 3 +
    (7 * (d0.stacks 265).length + 5 + (7 * (d1.stacks 267).length + 5 +
      (7 * (d2.stacks 264).length + 5))))), d3, ?_,
      he.seq (hreset.seq (h0.seq (h1.seq (h2.seq h3)))),
      ?_, ?_, ?_, ?_, ?_, ?_, hb3, ?_⟩
  · have := hb 1219
    have h265 : (d0.stacks 265).length ≤ B := hb0 265
    have h267 : (d1.stacks 267).length ≤ B := hb1 267
    have h264 : (d2.stacks 264).length ≤ B := hb2 264
    omega
  · simp [d3, d2, d1, d0, copiedWord, clearOutputState, StackRoutines.copyStacks,
      resetLeafState, resetRegisterState, h1104, hfr 265 (by decide)]
  · simp [d3, d2, d1, d0, copiedWord, clearOutputState, StackRoutines.copyStacks,
      resetLeafState, resetRegisterState, h1105, hfr 267 (by decide)]
  · simp [d3, d2, d1, d0, copiedWord, clearOutputState, StackRoutines.copyStacks,
      resetLeafState, resetRegisterState, h1106, hfr 264 (by decide)]
  · simp [d3, d2, d1, d0, copiedWord, clearOutputState, StackRoutines.copyStacks]
  · intro j h4 h5 h6
    have hj : ABI.leafStacks j ≠ 1219 := by
      intro h; have hv := congrArg Fin.val h
      change 320 + j.val = 1219 at hv
      omega
    simp [d3, d2, d1, d0, copiedWord, clearOutputState, StackRoutines.copyStacks,
      resetLeafState, resetRegisterState, h4, h5, h6, hj, hempty j]
  · intro i hi hs
    have h4 : i ≠ 1104 := by intro h; subst i; exact hi ⟨784, rfl⟩
    have h5 : i ≠ 1105 := by intro h; subst i; exact hi ⟨785, rfl⟩
    have h6 : i ≠ 1106 := by intro h; subst i; exact hi ⟨786, rfl⟩
    simpa [d3, d2, d1, d0, copiedWord, clearOutputState, StackRoutines.copyStacks,
      resetLeafState, resetRegisterState, h4, h5, h6, hs] using hframe i hi
  · intro j
    have h72 : ABI.leafRegisters j ≠ 72 := by
      intro h; have hv := congrArg Fin.val h
      change 32 + j.val = 72 at hv
      omega
    have h73 : ABI.leafRegisters j ≠ 73 := by
      intro h; have hv := congrArg Fin.val h
      change 32 + j.val = 73 at hv
      omega
    simp [d3, d2, d1, d0, copiedWord, clearOutputState, readRegs,
      resetLeafState, resetRegisterState, leafRegisterPorts, h72, h73]

theorem exportLeaf_eval (a : State 80 1220) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∃ steps b, steps ≤ 1803 * B + 2699 ∧ Eval exportLeaf steps a b ∧
      b.stacks 263 = a.stacks 1108 ∧ b.stacks 1219 = [] ∧
      (∀ j : Fin 896, b.stacks (ABI.leafStacks j) = []) ∧
      (∀ i, (¬ ∃ j, ABI.leafStacks j = i) → i ≠ 263 → i ≠ 1219 →
        b.stacks i = a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ B) := by
  let d0 := clearOutputState 263 a
  let d1 := clearOutputState 1219 d0
  let d2 := copiedWord 1108 263 d1
  have h0 := clearOutput_eval 263 a
  have h1 := clearOutput_eval 1219 d0
  have h2 := copyWord_eval 1108 263 1219 d1 (by decide) (by decide) (by decide)
    (by simp [d1, clearOutputState])
  have hb0 := clearOutput_bound 263 a B ha
  have hb1 := clearOutput_bound 1219 d0 B hb0
  have hb2 := copyWord_bound 1108 263 d1 B hb1
    (by simp [d1, d0, clearOutputState])
  obtain ⟨t, b, ht, he, hempty, hframe, hb⟩ := clearLeaf_eval d2 B hb2
  have h263 : ¬ ∃ j, ABI.leafStacks j = 263 := by
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change 320 + j.val = 263 at hv
    omega
  have h1219 : ¬ ∃ j, ABI.leafStacks j = 1219 := by
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change 320 + j.val = 1219 at hv
    omega
  refine ⟨2 * (a.stacks 263).length + 3 +
    (2 * (d0.stacks 1219).length + 3 + (7 * (d1.stacks 1108).length + 5 + t)),
    b, ?_, h0.seq (h1.seq (h2.seq he)), ?_, ?_, hempty, ?_, hb⟩
  · have := ha 263
    have hscratch : (d0.stacks 1219).length ≤ B := hb0 1219
    have hcount : (d1.stacks 1108).length ≤ B := hb1 1108
    omega
  · rw [hframe 263 h263]
    simp [d2, d1, d0, copiedWord, clearOutputState, StackRoutines.copyStacks]
  · rw [hframe 1219 h1219]
    simp [d2, d1, copiedWord, clearOutputState, StackRoutines.copyStacks]
  · intro i hi hc hs
    rw [hframe i hi]
    simp [d2, d1, d0, copiedWord, clearOutputState, StackRoutines.copyStacks, hc, hs]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
