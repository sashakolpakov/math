import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCorrect
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeSpace
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizationCorrectness

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls

def normalizationRegisters : Fin 15 ↪ Fin 80 := Fin.castAddEmb 65

def normalizationStacks : Fin 16 ↪ Fin 1220 where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 1218, 14, 15]
  inj' := by decide

def normalizationCommand : Cmd 80 1220 :=
  .call (ProgramLinking.liftProgram SubexpNormalizationProgram.program
    normalizationRegisters normalizationStacks)

def unaryRegisters : Fin 2 ↪ Fin 80 := (Fin.castAddEmb 1).trans ABI.positivityRegisters

def unaryStacks : Fin 2 ↪ Fin 1220 where
  toFun := ![1218, 258]
  inj' := by decide

def seedUnary : Cmd 80 1220 :=
  .base (.seq (.atom (.set 72 false)) (.atom (.push 258 72)))

def seededUnary (a : State 80 1220) : State 80 1220 :=
  ⟨Function.update a.regs 72 false, Function.update a.stacks 258 (false :: a.stacks 258)⟩

def ambientCommand : Cmd 80 1220 :=
  .seq (copyWord ABI.countStack 1218 1219)
    (.seq seedUnary (.seq (.call (ProgramLinking.liftProgram ParserProgram.natProgram
      unaryRegisters unaryStacks)) (clearOutput 1218)))

noncomputable def parsedAmbient (a : State 80 1220) (n : ℕ) (body : List Bool) :
    State 80 1220 :=
  embedState unaryRegisters unaryStacks (seededUnary (copiedWord ABI.countStack 1218 a))
    (StructuredProgram.State.ofCfg
      (ParserProgram.cfg (l := 5) none false true body (Encoding.encodeNat n)))

noncomputable def ambientResult (a : State 80 1220) (n : ℕ) (body : List Bool) :
    State 80 1220 := clearOutputState 1218 (parsedAmbient a n body)

theorem seedUnary_eval (a : State 80 1220) : Eval seedUnary 2 a (seededUnary a) := by
  apply Eval.base
  simpa [seedUnary, seededUnary, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.withPC,
    StructuredProgram.State.ofCfg, execInstr] using
    (StructuredProgram.Eval.atom (.set (72 : Fin 80) false) a).seq
      (StructuredProgram.Eval.atom (.push (258 : Fin 1220) (72 : Fin 80)) _)

theorem ambient_eval (a : State 80 1220) (n : ℕ) (body : List Bool)
    (hc : a.stacks ABI.countStack = Encoding.encodeNat n ++ body)
    (hu : a.stacks 258 = []) (hw : a.stacks 1218 = []) (hs : a.stacks 1219 = []) :
    Eval ambientCommand (7 * (a.stacks ABI.countStack).length + 4 * n + 2 * body.length + 14)
      a (ambientResult a n body) := by
  let ready := seededUnary (copiedWord ABI.countStack 1218 a)
  have hc' : a.stacks 256 = Encoding.encodeNat n ++ body := hc
  have hprojection : (projectState unaryRegisters unaryStacks ready).withPC
      (some ParserProgram.natProgram.entry) =
      ParserProgram.cfg (some 0) (ready.regs (unaryRegisters 0))
        (ready.regs (unaryRegisters 1)) (Encoding.encodeNat n ++ body) [false] := by
    apply congrArg₂ (Cfg.mk (some 0))
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;>
        simp [projectState, unaryStacks, ready, seededUnary, copiedWord,
          StackRoutines.copyStacks, ParserProgram.pair, hc', hu, hw, ABI.countStack]
  have hparse := eval_call_from_state ParserProgram.natProgram unaryRegisters unaryStacks
    ready unaryRegisters.injective unaryStacks.injective
    (n := 4 * n + 4) (b := StructuredProgram.State.ofCfg
      (ParserProgram.cfg (l := 5) none false true body (Encoding.encodeNat n)))
    (by
      rw [hprojection]
      simpa [Encoding.encodeNat, StructuredProgram.State.ofCfg,
        StructuredProgram.State.withPC, ParserProgram.cfg] using
        (ParserProgram.nat_trace n body [false] (ready.regs (unaryRegisters 0))
          (ready.regs (unaryRegisters 1))))
  have hbody : (parsedAmbient a n body).stacks 1218 = body :=
    embedState_stack unaryRegisters unaryStacks ready _ unaryStacks.injective 0
  convert (copyWord_eval ABI.countStack 1218 1219 a (by decide) (by decide)
    (by decide) hs).seq ((seedUnary_eval _).seq (hparse.seq
      (clearOutput_eval 1218 (parsedAmbient a n body)))) using 1
  · rfl
  · rw [hbody]
    omega
  · rfl

theorem ambientResult_stacks (a : State 80 1220) (n : ℕ) (body : List Bool)
    (hw : a.stacks 1218 = []) :
    (ambientResult a n body).stacks = Function.update a.stacks 258 (Encoding.encodeNat n) := by
  funext i
  by_cases hi : i = 1218
  · subst i; simp [ambientResult, clearOutputState, hw]
  by_cases hu : i = 258
  · subst i
    change (parsedAmbient a n body).stacks 258 = Encoding.encodeNat n
    exact embedState_stack _ unaryStacks _ _ unaryStacks.injective 1
  have hoff : ¬ ∃ j, unaryStacks j = i := by
    rintro ⟨j, hj⟩
    fin_cases j <;> simp [unaryStacks] at hj <;> omega
  simp only [ambientResult, clearOutputState, Function.update_of_ne hi]
  rw [parsedAmbient, embedState_stack_frame _ _ _ _ i hoff]
  simp [seededUnary, copiedWord, StackRoutines.copyStacks, hi, hu]

def placeBodyCommand : Cmd 80 1220 :=
  .seq (copyWord 1218 265 1219) (clearOutput 1218)

def placedBody (a : State 80 1220) : State 80 1220 :=
  clearOutputState 1218 (copiedWord 1218 265 a)

theorem placeBody_eval (a : State 80 1220) (hs : a.stacks 1219 = []) :
    Eval placeBodyCommand (9 * (a.stacks 1218).length + 8) a (placedBody a) := by
  convert (copyWord_eval 1218 265 1219 a (by decide) (by decide) (by decide) hs).seq
    (clearOutput_eval 1218 (copiedWord 1218 265 a)) using 1
  · rfl
  · simp [copiedWord, StackRoutines.copyStacks]
    omega
  · rfl

theorem placedBody_stacks (a : State 80 1220) :
    (placedBody a).stacks =
      Function.update (Function.update a.stacks 265 (a.stacks 1218 ++ a.stacks 265)) 1218 [] := rfl


theorem normalization_after_header {n : ℕ} (F : SAT.CNF (Fin n)) (binary : List Bool) :
    ∃ steps b, steps ≤ 3300 * ((Encoding.encodeCNFBody F).length + 1) ^ 2 ∧
      Eval normalizationCommand steps
        (headerResult (Encoding.encodeCNF F) (Encoding.encodeCNFBody F) binary) b ∧
      b.stacks 1218 = SubexpNormalizationCorrectness.normalizedBody F ∧
      (∀ i : Fin 16, i ≠ 13 → b.stacks (normalizationStacks i) = []) ∧
      (∀ i, (¬ ∃ j, normalizationStacks j = i) → b.stacks i =
        (headerResult (Encoding.encodeCNF F) (Encoding.encodeCNFBody F) binary).stacks i) := by
  let a := headerResult (Encoding.encodeCNF F) (Encoding.encodeCNFBody F) binary
  let localData := projectState normalizationRegisters normalizationStacks a
  have hsource : localData.stacks 13 = Encoding.encodeCNFBody F :=
    headerResult_body _ _ _
  have hready : SubexpNormalizationProgram.Ready localData := by
    intro i hi
    fin_cases i <;> first | contradiction |
      exact headerResult_other _ _ _ _ (by decide) (by decide) (by decide)
  obtain ⟨b, hb, hout, steps, hs, ht⟩ :=
    SubexpNormalizationCorrectness.canonical_body_runsIn F localData hsource hready
  refine ⟨steps, embedState normalizationRegisters normalizationStacks a b, hs,
    eval_call_from_state _ _ _ a normalizationRegisters.injective normalizationStacks.injective ht,
    ?_, ?_, ?_⟩
  · exact (embedState_stack _ _ _ _ normalizationStacks.injective 13).trans hout
  · intro i hi
    exact (embedState_stack _ _ _ _ normalizationStacks.injective i).trans (hb i hi)
  · intro i hi
    exact embedState_stack_frame _ _ _ _ i hi

theorem normalization_after_header_frame {n : ℕ} (F : SAT.CNF (Fin n)) (binary : List Bool) :
    ∃ steps b, steps ≤ 3300 * ((Encoding.encodeCNFBody F).length + 1) ^ 2 ∧
      Eval normalizationCommand steps
        (headerResult (Encoding.encodeCNF F) (Encoding.encodeCNFBody F) binary) b ∧
      b.stacks 1218 = SubexpNormalizationCorrectness.normalizedBody F ∧
      b.stacks ABI.countStack = Encoding.encodeCNF F ∧ b.stacks 267 = binary ∧
      (∀ i, i ≠ ABI.countStack → i ≠ 267 → i ≠ 1218 → b.stacks i = []) := by
  obtain ⟨steps, b, hs, he, ho, hr, hf⟩ := normalization_after_header F binary
  have hframe (i : Fin 1220) (hi : ¬ ∃ j, normalizationStacks j = i) :
      b.stacks i = (headerResult (Encoding.encodeCNF F) (Encoding.encodeCNFBody F) binary).stacks i :=
    hf i hi
  refine ⟨steps, b, hs, he, ho, ?_, ?_, ?_⟩
  · rw [hframe _ (by rintro ⟨j, hj⟩; fin_cases j <;> simp [normalizationStacks, ABI.countStack] at hj)]
    exact headerResult_input _ _ _
  · rw [hframe _ (by rintro ⟨j, hj⟩; fin_cases j <;> simp [normalizationStacks] at hj)]
    exact headerResult_binary _ _ _
  · intro i hc hn hb
    by_cases hi : ∃ j, normalizationStacks j = i
    · obtain ⟨j, rfl⟩ := hi
      apply hr j
      intro hj
      subst j
      exact hb rfl
    · rw [hframe i hi]
      exact headerResult_other _ _ _ i hc hn hb

def frontendCommand : Cmd 80 1220 :=
  .seq headerCommand (.seq normalizationCommand (.seq placeBodyCommand ambientCommand))

def frontendProgram := compiled frontendCommand ABI.countStack ABI.answerStack

structure FrontendReady {n : ℕ} (F : SAT.CNF (Fin n)) (binary : List Bool)
    (a : State 80 1220) : Prop where
  input : a.stacks ABI.countStack = Encoding.encodeCNF F
  header : a.stacks 258 = Encoding.encodeNat n
  body : a.stacks 265 = SubexpNormalizationCorrectness.normalizedBody F
  dimension : a.stacks 267 = binary
  blank : ∀ i, i ≠ ABI.countStack → i ≠ 258 → i ≠ 265 → i ≠ 267 → a.stacks i = []

def frontendBound {n : ℕ} (F : SAT.CNF (Fin n)) : ℕ :=
  14 * Encoding.formulaBitLength F + 4 * n + 11 * (Encoding.encodeCNFBody F).length + 27 +
    FrontendProgram.initializeBound n + 3300 * ((Encoding.encodeCNFBody F).length + 1) ^ 2

theorem frontend_eval {n : ℕ} (F : SAT.CNF (Fin n)) :
    ∃ binary steps b, BinaryArithmetic.toNat binary = n ∧ binary.length ≤ n ∧
      steps ≤ frontendBound F ∧ Eval frontendCommand steps
        (StructuredProgram.ioState ABI.countStack (Encoding.encodeCNF F)) b ∧
      FrontendReady F binary b := by
  obtain ⟨binary, headerSteps, hv, hl, hh, he⟩ := header_eval n (Encoding.encodeCNFBody F)
  obtain ⟨normalSteps, a, hn, hnormal, hbody, hinput, hbinary, hblank⟩ :=
    normalization_after_header_frame F binary
  have ha265 : a.stacks 265 = [] := hblank 265 (by decide) (by decide) (by decide)
  have ha1219 : a.stacks 1219 = [] := hblank 1219 (by decide) (by decide) (by decide)
  have hp := placeBody_eval a ha1219
  have hplaced (i : Fin 1220) (hi : i ≠ 265) (hw : i ≠ 1218) :
      (placedBody a).stacks i = a.stacks i := by
    simp [placedBody_stacks, hi, hw]
  have hpc : (placedBody a).stacks ABI.countStack = Encoding.encodeCNF F :=
    (hplaced _ (by decide) (by decide)).trans hinput
  have hpu : (placedBody a).stacks 258 = [] :=
    (hplaced _ (by decide) (by decide)).trans (hblank _ (by decide) (by decide) (by decide))
  have hpw : (placedBody a).stacks 1218 = [] := by simp [placedBody_stacks]
  have hps : (placedBody a).stacks 1219 = [] :=
    (hplaced _ (by decide) (by decide)).trans ha1219
  have ham := ambient_eval (placedBody a) n (Encoding.encodeCNFBody F) hpc hpu hpw hps
  have hfinal := ambientResult_stacks (placedBody a) n (Encoding.encodeCNFBody F) hpw
  refine ⟨binary, headerSteps + (normalSteps + (9 * (a.stacks 1218).length + 8 +
    (7 * ((placedBody a).stacks ABI.countStack).length + 4 * n +
      2 * (Encoding.encodeCNFBody F).length + 14))),
    ambientResult (placedBody a) n (Encoding.encodeCNFBody F), hv, hl, ?_,
    he.seq (hnormal.seq (hp.seq ham)), ?_⟩
  · have hlen := SubexpNormalizationCorrectness.normalizedBody_length_le F
    rw [hbody, hpc]
    change headerSteps + (normalSteps +
      (9 * (SubexpNormalizationCorrectness.normalizedBody F).length + 8 +
        (7 * Encoding.formulaBitLength F + 4 * n +
          2 * (Encoding.encodeCNFBody F).length + 14))) ≤ frontendBound F
    change headerSteps ≤ 7 * Encoding.formulaBitLength F + 5 +
      FrontendProgram.initializeBound n at hh
    dsimp [frontendBound]
    omega
  · constructor
    · rw [hfinal, Function.update_of_ne (by decide : ABI.countStack ≠ 258)]
      exact hpc
    · rw [hfinal, Function.update_self]
    · rw [hfinal, Function.update_of_ne (by decide : (265 : Fin 1220) ≠ 258)]
      simp [placedBody_stacks, ha265, hbody]
    · rw [hfinal, Function.update_of_ne (by decide : (267 : Fin 1220) ≠ 258),
        hplaced _ (by decide) (by decide)]
      exact hbinary
    · intro i hc hu hb hn
      rw [hfinal, Function.update_of_ne hu]
      by_cases hw : i = 1218
      · subst i; exact hpw
      · rw [hplaced i hb hw]
        exact hblank i hc hn hw

theorem frontendBound_polynomial {n : ℕ} (F : SAT.CNF (Fin n)) :
    frontendBound F ≤ 4000 * (Encoding.formulaBitLength F + 1) ^ 2 := by
  have hn := Encoding.numVariables_le_formulaBitLength F
  have hb : (Encoding.encodeCNFBody F).length ≤ Encoding.formulaBitLength F := by
    rw [Encoding.formulaBitLength_eq]
    omega
  have hn2 := Nat.pow_le_pow_left hn 2
  have hb2 := Nat.pow_le_pow_left (Nat.add_le_add_right hb 1) 2
  dsimp [frontendBound, FrontendProgram.initializeBound]
  nlinarith

theorem frontend_trace_space {n : ℕ} (F : SAT.CNF (Fin n)) :
    ∃ binary steps b, BinaryArithmetic.toNat binary = n ∧ binary.length ≤ n ∧
      steps ≤ 4001 * (Encoding.formulaBitLength F + 1) ^ 2 ∧
      Trace frontendProgram steps (initial frontendProgram (Encoding.encodeCNF F))
        (b.withPC none) ∧ FrontendReady F binary b ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace frontendProgram prefixSteps (initial frontendProgram (Encoding.encodeCNF F))
          intermediate → ∀ i, (intermediate.stacks i).length ≤
            Encoding.formulaBitLength F + 4001 * (Encoding.formulaBitLength F + 1) ^ 2 := by
  obtain ⟨binary, steps, b, hv, hl, hs, he, hr⟩ := frontend_eval F
  have htime : steps + 1 ≤ 4001 * (Encoding.formulaBitLength F + 1) ^ 2 := by
    have hpoly := frontendBound_polynomial F
    have hpositive : 1 ≤ (Encoding.formulaBitLength F + 1) ^ 2 := Nat.one_le_pow' 2 _
    omega
  refine ⟨binary, steps + 1, b, hv, hl, htime,
    compiled_halt_trace he ABI.countStack ABI.answerStack, hr, ?_⟩
  intro prefixSteps intermediate hp ht i
  exact StructuredSpace.local_stack_bound frontendProgram
    (steps := 4001 * (Encoding.formulaBitLength F + 1) ^ 2)
    (show dataBits (initial frontendProgram (Encoding.encodeCNF F)) ≤ Encoding.formulaBitLength F
      by simp [Encoding.formulaBitLength]) prefixSteps intermediate (hp.trans htime) ht i


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
