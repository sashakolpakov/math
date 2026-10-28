import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.CounterForPrograms
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.SubexpEnumerationPayload
import OAI.Algorithms.SubexponentialSAT.SubexpModulusConstruction

namespace OAI.Algorithms

/-!
# Canonical scalar alphabet by an actual binary countdown

At each positive counter value the program copies and decrements the copy,
then prepends its fixed-width word as a record. The controller decrements the
original counter afterward. Thus descending visits produce ascending records.
-/

namespace SubexponentialSAT.SubexpAlphabetProgram

open BitProgram StructuredCalls CounterPrograms Subexp.TupleProgram

def loopPorts : CounterForPrograms.Ports 6 6 where
  register := ⟨![0, 1, 2], by decide⟩
  counter := 0
  scratch := 1
  counter_ne_scratch := by decide

def decPorts : CounterForPrograms.Ports 6 6 where
  register := ⟨![3, 4, 5], by decide⟩
  counter := 2
  scratch := 3
  counter_ne_scratch := by decide

def emitPorts : RecordPrograms.Ports 6 6 :=
  ⟨3, 4, 5, 4, 5, by decide, by decide, by decide, by decide⟩

def clean (a : State 6 6) : Prop :=
  a.stacks 2 = [] ∧ a.stacks 3 = [] ∧ a.stacks 4 = []

def copied (a : State 6 6) : State 6 6 :=
  ⟨readRegs a.regs 3 4 none, StackRoutines.copyStacks 0 2 a.stacks⟩

def transferred (a : State 6 6) : State 6 6 :=
  ⟨readRegs a.regs 3 4 none, StackRoutines.transferStacks 2 4 a.stacks⟩

def emitted (a : State 6 6) : State 6 6 :=
  pushedState 5 3 true (escapedState emitPorts (pushedState 5 3 false a))

abbrev emit : Cmd 6 6 :=
  .seq (pushConst 5 3 false) (.seq (escape emitPorts) (pushConst 5 3 true))

theorem emit_eval (a : State 6 6) :
    Eval emit (5 * (a.stacks 4).length + 7) a (emitted a) := by
  have h := (pushConst_eval 5 3 false a).seq
    ((escape_eval_state emitPorts (pushedState 5 3 false a)).seq
      (pushConst_eval 5 3 true (escapedState emitPorts (pushedState 5 3 false a))))
  convert h using 1 <;> simp [ emitted, emitPorts, pushedState] ; omega

theorem decrement_other (a : State 6 6) (i : Fin 6) (h2 : i ≠ 2) (h3 : i ≠ 3) :
    (CounterForPrograms.decrementResult decPorts a).stacks i = a.stacks i :=
  CounterForPrograms.install_other_stack decPorts a _ _ _ _ _ i h2 h3

abbrev body : Cmd 6 6 :=
  .seq (.call (StackRoutines.copyProgram 0 2 3 3 4))
    (.seq (CounterForPrograms.decrementCmd decPorts)
      (.seq (.call (StackRoutines.transferProgram 2 4 3 4)) emit))

/-- Every body call is a concrete copy, decrement, reverse, and record emit. -/
theorem body_eval (a : State 6 6) (hc : clean a) (hp : 0 < value (a.stacks 0)) :
    ∃ n b, n ≤ 30 * (a.stacks 0).length + 30 ∧ Eval body n a b ∧
      b.stacks 0 = a.stacks 0 ∧ b.stacks 1 = a.stacks 1 ∧ clean b ∧
      b.stacks 5 = prependRecord (ripple false (a.stacks 0)) (a.stacks 5) := by
  let b := copied a
  let c := CounterForPrograms.decrementResult decPorts b
  let d := transferred c
  let e := emitted d
  have h1 := copy_eval 0 2 3 3 4 (by decide) (by decide) (by decide) (by decide) a hc.2.1
  have hb2 : b.stacks 2 = a.stacks 0 := by
    simp [b, copied, StackRoutines.copyStacks, hc.1]
  have hb3 : b.stacks 3 = [] := by
    simpa [b, copied, StackRoutines.copyStacks] using hc.2.1
  have h2 := CounterForPrograms.decrement_eval decPorts b hb3
  have hc2 : c.stacks 2 = ripple false (a.stacks 0) := by
    simpa [c, decPorts, hb2] using CounterForPrograms.decrementResult_counter decPorts b
  have hc3 : c.stacks 3 = [] := CounterForPrograms.decrementResult_scratch decPorts b
  have hc4 : c.stacks 4 = [] := by
    rw [decrement_other b 4 (by decide) (by decide)]
    simpa [b, copied, StackRoutines.copyStacks] using hc.2.2
  have h3 := transfer_eval 2 4 3 4 (by decide) (by decide) c
  have hd4 : d.stacks 4 = (ripple false (a.stacks 0)).reverse := by
    simp [d, transferred, StackRoutines.transferStacks, hc2, hc4]
  have h4 := emit_eval d
  refine ⟨(7 * (a.stacks 0).length + 5) +
    ((rippleCost false (b.stacks 2) + 1) +
      ((3 * (c.stacks 2).length + 3) + (5 * (d.stacks 4).length + 7))),
    e, ?_, h1.seq (h2.seq (h3.seq h4)), ?_, ?_, ?_, ?_⟩
  · have hcost := rippleCost_le false (a.stacks 0)
    rw [hb2, hc2, hd4, List.length_reverse, decrement_length hp]
    omega
  · simp only [e, emitted, pushedState, emitPorts,
      Function.update_of_ne (by decide : (0 : Fin 6) ≠ 5),
      Function.update_of_ne (by decide : (0 : Fin 6) ≠ 4)]
    change (transferred c).stacks 0 = _
    simp only [transferred, StackRoutines.transferStacks,
      Function.update_of_ne (by decide : (0 : Fin 6) ≠ 4),
      Function.update_of_ne (by decide : (0 : Fin 6) ≠ 2)]
    rw [decrement_other b 0 (by decide) (by decide)]
    simp [b, copied, StackRoutines.copyStacks]
  · simp only [e, emitted, pushedState, emitPorts,
      Function.update_of_ne (by decide : (1 : Fin 6) ≠ 5),
      Function.update_of_ne (by decide : (1 : Fin 6) ≠ 4)]
    change (transferred c).stacks 1 = _
    simp only [transferred, StackRoutines.transferStacks,
      Function.update_of_ne (by decide : (1 : Fin 6) ≠ 4),
      Function.update_of_ne (by decide : (1 : Fin 6) ≠ 2)]
    rw [decrement_other b 1 (by decide) (by decide)]
    simp [b, copied, StackRoutines.copyStacks]
  · simp [clean, e, emitted, pushedState, emitPorts, d, transferred,
      StackRoutines.transferStacks, hc3]
  · have hc5 : c.stacks 5 = a.stacks 5 := by
      rw [decrement_other b 5 (by decide) (by decide)]
      simp [b, copied, StackRoutines.copyStacks]
    simp [e, emitted, pushedState, emitPorts, d, transferred,
      StackRoutines.transferStacks, hc2, hc4, hc5, prependRecord,
      frame_eq_escaped, List.append_assoc]

theorem canonical_word (word : List Bool) :
    word = SubexpLiftRing.fixedBits word.length (value word) := by
  apply SubexpModulusConstruction.bits_eq_of_length_of_value
  · exact (SubexpLiftRing.fixedBits_length _ _).symm
  · rw [SubexpLiftRing.toNat_fixedBits_of_lt]
    · exact (value_eq_toNat word).symm
    · simpa only [value_eq_toNat] using ModularArithmetic.toNat_lt_pow_length word

theorem canonical_of_width_value (word : List Bool) (width n : ℕ)
    (hw : word.length = width) (hv : value word = n) :
    word = SubexpLiftRing.fixedBits width n := by
  simpa only [hw, hv] using canonical_word word

theorem clean_next (a : State 6 6) (h : clean a) :
    clean (CounterForPrograms.nextState loopPorts a) := by
  have h2 := CounterForPrograms.nextState_outside loopPorts a 2 (by decide) (by decide)
  have h3 := CounterForPrograms.nextState_outside loopPorts a 3 (by decide) (by decide)
  have h4 := CounterForPrograms.nextState_outside loopPorts a 4 (by decide) (by decide)
  exact ⟨h2.symm.trans h.1, h3.symm.trans h.2.1, h4.symm.trans h.2.2⟩

/-- The actual countdown visits each lower integer exactly once. Prepending
the emitted records gives ascending order, including the zero word. -/
theorem loop_eval (fuel : ℕ) : ∀ (a : State 6 6), value (a.stacks 0) = fuel →
    a.stacks 1 = [] → clean a → a.regs 2 = !(isZero (a.stacks 0)) →
    ∃ n e, n ≤ fuel * (60 * (a.stacks 0).length + 60) + 1 ∧
      Eval (CounterForPrograms.loopCmd loopPorts body) n a e ∧ clean e ∧
      e.stacks 1 = [] ∧ value (e.stacks 0) = 0 ∧ (e.stacks 0).length = (a.stacks 0).length ∧
      e.stacks 5 = appendEncoded
        ((List.range fuel).map (SubexpLiftRing.fixedBits (a.stacks 0).length)) (a.stacks 5) := by
  induction fuel with
  | zero =>
      intro a hv hs hc hf
      have hz := (isZero_eq_true_iff (a.stacks 0)).mpr hv
      have hflag : a.regs (loopPorts.register 2) = false := by simpa [loopPorts, hz] using hf
      exact ⟨1, a, by simp, Eval.while_false hflag, hc, hs, hv, rfl, rfl⟩
  | succ fuel ih =>
      intro a hv hs hc hf
      have hp : 0 < value (a.stacks 0) := by omega
      have hz := (isZero_eq_false_iff (a.stacks 0)).mpr hp
      have hflag : a.regs (loopPorts.register 2) = true := by simpa [loopPorts, hz] using hf
      obtain ⟨nb, b, hnb, hbody, hb0, hb1, hbc, hbout⟩ := body_eval a hc hp
      have hbs : b.stacks 1 = [] := hb1.trans hs
      let c := CounterForPrograms.nextState loopPorts b
      have hcv : value (c.stacks 0) = fuel := by
        change value ((CounterForPrograms.nextState loopPorts b).stacks loopPorts.counter) = fuel
        rw [CounterForPrograms.nextState_counter]
        change value (ripple false (b.stacks 0)) = fuel
        rw [hb0]
        have hd := value_decrement hp
        omega
      have hcw : (c.stacks 0).length = (a.stacks 0).length := by
        change ((CounterForPrograms.nextState loopPorts b).stacks loopPorts.counter).length = _
        rw [CounterForPrograms.nextState_counter]
        change (ripple false (b.stacks 0)).length = _
        rw [hb0, decrement_length hp]
      have hcs : c.stacks 1 = [] := CounterForPrograms.nextState_scratch loopPorts b
      have hcc : clean c := clean_next b hbc
      have hcf : c.regs 2 = !(isZero (c.stacks 0)) :=
        CounterForPrograms.nextState_flag loopPorts b
      obtain ⟨nt, e, hnt, htail, hec, hes, hev, hew, heout⟩ := ih c hcv hcs hcc hcf
      have hbpos : 0 < value (b.stacks 0) := by simpa only [hb0] using hp
      have hadv := CounterForPrograms.advanceCost_le loopPorts b hbpos
      change CounterForPrograms.advanceCost loopPorts b + 1 ≤
        16 * (b.stacks 0).length + 16 at hadv
      rw [hb0] at hadv
      rw [hcw] at hnt hew heout
      refine ⟨nb + CounterForPrograms.advanceCost loopPorts b + nt + 1, e, ?_, ?_,
        hec, hes, hev, hew, ?_⟩
      · nlinarith
      · exact Eval.while_true hflag
          (hbody.seq (CounterForPrograms.advance_eval loopPorts b hbs)) htail
      · have hc5 := CounterForPrograms.nextState_outside loopPorts b 5 (by decide) (by decide)
        change b.stacks 5 = c.stacks 5 at hc5
        rw [heout, ← hc5, hbout]
        have hword : ripple false (a.stacks 0) =
            SubexpLiftRing.fixedBits (a.stacks 0).length fuel := by
          apply canonical_of_width_value _ _ _ (decrement_length hp)
          have hd := value_decrement hp
          omega
        rw [hword, List.range_succ, List.map_append]
        simp [appendEncoded, List.foldr_append]

def alphabetWords (word : List Bool) : List (List Bool) :=
  (List.range (value word)).map (SubexpLiftRing.fixedBits word.length)

def inputState (word : List Bool) (regs : Fin 6 → Bool := fun _ => false) : State 6 6 :=
  ⟨regs, fun i => if i = 0 then word else []⟩

abbrev cmd : Cmd 6 6 :=
  .seq (pushConst 5 3 false) (CounterForPrograms.forCmd loopPorts body)

def program := StructuredCalls.compiled cmd 0 5

/-- Starting with only a binary counter word, emit the complete ascending
fixed-width alphabet below its value. -/
theorem program_runsIn_clean (word : List Bool) (regs : Fin 6 → Bool) :
    ∃ next : State 6 6,
      next.stacks 5 = ProgramEncoding.encodeRecords (alphabetWords word) ∧
      clean next ∧ next.stacks 1 = [] ∧ value (next.stacks 0) = 0 ∧
      (next.stacks 0).length = word.length ∧
      RunsIn program ((value word + 1) * (60 * word.length + 60))
        ((inputState word regs).withPC (some program.entry)) (next.withPC none) := by
  let a := inputState word regs
  let b := pushedState 5 3 false a
  let c := CounterForPrograms.testResult loopPorts b
  have hb0 : b.stacks 0 = word := by simp [b, a, inputState]
  have hbs : b.stacks 1 = [] := by simp [b, a, inputState]
  have hcstack : c.stacks = b.stacks := CounterForPrograms.testResult_stacks loopPorts b hbs
  have hc0 : c.stacks 0 = word := by rw [hcstack, hb0]
  have hcs : c.stacks 1 = [] := by rw [hcstack, hbs]
  have hcc : clean c := by simp [clean, hcstack, b, a, inputState]
  have hcf : c.regs 2 = !(isZero (c.stacks 0)) := by
    rw [hcstack]
    exact CounterForPrograms.testResult_flag loopPorts b
  obtain ⟨n, next, hn, he, hec, hes, hev, hew, hout⟩ :=
    loop_eval (value word) c (by rw [hc0]) hcs hcc hcf
  have hpush := pushConst_eval 5 3 false a
  have htest := CounterForPrograms.test_eval loopPorts b hbs
  have hrun := hpush.seq (htest.seq he)
  have hc5 : c.stacks 5 = ProgramEncoding.encodeRecords [] := by
    simp [hcstack, b, a, inputState, ProgramEncoding.encodeRecords,
      Encoding.encodeList]
  rw [hc0, hc5, appendEncoded_encodeRecords, List.append_nil] at hout
  refine ⟨next, hout, hec, hes, hev, ?_,
    2 + ((8 * (b.stacks loopPorts.counter).length + 7) + n) + 1, ?_, ?_⟩
  · simpa only [hc0] using hew
  · change 2 + ((8 * (b.stacks 0).length + 7) + n) + 1 ≤ _
    rw [hb0]
    rw [hc0] at hn
    nlinarith
  · exact StructuredCalls.compiled_halt_trace hrun 0 5

theorem program_runsIn (word : List Bool) :
    ∃ next : State 6 6,
      next.stacks 5 = ProgramEncoding.encodeRecords (alphabetWords word) ∧
      RunsIn program ((value word + 1) * (60 * word.length + 60))
        (initial program word) (next.withPC none) := by
  obtain ⟨next, hout, _, _, _, _, hr⟩ := program_runsIn_clean word (fun _ => false)
  exact ⟨next, hout, hr⟩

theorem primitive_runsIn (word : List Bool) :
    ∃ next : State 6 6,
      next.stacks 5 = ProgramEncoding.encodeRecords (alphabetWords word) ∧
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * ((value word + 1) * (60 * word.length + 60)))
        (primitiveCfg program (initial program word)) (primitiveCfg program (next.withPC none)) := by
  obtain ⟨next, hout, hr⟩ := program_runsIn word
  exact ⟨next, hout, primitive_execution program hr⟩

theorem scalarAlphabet_eq_range (p : ℕ) [Fact p.Prime] :
    (QuarticSearch.elements p).map (SubexpEnumerationPayload.scalarCode p).block =
      (List.range p).map (SubexpLiftRing.fixedBits (SubexpEnumerationPayload.scalarWidth p)) := by
  apply List.ext_getElem
  · simp [QuarticSearch.elements]
  · intro i hi hj
    have hip : i < p := by simpa [QuarticSearch.elements] using hi
    simp [QuarticSearch.elements, SubexpEnumerationPayload.scalarCode,
      SubexpEnumerationPayload.scalarBits, ZMod.val_natCast, Nat.mod_eq_of_lt hip]

def primeWord (p : ℕ) : List Bool :=
  SubexpLiftRing.fixedBits (SubexpEnumerationPayload.scalarWidth p) p

@[simp] theorem primeWord_value (p : ℕ) : value (primeWord p) = p := by
  rw [value_eq_toNat, primeWord, SubexpLiftRing.toNat_fixedBits_of_lt]
  exact Nat.lt_pow_succ_log_self Nat.one_lt_two p

@[simp] theorem primeWord_length (p : ℕ) :
    (primeWord p).length = SubexpEnumerationPayload.scalarWidth p :=
  SubexpLiftRing.fixedBits_length _ _

theorem alphabetWords_primeWord (p : ℕ) [Fact p.Prime] :
    alphabetWords (primeWord p) =
      (QuarticSearch.elements p).map (SubexpEnumerationPayload.scalarCode p).block := by
  rw [alphabetWords, primeWord_value, primeWord_length, scalarAlphabet_eq_range]

/-- The canonical prime-field alphabet is an actual program output, in
exactly the same order as the vector and node specifications. -/
theorem selected_program_runsIn (p : ℕ) [Fact p.Prime] :
    ∃ next : State 6 6,
      next.stacks 5 = ProgramEncoding.encodeRecords
        ((QuarticSearch.elements p).map (SubexpEnumerationPayload.scalarCode p).block) ∧
      RunsIn program ((p + 1) * (60 * SubexpEnumerationPayload.scalarWidth p + 60))
        (initial program (primeWord p)) (next.withPC none) := by
  simpa only [alphabetWords_primeWord, primeWord_value, primeWord_length] using
    program_runsIn (primeWord p)

end SubexponentialSAT.SubexpAlphabetProgram

end OAI.Algorithms
