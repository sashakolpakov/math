import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDenseProgram
import OAI.Algorithms.SubexponentialSAT.SubexpCoefficientLookup
import OAI.Algorithms.SubexponentialSAT.SubexpCanonicalWords
import OAI.Algorithms.SubexponentialSAT.SubexpCanonicalDense
import OAI.Algorithms.SubexponentialSAT.SubexpDenseSerialization

namespace OAI.Algorithms

namespace SubexponentialSAT.SubexpDenseProgram.Projection

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- Local stacks 0--19 are the concrete coefficient-lookup ABI. Stacks
20/21 are slot input and output; 22/23 are preserved polynomial inputs;
24 is copy scratch and 25 is the preserved slot master. -/
def lookupPorts : Fin 20 → Fin 26 := Fin.castAdd 6

def lookupRegisters : Fin 8 → Fin 8 := id

def emitPorts : Fin 6 → Fin 26 := ![8, 14, 25, 21, 17, 16]

def emitRegisters : Fin 5 → Fin 8 := Fin.castAdd 3

abbrev copyInput (source : Fin 26) : Cmd 8 26 :=
  .call (StackRoutines.copyProgram source 15 24 0 1)

abbrev lookupCall : Cmd 8 26 :=
  .call (ProgramLinking.liftProgram SubexpCoefficientLookup.lookupProgram
    lookupRegisters lookupPorts)

abbrev scanCall : Cmd 8 26 :=
  .call (ProgramLinking.liftProgram SubexpCoefficientLookup.scanProgram
    lookupRegisters lookupPorts)

abbrev emitCall : Cmd 8 26 :=
  .call (ProgramLinking.liftProgram RawEmitter.emitRawTermProgram emitRegisters emitPorts)

abbrev resetFlags : Cmd 8 26 :=
  .seq (.base (.atom (.set 0 false)))
    (.seq (.base (.atom (.set 1 true))) (.base (.atom (.set 7 false))))

/-- One projected coefficient, using the actual full-list lookup and raw
coefficient writer. The input polynomial is copied before its destructive scan. -/
abbrev slotCallback : Cmd 8 26 :=
  .seq (copyInput 22) (.seq lookupCall (.seq emitCall resetFlags))

/-- Addition projects the concatenation by scanning the two input lists
successively into one accumulator; it need not materialize a concatenation. -/
abbrev additionSlotCallback : Cmd 8 26 :=
  .seq (copyInput 22)
    (.seq lookupCall (.seq (copyInput 23) (.seq scanCall (.seq emitCall resetFlags))))

def slotPorts : RecordPrograms.Ports 8 26 where
  tag := 0
  present := 1
  found := 7
  source := 20
  payload := 14
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

abbrev project : Cmd 8 26 := RecordPrograms.iterate slotPorts slotCallback
abbrev add : Cmd 8 26 := RecordPrograms.iterate slotPorts additionSlotCallback

/-- Fixed finite tables; neither dimensions nor coefficient widths appear in
their construction. The runtime inputs carry every growing parameter. -/
def projectProgram := RecordPrograms.program slotPorts slotCallback
def addProgram := RecordPrograms.program slotPorts additionSlotCallback

theorem lookupPorts_injective : Function.Injective lookupPorts := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun i : Fin 26 => i.val) h
theorem emitPorts_injective : Function.Injective emitPorts := by decide
theorem emitRegisters_injective : Function.Injective emitRegisters := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun i : Fin 8 => i.val) h

def extendState (lower : State 8 20) (upper : Fin 6 → List Bool) : State 8 26 :=
  ⟨lower.regs, Fin.addCases (m := 20) (n := 6) (motive := fun _ => List Bool)
    lower.stacks upper⟩

theorem embed_lookup (lower next : State 8 20) (upper : Fin 6 → List Bool) :
    embedState lookupRegisters lookupPorts (extendState lower upper) next =
      extendState next upper := by
  apply SubexpScanPrimitives.state_ext
  · simp [embedState, lookupRegisters, extendState]
  · funext i
    refine Fin.addCases (m := 20) (n := 6) (fun j => ?_) (fun j => ?_) i
    · simpa only [lookupPorts, extendState, Fin.addCases_left] using
        (embedState_stack lookupRegisters lookupPorts (extendState lower upper) next
          lookupPorts_injective j)
    · rw [embedState_stack_frame]
      · simp only [extendState, Fin.addCases_right]
      · rintro ⟨k, hk⟩
        have hv := congrArg Fin.val hk
        change k.val = 20 + j.val at hv
        omega

def controllerState (regs : Fin 8 → Bool)
    (modulus acc width query raw slots output left right master : List Bool) : State 8 26 :=
  extendState (SubexpCoefficientLookup.state regs modulus acc [] width query raw [])
    ![slots, output, left, right, [], master]

theorem copyLeft_eval (regs : Fin 8 → Bool)
    (modulus acc width query slots output left right master : List Bool) :
    Eval (copyInput 22) (7 * left.length + 5)
      (controllerState regs modulus acc width query [] slots output left right master)
      (controllerState (readRegs regs 0 1 none) modulus acc width query left slots output left right master) := by
  let d := controllerState regs modulus acc width query [] slots output left right master
  have hc := SubexpScanPrimitives.copy_eval d 22 15 24 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  have hsource : d.stacks 22 = left := rfl
  have he : SubexpScanPrimitives.afterCopy d 22 15 0 1 =
      controllerState (readRegs regs 0 1 none) modulus acc width query left slots output left right master := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext i
      fin_cases i <;>
        simp [d, controllerState, extendState, SubexpScanPrimitives.afterCopy,
          StackRoutines.copyStacks, SubexpCoefficientLookup.state, SubexpCoefficientLookup.frame,
          SubexpFlatAdd.ready, SubexpFlatAdd.state, SubexpFlatAdd.stacks,
          Fin.addCases, Fin.coe_ofNat_eq_mod]
  rw [hsource] at hc
  rw [he] at hc
  simpa only [copyInput, d] using hc

theorem copyRight_eval (regs : Fin 8 → Bool)
    (modulus acc width query slots output left right master : List Bool) :
    Eval (copyInput 23) (7 * right.length + 5)
      (controllerState regs modulus acc width query [] slots output left right master)
      (controllerState (readRegs regs 0 1 none) modulus acc width query right slots output left right master) := by
  let d := controllerState regs modulus acc width query [] slots output left right master
  have hc := SubexpScanPrimitives.copy_eval d 23 15 24 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  have hsource : d.stacks 23 = right := rfl
  have he : SubexpScanPrimitives.afterCopy d 23 15 0 1 =
      controllerState (readRegs regs 0 1 none) modulus acc width query right slots output left right master := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext i
      fin_cases i <;>
        simp [d, controllerState, extendState, SubexpScanPrimitives.afterCopy,
          StackRoutines.copyStacks, SubexpCoefficientLookup.state, SubexpCoefficientLookup.frame,
          SubexpFlatAdd.ready, SubexpFlatAdd.state, SubexpFlatAdd.stacks,
          Fin.addCases, Fin.coe_ofNat_eq_mod]
  rw [hsource] at hc
  rw [he] at hc
  simpa only [copyInput, d] using hc

section LookupCalls

open SubexpCoefficientLookup SubexpLiftRing

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

/-- The local controller calls the concrete complete lookup machine and
preserves all six outer-controller stacks. -/
theorem lookupCall_eval (regs : Fin 8 → Bool) (records : List (Record p μ))
    (width query : List Bool) (hwidth : width.length = baseWidth p μ)
    (upper : Fin 6 → List Bool) :
    ∃ n ≤ 14 * baseWidth p μ + 12 +
        RecordPrograms.budget (recordCost (baseWidth p μ) query) (encoded p μ records),
      ∃ regs', Eval lookupCall n
        (extendState (state regs M.bits [] [] width query
          (Encoding.encodeList id (encoded p μ records)) []) upper)
        (extendState (state (normalized regs' false true false) M.bits
          (SubexpFlatAdd.encode (fold p μ M query (zeroCoefficient p μ) records)) []
          width query [] []) upper) := by
  obtain ⟨regs', n, hn, ht⟩ := lookup_runs p μ M regs records width query [] hwidth
  simp only [List.append_nil] at ht
  let a := state regs M.bits [] [] width query (Encoding.encodeList id (encoded p μ records)) []
  let b := state (normalized regs' false true false) M.bits
    (SubexpFlatAdd.encode (fold p μ M query (zeroCoefficient p μ) records)) [] width query [] []
  have hc := eval_call_lifted SubexpCoefficientLookup.lookupProgram lookupRegisters lookupPorts
    (extendState a upper) Function.injective_id lookupPorts_injective
    (a := a) (b := b) ht
  refine ⟨n, hn, regs', ?_⟩
  simpa only [embed_lookup, lookupCall] using hc

theorem scanCall_eval (regs : Fin 8 → Bool) (initial : Coefficient p μ)
    (records : List (Record p μ)) (width query : List Bool)
    (hwidth : width.length = baseWidth p μ) (upper : Fin 6 → List Bool) :
    ∃ n ≤ 4 + RecordPrograms.budget (recordCost (baseWidth p μ) query) (encoded p μ records),
      ∃ regs', Eval scanCall n
        (extendState (state regs M.bits (SubexpFlatAdd.encode initial) [] width query
          (Encoding.encodeList id (encoded p μ records)) []) upper)
        (extendState (state (normalized regs' false true false) M.bits
          (SubexpFlatAdd.encode (fold p μ M query initial records)) [] width query [] []) upper) := by
  obtain ⟨regs', n, hn, ht⟩ := scan_runs p μ M regs initial records width query [] hwidth
  simp only [List.append_nil] at ht
  let a := state regs M.bits (SubexpFlatAdd.encode initial) [] width query
    (Encoding.encodeList id (encoded p μ records)) []
  let b := state (normalized regs' false true false) M.bits
    (SubexpFlatAdd.encode (fold p μ M query initial records)) [] width query [] []
  have hc := eval_call_lifted SubexpCoefficientLookup.scanProgram lookupRegisters lookupPorts
    (extendState a upper) Function.injective_id lookupPorts_injective
    (a := a) (b := b) ht
  refine ⟨n, hn, regs', ?_⟩
  simpa only [embed_lookup, scanCall] using hc

end LookupCalls

theorem emitCall_eval (frame : State 8 26) (key coefficient spare output : List Bool)
    (regs : Fin 5 → Bool) :
    Eval emitCall (37 * coefficient.length + 21 * key.length + 57)
      (embedState emitRegisters emitPorts frame
        (SubexpRecordScan.recordState regs coefficient key.reverse spare output [] []))
      (embedState emitRegisters emitPorts frame
        (SubexpRecordScan.recordState (SubexpArgumentProgram.finishedRegs regs) [] [] spare
          (true :: (Encoding.frame (SubexpArgumentProgram.recordBody key coefficient) ++ output)) [] [])) := by
  exact eval_call_lifted RawEmitter.emitRawTermProgram emitRegisters emitPorts frame
    emitRegisters_injective emitPorts_injective
    (RawEmitter.emitRawTerm_trace key coefficient spare output regs)

def emittedRegs (regs : Fin 8 → Bool) : Fin 8 → Bool :=
  Function.update (Function.update regs 0 true) 1 false

theorem emitController_eval (regs : Fin 8 → Bool)
    (modulus coefficient width query slots output left right master : List Bool) :
    Eval emitCall (37 * coefficient.length + 21 * query.length + 57)
      (controllerState regs modulus coefficient width query [] slots output left right master)
      (controllerState (emittedRegs regs) modulus [] width [] [] slots
        (true :: (Encoding.frame (SubexpArgumentProgram.recordBody query coefficient) ++ output))
        left right master) := by
  let d := controllerState regs modulus coefficient width query [] slots output left right master
  let result := controllerState (emittedRegs regs) modulus [] width [] [] slots
    (true :: (Encoding.frame (SubexpArgumentProgram.recordBody query coefficient) ++ output))
    left right master
  let rs : Fin 5 → Bool := fun i => regs (emitRegisters i)
  let a := SubexpRecordScan.recordState rs coefficient query.reverse master output [] []
  let b := SubexpRecordScan.recordState (SubexpArgumentProgram.finishedRegs rs) [] [] master
    (true :: (Encoding.frame (SubexpArgumentProgram.recordBody query coefficient) ++ output)) [] []
  have ha : embedState emitRegisters emitPorts d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ emitRegisters_injective emitPorts_injective
    · intro i; rfl
    · intros; rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have hb : embedState emitRegisters emitPorts d b = result := by
    apply embedState_eq_of_ports _ _ _ _ _ emitRegisters_injective emitPorts_injective
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have h0 : i ≠ 0 := by
        intro h; apply hi; exact ⟨0, by simp [emitRegisters, h]⟩
      have h1 : i ≠ 1 := by
        intro h; apply hi; exact ⟨1, by simp [emitRegisters, h]⟩
      simp [d, result, controllerState, extendState, SubexpCoefficientLookup.state,
        SubexpFlatAdd.ready, SubexpFlatAdd.state, emittedRegs, h0, h1]
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have h8 : i ≠ 8 := by
        intro h; apply hi; exact ⟨0, by simp [emitPorts, h]⟩
      have h14 : i ≠ 14 := by
        intro h; apply hi; exact ⟨1, by simp [emitPorts, h]⟩
      have h21 : i ≠ 21 := by
        intro h; apply hi; exact ⟨3, by simp [emitPorts, h]⟩
      fin_cases i <;>
        simp_all [d, result, controllerState, extendState, SubexpCoefficientLookup.state,
          SubexpCoefficientLookup.frame, SubexpFlatAdd.ready, SubexpFlatAdd.state,
          SubexpFlatAdd.stacks, Fin.addCases, Fin.coe_ofNat_eq_mod]
  have h := emitCall_eval d query coefficient master output rs
  change Eval emitCall _ (embedState emitRegisters emitPorts d a)
    (embedState emitRegisters emitPorts d b) at h
  simpa only [ha, hb] using h

theorem resetFlags_eval (d : State 8 26) :
    Eval resetFlags 3 d ⟨SubexpCoefficientLookup.normalized d.regs false true false, d.stacks⟩ := by
  let a₀ : StructuredProgram.Atom 8 26 := .set 0 false
  let a₁ : StructuredProgram.Atom 8 26 := .set 1 true
  let a₇ : StructuredProgram.Atom 8 26 := .set 7 false
  have h₀ := Eval.base (StructuredProgram.Eval.atom a₀ d)
  have h₁ := Eval.base (StructuredProgram.Eval.atom a₁ (a₀.eval d))
  have h₇ := Eval.base (StructuredProgram.Eval.atom a₇ (a₁.eval (a₀.eval d)))
  simpa [resetFlags, a₀, a₁, a₇, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr,
    SubexpCoefficientLookup.normalized] using Eval.seq h₀ (Eval.seq h₁ h₇)

section SlotExecution

open SubexpCoefficientLookup SubexpLiftRing

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

def lookupValue (query : List Bool) (records : List (Record p μ)) : Coefficient p μ :=
  fold p μ M query (zeroCoefficient p μ) records

def singleSlotCost (query : List Bool) (records : List (Record p μ)) : ℕ :=
  (7 * (Encoding.encodeList id (encoded p μ records)).length + 5) +
    (14 * baseWidth p μ + 12 +
      RecordPrograms.budget (recordCost (baseWidth p μ) query) (encoded p μ records)) +
    (37 * (SubexpFlatAdd.encode (lookupValue p μ M query records)).length +
      21 * query.length + 57) + 3

omit [Fact p.Prime] in
theorem singleSlotCost_eq (query : List Bool) (records : List (Record p μ)) :
    singleSlotCost p μ M query records =
      7 * (Encoding.encodeList id (encoded p μ records)).length +
        RecordPrograms.budget (recordCost (baseWidth p μ) query) (encoded p μ records) +
        162 * baseWidth p μ + 21 * query.length + 77 := by
  simp only [singleSlotCost, SubexpFlatAdd.encode_length]
  ring

/-- This coefficient is polynomial in the actual bit widths and independent
of the number of records. It includes all copy, scan, emit and reset steps. -/
def scanFactor (B I : ℕ) : ℕ :=
  30 * I + 4 * SubexpFlatAdd.wordCost B + 220 * B + 180

omit [Fact p.Prime] in
theorem singleSlotCost_le_serialized (query : List Bool) (records : List (Record p μ))
    (I : ℕ) (hquery : query.length ≤ I) :
    singleSlotCost p μ M query records ≤
      scanFactor (baseWidth p μ) I *
        ((Encoding.encodeList id (encoded p μ records)).length + 1) := by
  have hs := scan_budget_le_input (baseWidth p μ) query (encoded p μ records)
  have hq := Nat.mul_le_mul_right
    ((Encoding.encodeList id (encoded p μ records)).length + 1) hquery
  rw [singleSlotCost_eq]
  unfold scanFactor
  nlinarith

/-- A complete one-slot execution: preserving copy, actual full-list lookup,
actual raw record writer, and flag reset. Every called service is concrete. -/
theorem slotCallback_eval (regs : Fin 8 → Bool) (records : List (Record p μ))
    (width query slots output right master : List Bool) (hwidth : width.length = baseWidth p μ) :
    ∃ n ≤ singleSlotCost p μ M query records, ∃ regs',
      Eval slotCallback n
        (controllerState regs M.bits [] width query [] slots output
          (Encoding.encodeList id (encoded p μ records)) right master)
        (controllerState (normalized regs' false true false) M.bits [] width [] [] slots
          (true :: (Encoding.frame (SubexpArgumentProgram.recordBody query
            (SubexpFlatAdd.encode (lookupValue p μ M query records))) ++ output))
          (Encoding.encodeList id (encoded p μ records)) right master) := by
  let left := Encoding.encodeList id (encoded p μ records)
  let value := lookupValue p μ M query records
  let r₀ := readRegs regs 0 1 none
  have hc := copyLeft_eval regs M.bits [] width query slots output left right master
  obtain ⟨n, hn, r₁, hl⟩ := lookupCall_eval p μ M r₀ records width query hwidth
    ![slots, output, left, right, [], master]
  let r₂ := normalized r₁ false true false
  have he := emitController_eval r₂ M.bits (SubexpFlatAdd.encode value) width query
    slots output left right master
  let finalOutput := true :: (Encoding.frame (SubexpArgumentProgram.recordBody query
    (SubexpFlatAdd.encode value)) ++ output)
  let d := controllerState (emittedRegs r₂) M.bits [] width [] [] slots finalOutput left right master
  have hr := resetFlags_eval d
  change Eval resetFlags 3 d
    (controllerState (normalized (emittedRegs r₂) false true false)
      M.bits [] width [] [] slots finalOutput left right master) at hr
  have hh := Eval.seq hc (Eval.seq hl (Eval.seq he hr))
  refine ⟨(7 * left.length + 5) + (n +
    ((37 * (SubexpFlatAdd.encode value).length + 21 * query.length + 57) + 3)), ?_,
    emittedRegs r₂, ?_⟩
  · dsimp only [singleSlotCost, left, value]
    omega
  · simpa only [slotCallback, d, r₀, r₂, left, value, finalOutput, lookupValue] using hh

def additionValue (query : List Bool) (left right : List (Record p μ)) : Coefficient p μ :=
  fold p μ M query (lookupValue p μ M query left) right

def additionSlotCost (query : List Bool) (left right : List (Record p μ)) : ℕ :=
  singleSlotCost p μ M query left +
    7 * (Encoding.encodeList id (encoded p μ right)).length + 9 +
    RecordPrograms.budget (recordCost (baseWidth p μ) query) (encoded p μ right)

omit [Fact p.Prime] in
theorem additionSlotCost_le_serialized (query : List Bool)
    (left right : List (Record p μ)) (I : ℕ) (hquery : query.length ≤ I) :
    additionSlotCost p μ M query left right ≤
      scanFactor (baseWidth p μ) I *
        ((Encoding.encodeList id (encoded p μ left)).length +
          (Encoding.encodeList id (encoded p μ right)).length + 2) := by
  have hl := singleSlotCost_le_serialized p μ M query left I hquery
  have hr := singleSlotCost_le_serialized p μ M query right I hquery
  have hsum : additionSlotCost p μ M query left right ≤
      singleSlotCost p μ M query left + singleSlotCost p μ M query right := by
    rw [additionSlotCost, singleSlotCost_eq p μ M query right]
    omega
  nlinarith

theorem additionSlotCallback_eval (regs : Fin 8 → Bool)
    (leftRecords rightRecords : List (Record p μ))
    (width query slots output master : List Bool) (hwidth : width.length = baseWidth p μ) :
    ∃ n ≤ additionSlotCost p μ M query leftRecords rightRecords, ∃ regs',
      Eval additionSlotCallback n
        (controllerState regs M.bits [] width query [] slots output
          (Encoding.encodeList id (encoded p μ leftRecords))
          (Encoding.encodeList id (encoded p μ rightRecords)) master)
        (controllerState (normalized regs' false true false) M.bits [] width [] [] slots
          (true :: (Encoding.frame (SubexpArgumentProgram.recordBody query
            (SubexpFlatAdd.encode (additionValue p μ M query leftRecords rightRecords))) ++ output))
          (Encoding.encodeList id (encoded p μ leftRecords))
          (Encoding.encodeList id (encoded p μ rightRecords)) master) := by
  let left := Encoding.encodeList id (encoded p μ leftRecords)
  let right := Encoding.encodeList id (encoded p μ rightRecords)
  let first := lookupValue p μ M query leftRecords
  let value := additionValue p μ M query leftRecords rightRecords
  let r₀ := readRegs regs 0 1 none
  have hc₀ := copyLeft_eval regs M.bits [] width query slots output left right master
  obtain ⟨n, hn, r₁, hl⟩ := lookupCall_eval p μ M r₀ leftRecords width query hwidth
    ![slots, output, left, right, [], master]
  let r₂ := normalized r₁ false true false
  have hc₁ := copyRight_eval r₂ M.bits (SubexpFlatAdd.encode first) width query
    slots output left right master
  let r₃ := readRegs r₂ 0 1 none
  obtain ⟨m, hm, r₄, hs⟩ := scanCall_eval p μ M r₃ first rightRecords width query hwidth
    ![slots, output, left, right, [], master]
  let r₅ := normalized r₄ false true false
  have he := emitController_eval r₅ M.bits (SubexpFlatAdd.encode value) width query
    slots output left right master
  let finalOutput := true :: (Encoding.frame (SubexpArgumentProgram.recordBody query
    (SubexpFlatAdd.encode value)) ++ output)
  let d := controllerState (emittedRegs r₅) M.bits [] width [] [] slots finalOutput left right master
  have hr := resetFlags_eval d
  change Eval resetFlags 3 d
    (controllerState (normalized (emittedRegs r₅) false true false)
      M.bits [] width [] [] slots finalOutput left right master) at hr
  have hh := Eval.seq hc₀ (Eval.seq hl (Eval.seq hc₁ (Eval.seq hs (Eval.seq he hr))))
  refine ⟨(7 * left.length + 5) + (n + ((7 * right.length + 5) + (m +
    ((37 * (SubexpFlatAdd.encode value).length + 21 * query.length + 57) + 3)))), ?_,
    emittedRegs r₅, ?_⟩
  · simp only [additionSlotCost, singleSlotCost, SubexpFlatAdd.encode_length]
    dsimp only [left, right] at *
    omega
  · simpa only [additionSlotCallback, d, r₀, r₂, r₃, r₅, left, right, first, value,
      finalOutput, additionValue, lookupValue] using hh

end SlotExecution

theorem controllerOuterState (regs : Fin 8 → Bool)
    (modulus width output left right master : List Bool)
    (v pr found : Bool) (source payload : List Bool) :
    RecordPrograms.state slotPorts
        (controllerState regs modulus [] width [] [] [] output left right master)
        v pr found source payload =
      controllerState (SubexpCoefficientLookup.normalized regs v pr found)
        modulus [] width payload.reverse [] source output left right master := by
  apply SubexpScanPrimitives.state_ext
  · funext i
    fin_cases i <;>
      simp [RecordPrograms.state, slotPorts, controllerState, extendState,
        SubexpCoefficientLookup.state, SubexpCoefficientLookup.normalized,
        SubexpFlatAdd.ready, SubexpFlatAdd.state]
  · funext i
    fin_cases i <;>
      simp [RecordPrograms.state, slotPorts, controllerState, extendState,
        SubexpCoefficientLookup.state, SubexpCoefficientLookup.frame,
        SubexpFlatAdd.ready, SubexpFlatAdd.state, SubexpFlatAdd.stacks,
        Fin.addCases, Fin.coe_ofNat_eq_mod]

def controllerInvariant (modulus width left right master : List Bool) (d : State 8 26) : Prop :=
  ∃ (regs : Fin 8 → Bool) (output : List Bool),
    d = controllerState regs modulus [] width [] [] [] output left right master

section ProjectionLoop

open SubexpCoefficientLookup SubexpLiftRing

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

def projectedBody (records : List (Record p μ)) (query : List Bool) : List Bool :=
  SubexpArgumentProgram.recordBody query (SubexpFlatAdd.encode (lookupValue p μ M query records))

theorem slotCallback_contract (records : List (Record p μ))
    (width right master : List Bool) (hwidth : width.length = baseWidth p μ) :
    RecordPrograms.CallbackContractWith slotPorts slotCallback (fun _ => false)
      (fun query => singleSlotCost p μ M query records)
      (controllerInvariant M.bits width (Encoding.encodeList id (encoded p μ records)) right master)
      (PrependEffect 21 (projectedBody p μ M records)) := by
  intro query tail base valid
  obtain ⟨regs, output, rfl⟩ := valid
  obtain ⟨n, hn, regs', hrun⟩ := slotCallback_eval p μ M
    (normalized regs false true false) records width query tail output right master hwidth
  let out := true :: (Encoding.frame (projectedBody p μ M records query) ++ output)
  let next := controllerState regs' M.bits [] width [] [] [] out
    (Encoding.encodeList id (encoded p μ records)) right master
  refine ⟨n, next, hn, ⟨regs', out, rfl⟩, ?_, ?_⟩
  · rfl
  · rw [controllerOuterState, controllerOuterState]
    simpa only [List.reverse_reverse, List.reverse_nil, out, next, projectedBody] using hrun

/-- The complete projection table scans all supplied keys, executes a concrete
whole-list lookup per key, and writes the exact sequence of framed results.
Input keys are visited in the supplied order; prepending reverses that order. -/
theorem projectProgram_runs (records : List (Record p μ)) (queries : List (List Bool))
    (width right master inputSuffix : List Bool) (hwidth : width.length = baseWidth p μ)
    (regs : Fin 8 → Bool) (suffix : List (List Bool)) (v pr found : Bool) :
    ∃ next : State 8 26,
      controllerInvariant M.bits width (Encoding.encodeList id (encoded p μ records)) right master next ∧
      next.stacks 21 = Encoding.encodeList id
        (queries.reverse.map (projectedBody p μ M records) ++ suffix) ∧
      RunsIn projectProgram
        (4 + RecordPrograms.budget (fun query => singleSlotCost p μ M query records) queries)
        ((RecordPrograms.state slotPorts
          (controllerState regs M.bits [] width [] [] [] (Encoding.encodeList id suffix)
            (Encoding.encodeList id (encoded p μ records)) right master)
          v pr found (Encoding.encodeList id queries ++ inputSuffix) []).withPC
          (some projectProgram.entry))
        ((RecordPrograms.state slotPorts next false true false inputSuffix []).withPC none) := by
  let base := controllerState regs M.bits [] width [] [] [] (Encoding.encodeList id suffix)
    (Encoding.encodeList id (encoded p μ records)) right master
  have valid : controllerInvariant M.bits width
      (Encoding.encodeList id (encoded p μ records)) right master base :=
    ⟨regs, Encoding.encodeList id suffix, rfl⟩
  obtain ⟨next, hnext, hout, hrun⟩ := projectionController_run slotPorts slotCallback (21 : Fin 26)
    (by decide) (by decide) (projectedBody p μ M records)
    (fun query => singleSlotCost p μ M query records)
    (controllerInvariant M.bits width (Encoding.encodeList id (encoded p μ records)) right master)
    (slotCallback_contract p μ M records width right master hwidth)
    queries suffix inputSuffix base valid rfl v pr found
  exact ⟨next, hnext, hout, hrun⟩

end ProjectionLoop

section AdditionLoop

open SubexpCoefficientLookup SubexpLiftRing

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

def addedBody (left right : List (Record p μ)) (query : List Bool) : List Bool :=
  SubexpArgumentProgram.recordBody query
    (SubexpFlatAdd.encode (additionValue p μ M query left right))

theorem additionSlotCallback_contract (left right : List (Record p μ))
    (width master : List Bool) (hwidth : width.length = baseWidth p μ) :
    RecordPrograms.CallbackContractWith slotPorts additionSlotCallback (fun _ => false)
      (fun query => additionSlotCost p μ M query left right)
      (controllerInvariant M.bits width (Encoding.encodeList id (encoded p μ left))
        (Encoding.encodeList id (encoded p μ right)) master)
      (PrependEffect 21 (addedBody p μ M left right)) := by
  intro query tail base valid
  obtain ⟨regs, output, rfl⟩ := valid
  obtain ⟨n, hn, regs', hrun⟩ := additionSlotCallback_eval p μ M
    (normalized regs false true false) left right width query tail output master hwidth
  let out := true :: (Encoding.frame (addedBody p μ M left right query) ++ output)
  let next := controllerState regs' M.bits [] width [] [] [] out
    (Encoding.encodeList id (encoded p μ left))
    (Encoding.encodeList id (encoded p μ right)) master
  refine ⟨n, next, hn, ⟨regs', out, rfl⟩, ?_, ?_⟩
  · rfl
  · rw [controllerOuterState, controllerOuterState]
    simpa only [List.reverse_reverse, List.reverse_nil, out, next, addedBody] using hrun

/-- Complete finite addition controller. Both operands may contain arbitrary
raw keys and duplicate coefficients: each requested output key is obtained by
two actual scans of the encoded input lists. -/
theorem addProgram_runs (left right : List (Record p μ)) (queries : List (List Bool))
    (width master inputSuffix : List Bool) (hwidth : width.length = baseWidth p μ)
    (regs : Fin 8 → Bool) (suffix : List (List Bool)) (v pr found : Bool) :
    ∃ next : State 8 26,
      controllerInvariant M.bits width (Encoding.encodeList id (encoded p μ left))
        (Encoding.encodeList id (encoded p μ right)) master next ∧
      next.stacks 21 = Encoding.encodeList id
        (queries.reverse.map (addedBody p μ M left right) ++ suffix) ∧
      RunsIn addProgram
        (4 + RecordPrograms.budget (fun query => additionSlotCost p μ M query left right) queries)
        ((RecordPrograms.state slotPorts
          (controllerState regs M.bits [] width [] [] [] (Encoding.encodeList id suffix)
            (Encoding.encodeList id (encoded p μ left))
            (Encoding.encodeList id (encoded p μ right)) master)
          v pr found (Encoding.encodeList id queries ++ inputSuffix) []).withPC
          (some addProgram.entry))
        ((RecordPrograms.state slotPorts next false true false inputSuffix []).withPC none) := by
  let base := controllerState regs M.bits [] width [] [] [] (Encoding.encodeList id suffix)
    (Encoding.encodeList id (encoded p μ left))
    (Encoding.encodeList id (encoded p μ right)) master
  have valid : controllerInvariant M.bits width
      (Encoding.encodeList id (encoded p μ left))
      (Encoding.encodeList id (encoded p μ right)) master base :=
    ⟨regs, Encoding.encodeList id suffix, rfl⟩
  exact projectionController_run slotPorts additionSlotCallback (21 : Fin 26)
    (by decide) (by decide) (addedBody p μ M left right)
    (fun query => additionSlotCost p μ M query left right)
    (controllerInvariant M.bits width (Encoding.encodeList id (encoded p μ left))
      (Encoding.encodeList id (encoded p μ right)) master)
    (additionSlotCallback_contract p μ M left right width master hwidth)
    queries suffix inputSuffix base valid rfl v pr found

end AdditionLoop

section ExactLocalStates

open SubexpCoefficientLookup SubexpLiftRing

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

/-- Complete local-state form of the projection trace, including the preserved
input/cache stacks and empty work stacks. -/
theorem projectProgram_run (records : List (Record p μ)) (queries : List (List Bool))
    (width right master : List Bool) (hwidth : width.length = baseWidth p μ)
    (regs : Fin 8 → Bool) :
    ∃ finalRegs, RunsIn projectProgram
      (4 + RecordPrograms.budget (fun query => singleSlotCost p μ M query records) queries)
      ((controllerState regs M.bits [] width [] [] (Encoding.encodeList id queries) [false]
        (Encoding.encodeList id (encoded p μ records)) right master).withPC
          (some projectProgram.entry))
      ((controllerState (normalized finalRegs false true false) M.bits [] width [] [] []
        (Encoding.encodeList id (queries.reverse.map (projectedBody p μ M records)))
        (Encoding.encodeList id (encoded p μ records)) right master).withPC none) := by
  obtain ⟨next, hnext, hout, hrun⟩ := projectProgram_runs p μ M records queries
    width right master [] hwidth regs [] (regs 0) (regs 1) (regs 7)
  obtain ⟨finalRegs, output, rfl⟩ := hnext
  change output = _ at hout
  simp only [List.append_nil] at hout
  subst output
  refine ⟨finalRegs, ?_⟩
  simpa only [controllerOuterState, normalized_self, List.append_nil,
    List.reverse_nil, Encoding.encodeList] using hrun

theorem addProgram_run (left right : List (Record p μ)) (queries : List (List Bool))
    (width master : List Bool) (hwidth : width.length = baseWidth p μ)
    (regs : Fin 8 → Bool) :
    ∃ finalRegs, RunsIn addProgram
      (4 + RecordPrograms.budget (fun query => additionSlotCost p μ M query left right) queries)
      ((controllerState regs M.bits [] width [] [] (Encoding.encodeList id queries) [false]
        (Encoding.encodeList id (encoded p μ left))
        (Encoding.encodeList id (encoded p μ right)) master).withPC
          (some addProgram.entry))
      ((controllerState (normalized finalRegs false true false) M.bits [] width [] [] []
        (Encoding.encodeList id (queries.reverse.map (addedBody p μ M left right)))
        (Encoding.encodeList id (encoded p μ left))
        (Encoding.encodeList id (encoded p μ right)) master).withPC none) := by
  obtain ⟨next, hnext, hout, hrun⟩ := addProgram_runs p μ M left right queries
    width master [] hwidth regs [] (regs 0) (regs 1) (regs 7)
  obtain ⟨finalRegs, output, rfl⟩ := hnext
  change output = _ at hout
  simp only [List.append_nil] at hout
  subst output
  refine ⟨finalRegs, ?_⟩
  simpa only [controllerOuterState, normalized_self, List.append_nil,
    List.reverse_nil, Encoding.encodeList] using hrun

end ExactLocalStates

section AlgebraicRefinement

open SubexpSymbolicCost SymbolicCost SubexpQuarticRing SubexpLiftRing

def encodedRaw {D : ℕ} {C : Type*} (P : CoeffList D C) : List (List Bool × C) :=
  P.map fun term => (fixedKey term.1, term.2)

def decodedRaw {D : ℕ} {C R : Type*} (decode : C → R) (P : CoeffList D C) : CoeffList D R :=
  P.map fun term => (term.1, decode term.2)

theorem fixedKey_coeff_sum {D : ℕ} {C R : Type*} [Semiring R]
    (decode : C → R) (P : CoeffList D C) (a : RawIndex D) :
    ((encodedRaw P).map (fun r => if r.1 = fixedKey a then decode r.2 else 0)).sum =
      coeff (decodedRaw decode P) a := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    rcases p with ⟨b, c⟩
    have hk : fixedKey b = fixedKey a ↔ b = a := fixedKey_injective.eq_iff
    simp only [encodedRaw, decodedRaw, List.map_cons, List.sum_cons, coeff] at ih ⊢
    simp only [hk, ih]

theorem lookup_raw_coefficient (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D + 1))
    (c : Fin 4 → ZMod (p ^ (D + 1))) (P : CoeffList D (QuarticCode p D)) (a : RawIndex D) :
    quotientDenote c
        ((lookupValue p (D + 1) M (fixedKey a) (encodedRaw P)).map (wordValue p (D + 1))) =
      coeff (decodedRaw (fun z => quotientDenote c (z.map (wordValue p (D + 1)))) P) a := by
  rw [lookupValue, SubexpCoefficientLookup.lookup_quotient]
  exact fixedKey_coeff_sum
    (fun z : QuarticCode p D => quotientDenote c (z.map (wordValue p (D+1)))) P a

theorem addition_raw_coefficient (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D + 1))
    (c : Fin 4 → ZMod (p ^ (D + 1))) (P Q : CoeffList D (QuarticCode p D)) (a : RawIndex D) :
    quotientDenote c
        ((additionValue p (D + 1) M (fixedKey a) (encodedRaw P) (encodedRaw Q)).map
          (wordValue p (D + 1))) =
      coeff (decodedRaw (fun z => quotientDenote c (z.map (wordValue p (D + 1)))) P) a +
      coeff (decodedRaw (fun z => quotientDenote c (z.map (wordValue p (D + 1)))) Q) a := by
  rw [additionValue, SubexpCoefficientLookup.fold_quotient, lookup_raw_coefficient]
  rw [fixedKey_coeff_sum
    (fun z : QuarticCode p D => quotientDenote c (z.map (wordValue p (D+1)))) Q a]

open SubexpCanonicalWords

theorem zeroCoefficient_canonical (p μ : ℕ) [Fact p.Prime] :
    CanonicalQuad p μ (SubexpCoefficientLookup.zeroCoefficient p μ) := by
  have hz (n : ℕ) : BinaryArithmetic.toNat (List.replicate n false) = 0 := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp [List.replicate_succ, BinaryArithmetic.toNat_cons, BinaryArithmetic.bitVal_false, ih]
  have hp : 0 < p^μ := pow_pos (Fact.out : p.Prime).pos μ
  simpa [CanonicalQuad, CanonicalWord, SubexpCoefficientLookup.zeroCoefficient,
    SubexpPreparedQuartic.zeroWord, hz] using And.intro hp (And.intro hp (And.intro hp hp))

theorem lookupFold_canonical (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (query : List Bool)
    (records : List (SubexpCoefficientLookup.Record p μ))
    (a : SubexpCoefficientLookup.Coefficient p μ) (ha : CanonicalQuad p μ a) :
    CanonicalQuad p μ (SubexpCoefficientLookup.fold p μ M query a records) := by
  induction records generalizing a with
  | nil => exact ha
  | cons r records ih =>
    simp only [SubexpCoefficientLookup.fold, List.foldl_cons]
    apply ih
    by_cases h : r.1 = query
    · simp only [SubexpCoefficientLookup.update, h, ite_true]
      exact binaryAdd_canonical p μ M _ _
    · simpa only [SubexpCoefficientLookup.update, h, ite_false] using ha

theorem programScan_canonical (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1)) (t z o : QuarticCode p D)
    (hz : CanonicalQuad p (D+1) z) (P : CoeffList D (QuarticCode p D)) (a : RawIndex D) :
    CanonicalQuad p (D+1) (programScan (preparedProgram p D M t z o) P a).1 :=
  SubexpCanonicalDense.scan_canonical p D M t z o hz P a

theorem programScan_quotient (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1))
    (c : Fin 4 → ZMod (p^(D+1))) (t z o : QuarticCode p D)
    (hz : quotientDenote c (z.map (wordValue p (D+1))) = 0)
    (P : CoeffList D (QuarticCode p D)) (a : RawIndex D) :
    quotientDenote c ((programScan (preparedProgram p D M t z o) P a).1.map
      (wordValue p (D+1))) =
      coeff (decodedRaw (fun v => quotientDenote c (v.map (wordValue p (D+1)))) P) a :=
  SubexpCanonicalDense.scan_quotient p D M t z o c hz P a

/-- The machine's left-fold accumulator and the source evaluator's right-fold
scan produce identical coefficient bytes. This uses canonical modular outputs,
not an assumed ring structure on raw words. -/
theorem lookup_programScan (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1))
    (c : Fin 4 → ZMod (p^(D+1))) (t z o : QuarticCode p D)
    (hz : quotientDenote c (z.map (wordValue p (D+1))) = 0)
    (hcanonical : CanonicalQuad p (D+1) z)
    (P : CoeffList D (QuarticCode p D)) (a : RawIndex D) :
    lookupValue p (D+1) M (fixedKey a) (encodedRaw P) =
      (programScan (preparedProgram p D M t z o) P a).1 := by
  apply quad_eq_of_quotient_eq p (D+1) (Nat.zero_lt_succ D) c
  · exact lookupFold_canonical p (D+1) M _ _ _ (zeroCoefficient_canonical p (D+1))
  · exact programScan_canonical p D M t z o hcanonical P a
  · rw [lookup_raw_coefficient, programScan_quotient p D M c t z o hz]

theorem lookup_programProject (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1))
    (c : Fin 4 → ZMod (p^(D+1))) (t z o : QuarticCode p D)
    (hz : quotientDenote c (z.map (wordValue p (D+1))) = 0)
    (hcanonical : CanonicalQuad p (D+1) z)
    (P : CoeffList D (QuarticCode p D)) (slots : List (RawIndex D)) :
    slots.map (fun a => (a, lookupValue p (D+1) M (fixedKey a) (encodedRaw P))) =
      (programProject (preparedProgram p D M t z o) slots P).1 := by
  induction slots with
  | nil => rfl
  | cons a slots ih =>
    simp only [List.map_cons, programProject, ih,
      lookup_programScan p D M c t z o hz hcanonical P a]

theorem flat_encode_eq_block (p D : ℕ) (a : QuarticCode p D) :
    SubexpFlatAdd.encode a = (quarticCodeBlockCode p D).block a := by
  simp [SubexpFlatAdd.encode, SubexpFlatAdd.flatten, SubexpFlatAdd.quadWords,
    quarticCodeBlockCode, recordBlockCode, wordBlockCode, quadToPair, List.append_assoc]

/-- Exact serialized output, including both record frames and the outer list.
The slot iterator visits the reverse of `slots` to obtain this forward order. -/
theorem projected_bytes_eq_programProject (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1))
    (c : Fin 4 → ZMod (p^(D+1))) (t z o : QuarticCode p D)
    (hz : quotientDenote c (z.map (wordValue p (D+1))) = 0)
    (hcanonical : CanonicalQuad p (D+1) z)
    (P : CoeffList D (QuarticCode p D)) (slots : List (RawIndex D)) :
    Encoding.encodeList id
        (slots.map (fun a => projectedBody p (D+1) M (encodedRaw P) (fixedKey a))) =
      SubexpDenseSerialization.encodeFixedQuarticCoefficients p D
        (programProject (preparedProgram p D M t z o) slots P).1 := by
  induction slots with
  | nil => rfl
  | cons a slots ih =>
    simp only [List.map_cons, Encoding.encodeList, programProject,
      SubexpDenseSerialization.encodeFixedQuarticCoefficients,
      SubexpDenseSerialization.encodeFixedCoefficients] at ih ⊢
    rw [ih]
    simp only [projectedBody, SubexpArgumentProgram.recordBody,
      SubexpDenseSerialization.encodeFixedRecord, framedRecord,
      lookup_programScan p D M c t z o hz hcanonical P a,
      flat_encode_eq_block, id_eq]

theorem additionValue_eq_lookup_append (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (query : List Bool)
    (left right : List (SubexpCoefficientLookup.Record p μ)) :
    additionValue p μ M query left right = lookupValue p μ M query (left ++ right) := by
  simp [additionValue, lookupValue, SubexpCoefficientLookup.fold, List.foldl_append]

theorem encodedRaw_bytes (p D : ℕ) [Fact p.Prime] (P : CoeffList D (QuarticCode p D)) :
    Encoding.encodeList id (SubexpCoefficientLookup.encoded p (D+1) (encodedRaw P)) =
      SubexpDenseSerialization.encodeFixedQuarticCoefficients p D P := by
  induction P with
  | nil => rfl
  | cons term P ih =>
    rcases term with ⟨a,v⟩
    change true :: (Encoding.frame (framedRecord (fixedKey a) (SubexpFlatAdd.encode v)) ++
        Encoding.encodeList id (SubexpCoefficientLookup.encoded p (D+1) (encodedRaw P))) =
      true :: (Encoding.frame (framedRecord (fixedKey a) ((quarticCodeBlockCode p D).block v)) ++
        SubexpDenseSerialization.encodeFixedQuarticCoefficients p D P)
    rw [ih, flat_encode_eq_block]

theorem added_bytes_eq_programAdd (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1))
    (c : Fin 4 → ZMod (p^(D+1))) (t z o : QuarticCode p D)
    (hz : quotientDenote c (z.map (wordValue p (D+1))) = 0)
    (hcanonical : CanonicalQuad p (D+1) z)
    (P Q : CoeffList D (QuarticCode p D)) (slots : List (RawIndex D)) :
    Encoding.encodeList id
        (slots.map (fun a => addedBody p (D+1) M (encodedRaw P) (encodedRaw Q) (fixedKey a))) =
      SubexpDenseSerialization.encodeFixedQuarticCoefficients p D
        (programAdd (preparedProgram p D M t z o) slots P Q).1 := by
  have hbody (query : List Bool) :
      addedBody p (D+1) M (encodedRaw P) (encodedRaw Q) query =
        projectedBody p (D+1) M (encodedRaw (P ++ Q)) query := by
    simp only [addedBody, projectedBody, additionValue_eq_lookup_append,
      encodedRaw, List.map_append]
  simp_rw [hbody]
  simpa only [programAdd, appendWithCost_eq] using
    projected_bytes_eq_programProject p D M c t z o hz hcanonical (P ++ Q) slots

end AlgebraicRefinement

section ExactSerializedStates

open SymbolicCost SubexpSymbolicCost SubexpLiftRing SubexpQuarticRing
open SubexpCanonicalWords SubexpDenseSerialization SubexpCoefficientLookup

def queryBytes {D : ℕ} (slots : List (RawIndex D)) : List Bool :=
  Encoding.encodeList id ((slots.map fixedKey).reverse)

def projectionTime (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1))
    (P : CoeffList D (QuarticCode p D)) (slots : List (RawIndex D)) : ℕ :=
  4 + RecordPrograms.budget (fun query => singleSlotCost p (D+1) M query (encodedRaw P))
    ((slots.map fixedKey).reverse)

def additionTime (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1))
    (P Q : CoeffList D (QuarticCode p D)) (slots : List (RawIndex D)) : ℕ :=
  4 + RecordPrograms.budget
    (fun query => additionSlotCost p (D+1) M query (encodedRaw P) (encodedRaw Q))
    ((slots.map fixedKey).reverse)

variable (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D+1))
    (c : Fin 4 → ZMod (p^(D+1))) (t z o : QuarticCode p D)
    (hz : quotientDenote c (z.map (wordValue p (D+1))) = 0)
    (hcanonical : CanonicalQuad p (D+1) z)

include hz hcanonical

/-- Stable physical-wrapper interface: exact bytes and all 26 local stacks.
Raw input keys are unrestricted; the supplied output slot list determines the
projection. All caches and the input master are retained. -/
theorem projectProgram_exact (P : CoeffList D (QuarticCode p D))
    (slots : List (RawIndex D)) (width right : List Bool)
    (hwidth : width.length = baseWidth p (D+1)) (regs : Fin 8 → Bool) :
    ∃ finalRegs, RunsIn projectProgram (projectionTime p D M P slots)
      ((controllerState regs M.bits [] width [] [] (queryBytes slots) [false]
        (encodeFixedQuarticCoefficients p D P) right (queryBytes slots)).withPC
          (some projectProgram.entry))
      ((controllerState (normalized finalRegs false true false) M.bits [] width [] [] []
        (encodeFixedQuarticCoefficients p D
          (programProject (preparedProgram p D M t z o) slots P).1)
        (encodeFixedQuarticCoefficients p D P) right (queryBytes slots)).withPC none) := by
  have hout := projected_bytes_eq_programProject p D M c t z o hz hcanonical P slots
  obtain ⟨finalRegs, hrun⟩ := projectProgram_run p (D+1) M (encodedRaw P)
    ((slots.map fixedKey).reverse) width right (queryBytes slots) hwidth regs
  refine ⟨finalRegs, ?_⟩
  simpa only [List.reverse_reverse, List.map_map, Function.comp_def,
    encodedRaw_bytes, hout, projectionTime, queryBytes] using hrun

theorem addProgram_exact (P Q : CoeffList D (QuarticCode p D))
    (slots : List (RawIndex D)) (width : List Bool)
    (hwidth : width.length = baseWidth p (D+1)) (regs : Fin 8 → Bool) :
    ∃ finalRegs, RunsIn addProgram (additionTime p D M P Q slots)
      ((controllerState regs M.bits [] width [] [] (queryBytes slots) [false]
        (encodeFixedQuarticCoefficients p D P) (encodeFixedQuarticCoefficients p D Q)
        (queryBytes slots)).withPC (some addProgram.entry))
      ((controllerState (normalized finalRegs false true false) M.bits [] width [] [] []
        (encodeFixedQuarticCoefficients p D
          (programAdd (preparedProgram p D M t z o) slots P Q).1)
        (encodeFixedQuarticCoefficients p D P) (encodeFixedQuarticCoefficients p D Q)
        (queryBytes slots)).withPC none) := by
  have hout := added_bytes_eq_programAdd p D M c t z o hz hcanonical P Q slots
  obtain ⟨finalRegs, hrun⟩ := addProgram_run p (D+1) M (encodedRaw P) (encodedRaw Q)
    ((slots.map fixedKey).reverse) width (queryBytes slots) hwidth regs
  refine ⟨finalRegs, ?_⟩
  simpa only [List.reverse_reverse, List.map_map, Function.comp_def,
    encodedRaw_bytes, hout, additionTime, queryBytes] using hrun

end ExactSerializedStates

end SubexponentialSAT.SubexpDenseProgram.Projection

end OAI.Algorithms
