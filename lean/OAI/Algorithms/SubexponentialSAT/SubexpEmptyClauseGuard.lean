import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpEmptyClauseProgram
import OAI.Algorithms.SubexponentialSAT.SubexpMainReady

namespace OAI.Algorithms

/-! A real empty-clause branch before the four nonempty-leaf backend calls. -/

namespace SubexponentialSAT.SubexpEmptyClauseGuard

open BitProgram StructuredCalls SubexpMainProgram

variable {er es : ℕ}

def low (es : ℕ) (i : Fin 10) : Fin (totalStacks es) :=
  i.castLE (by dsimp [totalStacks, workStacks]; omega)

def stackMap (es : ℕ) (i : Fin 10) : Fin (totalStacks es) :=
  if i = 9 then persistent es 9 else low es i

theorem stackMap_injective (es : ℕ) : Function.Injective (stackMap es) := by
  intro i j h
  by_cases hi : i = 9 <;> by_cases hj : j = 9
  · exact hi.trans hj.symm
  · subst i
    have hv := congrArg (fun x : Fin (totalStacks es) => x.val) h
    simp [stackMap, hj, persistent, low, workStacks] at hv
    omega
  · subst j
    have hv := congrArg (fun x : Fin (totalStacks es) => x.val) h
    simp [stackMap, hi, persistent, low, workStacks] at hv
    omega
  · have hv := congrArg (fun x : Fin (totalStacks es) => x.val) h
    simp only [stackMap, ite_eq_right hi, ite_eq_right hj, low, Fin.val_castLE] at hv
    exact Fin.ext hv

def procedure (er es : ℕ) : Procedure er es where
  registers := 10
  stackCount := 10
  labels := StructuredCalls.size SubexpEmptyClauseProgram.command + 1
  program := SubexpEmptyClauseProgram.program
  register := ⟨fun i => i.castLE (by simp [workRegs]; omega), by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin (workRegs er) => x.val) h)⟩
  stack := ⟨stackMap es, stackMap_injective es⟩

def flagData (a : MainState er es) (answer : Bool) : MainState er es :=
  ⟨Function.update a.regs (scratchValue er) answer, a.stacks⟩

theorem register_zero_iff (j : Fin 10) :
    (procedure er es).registerMap j = scratchValue er ↔ j = 0 := by
  constructor
  · intro h
    apply Fin.ext
    exact congrArg (fun x : Fin (totalRegs er) => x.val) h
  · rintro rfl
    rfl

theorem install_result (a : MainState er es) (answer : Bool)
    (ha : SubexpMainReady.StorageReady 9 a) :
    (procedure er es).install a
      (SubexpEmptyClauseProgram.result ((procedure er es).project a) answer) = flagData a answer := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    by_cases hi : ∃ j : Fin 10, (procedure er es).registerMap j = i
    · obtain ⟨j, rfl⟩ := hi
      change ((procedure er es).install a
        (SubexpEmptyClauseProgram.result ((procedure er es).project a) answer)).regs
          ((procedure er es).registerMap j) = _
      rw [show ((procedure er es).install a
          (SubexpEmptyClauseProgram.result ((procedure er es).project a) answer)).regs
            ((procedure er es).registerMap j) =
          (SubexpEmptyClauseProgram.result ((procedure er es).project a) answer).regs j from
        embedState_register _ _ _ _ (procedure er es).registerMap_injective j]
      have hz : a.regs ((procedure er es).registerMap j) = false :=
        ha.1 ((procedure er es).register j)
      by_cases hj0 : j = 0
      · subst j
        rfl
      · have hreg : (procedure er es).registerMap j ≠ scratchValue er := by
          exact fun h => hj0 ((register_zero_iff j).mp h)
        simp only [SubexpEmptyClauseProgram.result, Procedure.project ]
        rw [ite_eq_right hj0, Function.update_noteq hreg]
        by_cases hj7 : j.val < 7
        · rw [ite_eq_left hj7]
          exact hz.symm
        · rw [ite_eq_right hj7]
          rfl
    · have hz : i ≠ scratchValue er := by
        intro h
        exact hi ⟨(0 : Fin 10), by simpa only [h] using
          (register_zero_iff (er := er) (es := es) 0).mpr rfl⟩
      change ((procedure er es).install a
        (SubexpEmptyClauseProgram.result ((procedure er es).project a) answer)).regs i = _
      rw [show ((procedure er es).install a
          (SubexpEmptyClauseProgram.result ((procedure er es).project a) answer)).regs i = a.regs i from
        embedState_register_frame _ _ _ _ i hi]
      simp [ hz]
  · exact congrArg StructuredProgram.State.stacks ((procedure er es).install_project a)

theorem scan_eval (records : List (List Bool)) (a : MainState er es)
    (hbody : a.stacks (persistent es 9) = Encoding.encodeList id records)
    (ha : SubexpMainReady.StorageReady 9 a) :
    ∃ t, t ≤ 100 * ((a.stacks (persistent es 9)).length + 1) + 1 ∧
      Eval (procedure er es).invoke t a (flagData a (decide ([false] ∈ records))) := by
  have hr : SubexpEmptyClauseProgram.Ready ((procedure er es).project a) := by
    constructor
    · intro i hi
      change i.val < 5 at hi
      have hi9 : i ≠ (9 : Fin 10) := by
        intro h
        have hv := congrArg (fun x : Fin 10 => x.val) h
        change i.val = 9 at hv
        omega
      change a.stacks (stackMap es i) = []
      rw [stackMap, ite_eq_right hi9]
      exact ha.2 _ (by change i.val < 9; omega)
    · change a.stacks (stackMap es 8) = []
      rw [stackMap, ite_eq_right (by decide)]
      exact ha.2 _ (by change (8 : ℕ) < 9; decide)
  have hs : ((procedure er es).project a).stacks (9 : Fin 10) = Encoding.encodeList id records := by
    change a.stacks (stackMap es 9) = Encoding.encodeList id records
    rw [show stackMap es 9 = persistent es 9 by simp [stackMap]]
    exact hbody
  obtain ⟨t, ht, he⟩ := SubexpEmptyClauseProgram.program_runsIn records
    ((procedure er es).project a) hs hr
  refine ⟨t, ?_, ?_⟩
  · change t ≤ 100 * ((a.stacks (stackMap es 9)).length + 1) + 1 at ht
    rw [show stackMap es 9 = persistent es 9 by simp [stackMap]] at ht
    exact ht
  · have h := (procedure er es).invoke_trace a _ he
    simpa only [install_result a _ ha] using h

def resetFlag (er es : ℕ) : MainCmd er es := atom (.set (scratchValue er) false)

theorem resetFlag_eval (a : MainState er es) (answer : Bool)
    (ha : a.regs (scratchValue er) = false) :
    Eval (resetFlag er es) 1 (flagData a answer) a := by
  have he : Eval (resetFlag er es) 1 (flagData a answer)
      ((StructuredProgram.Atom.set (scratchValue er) false).eval (flagData a answer)) :=
    .base (.atom _ _)
  have hs : (StructuredProgram.Atom.set (scratchValue er) false).eval (flagData a answer) = a := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      by_cases hi : i = scratchValue er
      · subst i
        simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.withPC, StructuredProgram.State.ofCfg,
          execInstr, flagData] using ha.symm
      · simp [ StructuredProgram.Atom.instr,
          execInstr, flagData, hi]
    · rfl
  rw [hs] at he
  exact he

def falseAnswer (er es : ℕ) : MainCmd er es :=
  .seq (clearPort er es (persistent es 10))
    (.seq (atom (.set (scratchValue er) false)) (atom (.push (persistent es 10) (scratchValue er))))

def falseData (a : MainState er es) : MainState er es :=
  ⟨readRegs a.regs (scratchValue er) (scratchPresent er) none,
    Function.update a.stacks (persistent es 10) [false]⟩

theorem falseAnswer_eval (a : MainState er es) :
    Eval (falseAnswer er es) (clearCost (persistent es 10) a + 2) a (falseData a) := by
  have he := (clearPort_eval (persistent es 10) a).seq
    ((Eval.base (StructuredProgram.Eval.atom (.set (scratchValue er) false) _)).seq
      (Eval.base (StructuredProgram.Eval.atom (.push (persistent es 10) (scratchValue er)) _)))
  have hr : Function.update (readRegs a.regs (scratchValue er) (scratchPresent er) none)
      (scratchValue er) false = readRegs a.regs (scratchValue er) (scratchPresent er) none := by
    apply Function.update_eq_self_iff.mpr
    simp [readRegs, scratch_ne er ]
  have hv : readRegs a.regs (scratchValue er) (scratchPresent er) none (scratchValue er) = false := by
    simp [readRegs, scratch_ne er]
  simpa [falseAnswer, SubexpMainProgram.atom, falseData, clearedData, clearCost, StackRoutines.clearStacks,
    StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr,
    hr, hv, Nat.add_assoc] using he

def backend {er es : ℕ} (p : Phases er es) : MainCmd er es :=
  .seq p.layout.invoke (.seq p.moments.invoke (.seq p.crt.invoke
    (.seq p.decode.invoke (finishLeaf er es))))

def accept {er es : ℕ} (p : Phases er es) : MainCmd er es :=
  .seq (resetFlag er es) (backend p)

def reject (er es : ℕ) : MainCmd er es :=
  .seq (resetFlag er es) (.seq (falseAnswer er es) (finishLeaf er es))

def leafCallback {er es : ℕ} (p : Phases er es) : MainCmd er es :=
  .seq (transferLeaf er es) (.seq (procedure er es).invoke
    (.ite (scratchValue er) (reject er es) (accept p)))

theorem backend_eval {p : Phases er es} {a : MainState er es} (run : LeafRun p a) :
    Eval (backend p) (run.layoutSteps + (run.momentSteps +
      (run.crtSteps + (run.decodeSteps + finishCost run.afterDecode))))
      (transferredData a) (finishedData run.afterDecode) :=
  .seq run.layoutTrace (.seq run.momentTrace
    (.seq run.crtTrace (.seq run.decodeTrace (finishLeaf_eval _))))

theorem accept_execution {p : Phases er es} (records : List (List Bool))
    (a : MainState er es) (ha : SubexpMainReady.StorageReady 9 (transferredData a))
    (hbody : (transferredData a).stacks (persistent es 9) = Encoding.encodeList id records)
    (hne : [false] ∉ records) (run : LeafRun p a) :
    ∃ t, t ≤ run.steps + 200 * (((transferredData a).stacks (persistent es 9)).length + 1) ∧
      Eval (leafCallback p) t a (finishedData run.afterDecode) := by
  obtain ⟨t, ht, he⟩ := scan_eval records (transferredData a) hbody ha
  have hscan : Eval (procedure er es).invoke t (transferredData a)
      (flagData (transferredData a) false) := by simpa [hne] using he
  have hr0 : (transferredData a).regs (scratchValue er) = false := ha.1 ⟨0, by simp [workRegs]⟩
  have hb := (resetFlag_eval (transferredData a) false hr0).seq (backend_eval run)
  have hx : (flagData (transferredData a) false).regs (scratchValue er) = false := by simp [flagData]
  have hout := (transferLeaf_eval a).seq
    (hscan.seq (Eval.ite_false (yes := reject er es) hx hb))
  refine ⟨_, ?_, hout⟩
  dsimp only [LeafRun.steps]
  omega

theorem false_finish_cost (a : MainState er es) :
    finishCost (falseData a) = 2 * (a.stacks (persistent es 9)).length + 9 := by
  simp [finishCost, clearCost, poppedAnswer, clearedData, falseData,
    StackRoutines.clearStacks, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, readRegs]
  ; omega

theorem reject_finished_eq (base : MainState er es) (tail bits : List Bool)
    (ha : SubexpMainReady.StorageReady 9 base)
    (h9 : base.stacks (persistent es 9) = [])
    (h10 : base.stacks (persistent es 10) = []) :
    finishedData (falseData (transferredData (leafInput base tail bits))) =
      RecordPrograms.state (ports er es) base false true false tail [] := by
  have hzero : base.regs (scratchValue er) = false := ha.1 ⟨0, by simp [workRegs]⟩
  have hone : base.regs (scratchPresent er) = false := ha.1 ⟨1, by dsimp [workRegs]; omega⟩
  have hvc (i : Fin 3) : scratchValue er ≠ controlRegister er i :=
    (control_ne_scratchValue er i).symm
  have hpc (i : Fin 3) : scratchPresent er ≠ controlRegister er i :=
    (control_ne_scratchPresent er i).symm
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    by_cases h0 : i = scratchValue er
    · subst i
      simp [ falseData, transferredData, leafInput, poppedAnswer, clearedData,
        RecordPrograms.state, ports, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, readRegs,
        hzero, scratch_ne er, hvc]
    by_cases h1 : i = scratchPresent er
    · subst i
      simp [ falseData, transferredData, leafInput, poppedAnswer, clearedData,
        RecordPrograms.state, ports, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, readRegs,
        hone, hpc]
    by_cases h2 : i = controlRegister er 0
    · subst i
      simp [ falseData, transferredData, leafInput, poppedAnswer, clearedData,
        RecordPrograms.state, ports, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, readRegs]
    by_cases h3 : i = controlRegister er 1
    · subst i
      simp [ falseData, transferredData, leafInput, poppedAnswer, clearedData,
        RecordPrograms.state, ports, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, readRegs]
    by_cases h4 : i = controlRegister er 2
    · subst i
      simp [ falseData, transferredData, leafInput, poppedAnswer, clearedData,
        RecordPrograms.state, ports, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, readRegs]
    simp [ falseData, transferredData, leafInput, poppedAnswer, clearedData,
      RecordPrograms.state, ports, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, readRegs,
      h0, h1, h2, h3, h4]
  · funext i
    by_cases h7 : i = persistent es 7
    · subst i
      simp [ falseData, transferredData, leafInput, poppedAnswer, clearedData,
        RecordPrograms.state, ports, StackRoutines.clearStacks, StackRoutines.transferStacks,
        StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]
    by_cases h8 : i = persistent es 8
    · subst i
      simp [ falseData, transferredData, leafInput, poppedAnswer, clearedData,
        RecordPrograms.state, ports, StackRoutines.clearStacks, StackRoutines.transferStacks,
        StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]
    by_cases hi9 : i = persistent es 9
    · subst i
      simp [ falseData, transferredData, leafInput, poppedAnswer, clearedData,
        RecordPrograms.state, ports, StackRoutines.clearStacks, StackRoutines.transferStacks,
        StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, h9]
    by_cases hi10 : i = persistent es 10
    · subst i
      simp [ falseData, transferredData, leafInput, poppedAnswer, clearedData,
        RecordPrograms.state, ports, StackRoutines.clearStacks, StackRoutines.transferStacks,
        StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, h10]
    simp [ falseData, transferredData, leafInput, poppedAnswer, clearedData,
      RecordPrograms.state, ports, StackRoutines.clearStacks, StackRoutines.transferStacks,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr,
      h7, h8, hi9, hi10]

theorem reject_execution {p : Phases er es} (records : List (List Bool))
    (base : MainState er es) (tail : List Bool)
    (ha : SubexpMainReady.StorageReady 9 base)
    (h9 : base.stacks (persistent es 9) = [])
    (h10 : base.stacks (persistent es 10) = []) (hempty : [false] ∈ records) :
    ∃ t, t ≤ 200 * ((Encoding.encodeList id records).length + 1) ∧
      Eval (leafCallback p) t (leafInput base tail (Encoding.encodeList id records))
        (RecordPrograms.state (ports er es) base false true false tail []) := by
  let start := leafInput base tail (Encoding.encodeList id records)
  let a := transferredData start
  have hfit : 9 ≤ workStacks es := by dsimp [workStacks]; omega
  have hra : SubexpMainReady.StorageReady 9 a :=
    SubexpMainReady.transferred_ready 9 hfit start
      (SubexpMainReady.leafInput_ready 9 hfit base tail _ ha)
  have hbody : a.stacks (persistent es 9) = Encoding.encodeList id records :=
    (transfer_leafInput base tail _ h9).1
  obtain ⟨t, ht, he⟩ := scan_eval records a hbody hra
  have hscan : Eval (procedure er es).invoke t a (flagData a true) := by simpa [hempty] using he
  have hz : a.regs (scratchValue er) = false := hra.1 ⟨0, by simp [workRegs]⟩
  have hbranch := (resetFlag_eval a true hz).seq
    ((falseAnswer_eval a).seq (finishLeaf_eval (falseData a)))
  have hflag : (flagData a true).regs (scratchValue er) = true := by simp [flagData]
  have hout := (transferLeaf_eval start).seq
    (hscan.seq (Eval.ite_true (no := accept p) hflag hbranch))
  have hend : finishedData (falseData a) =
      RecordPrograms.state (ports er es) base false true false tail [] :=
    reject_finished_eq base tail _ ha h9 h10
  rw [hend] at hout
  refine ⟨_, ?_, hout⟩
  have htransfer : transferCost start = 3 * (Encoding.encodeList id records).length + 3 := by
    simp [start, transferCost, leafInput, RecordPrograms.state, ports]
  have hclear : clearCost (persistent es 10) a = 3 := by
    simp [a, start, clearCost, transferredData, leafInput, RecordPrograms.state,
      ports, StackRoutines.transferStacks, h10]
  have hfinish := false_finish_cost a
  rw [hbody] at ht hfinish
  omega

/-- A semantic description of the bytes on which the real scanner returns
true. This predicate is not used as an instruction. -/
def HasEmpty (bits : List Bool) : Prop :=
  ∃ records : List (List Bool), bits = Encoding.encodeList id records ∧ [false] ∈ records

theorem hasEmpty_records (records : List (List Bool)) :
    HasEmpty (Encoding.encodeList id records) ↔ [false] ∈ records := by
  constructor
  · rintro ⟨other, he, hm⟩
    have ho : records = other := Encoding.encodeList_injective Function.injective_id he
    exact ho.symm ▸ hm
  · intro hm
    exact ⟨records, rfl, hm⟩

theorem hasEmpty_encoded {α : Type*} (encode : α → List Bool) (F : List (List α)) :
    HasEmpty (Encoding.encodeList (Encoding.encodeList encode) F) ↔ [] ∈ F := by
  have he := ExecSparsifyEncoding.encodeList_map (Encoding.encodeList encode) id F
  change Encoding.encodeList id (F.map (Encoding.encodeList encode)) =
    Encoding.encodeList (Encoding.encodeList encode) F at he
  rw [← he, hasEmpty_records, SubexpEmptyClauseProgram.empty_record_iff]

theorem hasEmpty_raw_iff {n : ℕ} (F : List (List (SAT.Literal (Fin n)))) :
    HasEmpty (ExecQuantitativeSparsify.encodeRawFormula F) ↔ [] ∈ F := by
  rw [← ExecSparsifyEncoding.words_encodeRawFormula, hasEmpty_encoded]
  simp [ExecSparsifyEncoding.words]

theorem hasEmpty_raw_unsatisfiable {n : ℕ} (F : List (List (SAT.Literal (Fin n))))
    (h : HasEmpty (ExecQuantitativeSparsify.encodeRawFormula F)) :
    ¬ SAT.Satisfiable (ExecCNF.formulaSet F) :=
  SubexpEmptyClauseProgram.empty_unsatisfiable F ((hasEmpty_raw_iff F).mp h)

theorem callback_contract {p : Phases er es} (test : List Bool → Bool)
    (cost : List Bool → ℕ) (invariant : MainState er es → Prop)
    (validPayload : List Bool → Prop)
    (encoded : ∀ bits, validPayload bits → ∃ records : List (List Bool), bits = Encoding.encodeList id records)
    (ready : ∀ base, invariant base → SubexpMainReady.StorageReady 9 base ∧
      base.stacks (persistent es 9) = [] ∧ base.stacks (persistent es 10) = [])
    (empty_answer : ∀ bits, validPayload bits → HasEmpty bits → test bits = false)
    (nonempty : LeafContract p test cost invariant (fun bits => validPayload bits ∧ ¬ HasEmpty bits)) :
    RecordPrograms.CallbackContractOn (ports er es) (leafCallback p) test
      (fun bits => cost bits + 200 * (bits.length + 1)) invariant validPayload := by
  intro bits tail base hv hi
  obtain ⟨records, rfl⟩ := encoded bits hv
  obtain ⟨hr, h9, h10⟩ := ready base hi
  by_cases hempty : [false] ∈ records
  · obtain ⟨t, ht, he⟩ := reject_execution (p := p) records base tail hr h9 h10 hempty
    have hans := empty_answer _ hv ⟨records, rfl, hempty⟩
    refine ⟨t, base, ?_, hi, ?_⟩
    · change t ≤ cost (Encoding.encodeList id records) + 200 * ((Encoding.encodeList id records).length + 1)
      omega
    simpa only [hans, leafInput] using he
  · have hnot : ¬ HasEmpty (Encoding.encodeList id records) := by
      rintro ⟨other, heq, hm⟩
      have ho : records = other := Encoding.encodeList_injective Function.injective_id heq
      exact hempty (ho.symm ▸ hm)
    obtain ⟨run, hcost, hnext, hs, hp, hout⟩ := nonempty _ tail base ⟨hv, hnot⟩ hi
    have hfit : 9 ≤ workStacks es := by dsimp [workStacks]; omega
    have hrstart := SubexpMainReady.transferred_ready 9 hfit
      (leafInput base tail (Encoding.encodeList id records))
      (SubexpMainReady.leafInput_ready 9 hfit base tail (Encoding.encodeList id records) hr)
    have hbody := (transfer_leafInput base tail (Encoding.encodeList id records) h9).1
    obtain ⟨t, ht, he⟩ := accept_execution records _ hrstart hbody hempty run
    rw [hbody] at ht
    refine ⟨t, finishedData run.afterDecode, ?_, hnext, ?_⟩
    · change t ≤ cost (Encoding.encodeList id records) + 200 * ((Encoding.encodeList id records).length + 1)
      omega
    rw [finished_record_state run.afterDecode tail (test _) hs hp hout] at he
    exact he

end SubexponentialSAT.SubexpEmptyClauseGuard

end OAI.Algorithms
