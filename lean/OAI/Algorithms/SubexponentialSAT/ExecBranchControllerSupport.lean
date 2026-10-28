import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram
import OAI.Algorithms.SubexponentialSAT.ExecWorklistProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Actual copying, child calls, and framed output for the two-child controller.
Ports 0--6 hold pending work, leaves, both outputs, parent, core, and selection.
Ports 7--22 are a reusable 16-stack child workspace. -/

namespace SubexponentialSAT.ExecBranchControllerSupport

open BitProgram StructuredCalls


abbrev Regs := Fin 15 → Bool
abbrev Front := Fin 7 → List Bool
abbrev Bank := Fin 16 → List Bool
abbrev Data := State 15 23

def frontPort (i : Fin 7) : Fin 23 := Fin.castAdd 16 i
def bankPort (i : Fin 16) : Fin 23 := Fin.natAdd 7 i

@[simp] theorem frontPort_inj {i j : Fin 7} : frontPort i = frontPort j ↔ i = j :=
  Fin.castAdd_inj
@[simp] theorem bankPort_inj {i j : Fin 16} : bankPort i = bankPort j ↔ i = j := by
  simp [bankPort, Fin.ext_iff]

theorem bankPort_injective : Function.Injective bankPort := fun _ _ h => bankPort_inj.mp h

@[simp] theorem front_ne_bank (i : Fin 7) (j : Fin 16) : frontPort i ≠ bankPort j := by
  intro h
  have he := congrArg Fin.val h
  change i.val = 7 + j.val at he
  omega

@[simp] theorem bank_ne_front (i : Fin 16) (j : Fin 7) : bankPort i ≠ frontPort j :=
  (front_ne_bank j i).symm

def state (regs : Regs) (front : Front) (bank : Bank) : Data :=
  ⟨regs, Fin.addCases (m := 7) (n := 16) (motive := fun _ => List Bool) front bank⟩

@[simp] theorem state_regs (regs : Regs) (front : Front) (bank : Bank) :
    (state regs front bank).regs = regs := rfl

theorem state_stacks (regs regs' : Regs) (front : Front) (bank : Bank) :
    (state regs front bank).stacks = (state regs' front bank).stacks := rfl

def emptyBank : Bank := fun _ => []
def idle (regs : Regs) (front : Front) : Data := state regs front emptyBank
def wordBank (port : Fin 16) (bits : List Bool) : Bank := Function.update emptyBank port bits

@[simp] theorem state_front (regs : Regs) (front : Front) (bank : Bank) (i : Fin 7) :
    (state regs front bank).stacks (frontPort i) = front i := by
  simp [state, frontPort]

@[simp] theorem state_bank (regs : Regs) (front : Front) (bank : Bank) (i : Fin 16) :
    (state regs front bank).stacks (bankPort i) = bank i := by
  simp [state, bankPort]

theorem state_update_bank (regs : Regs) (front : Front) (bank : Bank)
    (i : Fin 16) (bits : List Bool) :
    state regs front (Function.update bank i bits) =
      ⟨regs, Function.update (state regs front bank).stacks (bankPort i) bits⟩ := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext j
  refine Fin.addCases (m := 7) (n := 16) (fun k => ?_) (fun k => ?_) j
  · change (state regs front (Function.update bank i bits)).stacks (frontPort k) =
      Function.update (state regs front bank).stacks (bankPort i) bits (frontPort k)
    simp
  · change (state regs front (Function.update bank i bits)).stacks (bankPort k) =
      Function.update (state regs front bank).stacks (bankPort i) bits (bankPort k)
    simp [Function.update_apply]

theorem state_update_front (regs : Regs) (front : Front) (bank : Bank)
    (i : Fin 7) (bits : List Bool) :
    state regs (Function.update front i bits) bank =
      ⟨regs, Function.update (state regs front bank).stacks (frontPort i) bits⟩ := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext j
  refine Fin.addCases (m := 7) (n := 16) (fun k => ?_) (fun k => ?_) j
  · change (state regs (Function.update front i bits) bank).stacks (frontPort k) =
      Function.update (state regs front bank).stacks (frontPort i) bits (frontPort k)
    simp [Function.update_apply]
  · change (state regs (Function.update front i bits) bank).stacks (bankPort k) =
      Function.update (state regs front bank).stacks (frontPort i) bits (bankPort k)
    simp []

def reset (regs : Regs) : Regs := readRegs regs 0 1 none

@[simp] theorem reset_reset (regs : Regs) : reset (reset regs) = reset regs :=
  StackRoutines.readRegs_reset _ _ _ _

abbrev copyInto (src : Fin 7) (dst tmp : Fin 16) : Cmd 15 23 :=
  .call (StackRoutines.copyProgram (frontPort src) (bankPort dst) (bankPort tmp) 0 1)

theorem copyInto_eval (src : Fin 7) (dst tmp : Fin 16) (regs : Regs)
    (front : Front) (bank : Bank) (hne : tmp ≠ dst)
    (hdst : bank dst = []) (htmp : bank tmp = []) :
    Eval (copyInto src dst tmp) (7 * (front src).length + 5)
      (state regs front bank)
      (state (reset regs) front (Function.update bank dst (front src))) := by
  have h := ListRegisterProgram.copy_run (frontPort src) (bankPort dst) (bankPort tmp)
    (0 : Fin 15) 1 (front_ne_bank _ _) (front_ne_bank _ _)
    (fun h => hne (bankPort_inj.mp h)) (by decide)
    regs (state regs front bank).stacks (by simpa using htmp)
  rw [state_update_bank]
  apply Eval.call
  simpa [ListRegisterProgram.Run, StructuredProgram.State.withPC,
    StackRoutines.copyStacks, hdst, reset, state_front, state_bank,
    state_stacks regs (reset regs)] using h

abbrev load : Cmd 15 23 :=
  .seq (copyInto 5 9 0) (.seq (copyInto 6 12 0) (copyInto 4 13 0))

def loadCost (front : Front) : ℕ :=
  7 * ((front 4).length + (front 5).length + (front 6).length) + 15

def loaded (regs : Regs) (front : Front) : State 15 16 :=
  ExecClauseFiltersProgram.state regs (front 5) [] (front 6) (front 4) [] []

theorem load_eval (regs : Regs) (front : Front) :
    Eval load (loadCost front) (idle regs front)
      (state (reset regs) front (loaded (reset regs) front).stacks) := by
  let b1 : Bank := Function.update emptyBank 9 (front 5)
  let b2 : Bank := Function.update b1 12 (front 6)
  let b3 : Bank := Function.update b2 13 (front 4)
  have h1 := copyInto_eval 5 9 0 regs front emptyBank (by decide) rfl rfl
  have h2 := copyInto_eval 6 12 0 (reset regs) front b1 (by decide)
    (by simp [b1, emptyBank]) (by simp [b1, emptyBank])
  have h3 := copyInto_eval 4 13 0 (reset (reset regs)) front b2 (by decide)
    (by simp [b2, b1, emptyBank]) (by simp [b2, b1, emptyBank])
  have hb : b3 = (loaded (reset regs) front).stacks := by
    funext i
    fin_cases i <;> simp [b3, b2, b1, emptyBank, loaded, ExecClauseFiltersProgram.state]
  have h := h1.seq (h2.seq h3)
  change Eval load _ (idle regs front) (state _ front b3) at h
  rw [hb, reset_reset, reset_reset] at h
  convert h using 1
  unfold loadCost
  omega

theorem embed_child (frameRegs : Regs) (front : Front) (frameBank : Bank)
    (child : State 15 16) :
    embedState id bankPort (state frameRegs front frameBank) child =
      state child.regs front child.stacks := by
  apply embedState_eq_of_ports id bankPort _ _ _ Function.injective_id bankPort_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i; simp
  · intro i
    refine Fin.addCases (m := 7) (n := 16) (fun j hi => ?_) (fun j hi => ?_) i
    · exact (state_front child.regs front child.stacks j).trans
        (state_front frameRegs front frameBank j).symm
    · exact (hi ⟨j, rfl⟩).elim

abbrev callChild {l : ℕ} (p : Program 15 16 l) : Cmd 15 23 :=
  .call (ProgramLinking.liftProgram p id bankPort)

theorem callChild_eval {l : ℕ} (p : Program 15 16 l) (front : Front)
    {n : ℕ} {a b : State 15 16}
    (h : Trace p n (a.withPC (some p.entry)) (b.withPC none)) :
    Eval (callChild p) n (state a.regs front a.stacks) (state b.regs front b.stacks) := by
  have he := eval_call_lifted p id bankPort (state a.regs front a.stacks)
    Function.injective_id bankPort_injective h
  simpa only [embed_child, callChild] using he

def outputPort (i : Fin 2) : Fin 7 := ⟨2 + i.val, by omega⟩

@[simp] theorem outputPort_ne_zero (i : Fin 2) : outputPort i ≠ 0 := by
  intro h
  have he := congrArg Fin.val h
  change 2 + i.val = 0 at he
  omega
@[simp] theorem outputPort_ne_one (i : Fin 2) : outputPort i ≠ 1 := by
  intro h
  have he := congrArg Fin.val h
  change 2 + i.val = 1 at he
  omega

def emitReg (i : Fin 3) : Fin 15 := Fin.castAdd 12 i
def emitPort (i : Fin 2) : Fin 4 → Fin 23 :=
  ![frontPort 0, frontPort 1, frontPort (outputPort i), bankPort 0]

theorem emitReg_injective : Function.Injective emitReg := Fin.castAdd_injective 3 12
theorem emitPort_injective (i : Fin 2) : Function.Injective (emitPort i) := by
  fin_cases i <;> decide

abbrev emitInto (i : Fin 2) : Cmd 15 23 :=
  .call (ProgramLinking.liftProgram SubexpNormalizeProgram.emitRecordProgram emitReg (emitPort i))

def emittedRegs (regs : Regs) : Regs := Function.update (Function.update regs 0 true) 1 false

def emitAfter (i : Fin 2) (bits : List Bool) (d : Data) : Data :=
  ⟨emittedRegs d.regs, Function.update (Function.update d.stacks (bankPort 0) [])
    (frontPort (outputPort i)) (ExecWorklistProgram.record bits ++ d.stacks (frontPort (outputPort i)))⟩

theorem emitInto_eval (i : Fin 2) (bits : List Bool) (d : Data)
    (hpayload : d.stacks (bankPort 0) = bits.reverse) :
    Eval (emitInto i) (5 * bits.length + 7) d (emitAfter i bits d) := by
  let a := SubexpNormalizeProgram.filterState (d.regs 0) (d.regs 1) (d.regs 2)
    (d.stacks (frontPort 0)) (d.stacks (frontPort 1))
    (d.stacks (frontPort (outputPort i))) bits.reverse
  let b := SubexpNormalizeProgram.filterState true false (d.regs 2)
    (d.stacks (frontPort 0)) (d.stacks (frontPort 1))
    (ExecWorklistProgram.record bits ++ d.stacks (frontPort (outputPort i))) []
  have ha : embedState emitReg (emitPort i) d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ emitReg_injective (emitPort_injective i)
    · intro j; fin_cases j <;> rfl
    · intro j hj; rfl
    · intro j; fin_cases j <;> simp [a, emitPort, SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.quadruple, hpayload]
    · intro j hj; rfl
  have hb : embedState emitReg (emitPort i) d b = emitAfter i bits d := by
    apply embedState_eq_of_ports _ _ _ _ _ emitReg_injective (emitPort_injective i)
    · intro j
      fin_cases j <;> simp [b, emitReg, emitAfter, emittedRegs, SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.triple]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, h.symm⟩
      simp [emitAfter, emittedRegs, h0, h1]
    · intro j
      fin_cases j <;> simp [b, emitPort, emitAfter, SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.quadruple, Ne.symm (outputPort_ne_zero i), Ne.symm (outputPort_ne_one i)]
    · intro j hj
      have ho : j ≠ frontPort (outputPort i) := fun h => hj ⟨2, h.symm⟩
      have hp : j ≠ bankPort 0 := fun h => hj ⟨3, h.symm⟩
      simp [emitAfter, ho, hp]
  have ht := SubexpNormalizeProgram.emitRecord_trace bits
    (d.stacks (frontPort 0)) (d.stacks (frontPort 1))
    (d.stacks (frontPort (outputPort i))) (d.regs 0) (d.regs 1) (d.regs 2)
  have he := eval_call_lifted SubexpNormalizeProgram.emitRecordProgram emitReg (emitPort i) d
    emitReg_injective (emitPort_injective i) ht
  change Eval (emitInto i) _ (embedState emitReg (emitPort i) d a)
    (embedState emitReg (emitPort i) d b) at he
  simpa only [ha, hb] using he

abbrev toPayload : Cmd 15 23 :=
  .call (StackRoutines.transferProgram (bankPort 13) (bankPort 0) 0 1)

theorem toPayload_eval (regs : Regs) (front : Front) (bits : List Bool) :
    Eval toPayload (3 * bits.length + 3)
      (state regs front (wordBank 13 bits))
      (state (reset regs) front (wordBank 0 bits.reverse)) := by
  let d := state regs front (wordBank 13 bits)
  have hs : StackRoutines.transferStacks (bankPort 13) (bankPort 0) d.stacks =
      (state (reset regs) front (wordBank 0 bits.reverse)).stacks := by
    funext j
    refine Fin.addCases (m := 7) (n := 16) (fun k => ?_) (fun k => ?_) j
    · change StackRoutines.transferStacks (bankPort 13) (bankPort 0) d.stacks (frontPort k) =
        (state (reset regs) front (wordBank 0 bits.reverse)).stacks (frontPort k)
      simp [StackRoutines.transferStacks, d, wordBank, emptyBank]
    · change StackRoutines.transferStacks (bankPort 13) (bankPort 0) d.stacks (bankPort k) =
        (state (reset regs) front (wordBank 0 bits.reverse)).stacks (bankPort k)
      fin_cases k <;> simp [StackRoutines.transferStacks, d, wordBank, emptyBank]
  have h := ListRegisterProgram.transfer_run (bankPort 13) (bankPort 0) (0 : Fin 15) 1
    (by decide) (by decide) regs d.stacks
  rw [state_bank] at h
  rw [hs] at h
  apply Eval.call
  simpa [ListRegisterProgram.Run, StructuredProgram.State.withPC, d, wordBank,
    emptyBank, reset, state_regs] using h

abbrev frameChild (i : Fin 2) : Cmd 15 23 := .seq toPayload (emitInto i)

theorem frameChild_eval (i : Fin 2) (regs : Regs) (front : Front) (bits : List Bool) :
    Eval (frameChild i) (8 * bits.length + 10)
      (state regs front (wordBank 13 bits))
      (idle (emittedRegs (reset regs)) (Function.update front (outputPort i)
        (ExecWorklistProgram.record bits ++ front (outputPort i)))) := by
  let d := state (reset regs) front (wordBank 0 bits.reverse)
  have he := emitInto_eval i bits d (by simp [d, wordBank])
  have hfinal : emitAfter i bits d =
      idle (emittedRegs (reset regs)) (Function.update front (outputPort i)
        (ExecWorklistProgram.record bits ++ front (outputPort i))) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    refine Fin.addCases (m := 7) (n := 16) (fun k => ?_) (fun k => ?_) j
    · change (emitAfter i bits d).stacks (frontPort k) =
        (idle (emittedRegs (reset regs)) (Function.update front (outputPort i)
          (ExecWorklistProgram.record bits ++ front (outputPort i)))).stacks (frontPort k)
      simp [emitAfter, d, idle, Function.update_apply]
    · change (emitAfter i bits d).stacks (bankPort k) =
        (idle (emittedRegs (reset regs)) (Function.update front (outputPort i)
          (ExecWorklistProgram.record bits ++ front (outputPort i)))).stacks (bankPort k)
      by_cases hk : k = 0 <;> simp [emitAfter, d, idle, wordBank, emptyBank, hk]
  rw [hfinal] at he
  have h := (toPayload_eval regs front bits).seq he
  convert h using 1
  omega

abbrev buildChild {l : ℕ} (p : Program 15 16 l) (i : Fin 2) : Cmd 15 23 :=
  .seq load (.seq (callChild p) (frameChild i))

/-- Compose a measured execution of a concrete child table with the actual
input copies and frame writer. This lemma only links real instruction traces. -/
theorem buildChild_eval {l : ℕ} (p : Program 15 16 l) (i : Fin 2)
    (regs : Regs) (front : Front) (bits : List Bool) (rf : Regs) {n : ℕ}
    (h : Trace p n ((loaded (reset regs) front).withPC (some p.entry))
      ((ExecClauseFiltersProgram.state rf [] [] [] bits [] []).withPC none)) :
    Eval (buildChild p i) (loadCost front + (n + (8 * bits.length + 10)))
      (idle regs front)
      (idle (emittedRegs (reset rf)) (Function.update front (outputPort i)
        (ExecWorklistProgram.record bits ++ front (outputPort i)))) := by
  have hc := callChild_eval p front h
  have hbank : (ExecClauseFiltersProgram.state rf [] [] [] bits [] []).stacks =
      wordBank 13 bits := by
    funext j
    fin_cases j <;> simp [ExecClauseFiltersProgram.state, wordBank, emptyBank]
  rw [hbank] at hc
  exact (load_eval regs front).seq (hc.seq (frameChild_eval i rf front bits))

abbrev clearFront (i : Fin 7) : Cmd 15 23 :=
  .call (StackRoutines.clearProgram (frontPort i) 0 1)

theorem clearFront_eval (i : Fin 7) (regs : Regs) (front : Front) :
    Eval (clearFront i) (2 * (front i).length + 3) (idle regs front)
      (idle (reset regs) (Function.update front i [])) := by
  have h := ListRegisterProgram.clear_run (frontPort i) (0 : Fin 15) 1 regs (idle regs front).stacks
  rw [show (idle regs front).stacks (frontPort i) = front i by simp [idle]] at h
  change Eval _ _ _ (state (reset regs) (Function.update front i []) emptyBank)
  rw [state_update_front]
  apply Eval.call
  simpa [ListRegisterProgram.Run, StructuredProgram.State.withPC, StackRoutines.clearStacks,
    reset, idle, state_regs, state_stacks regs (reset regs)] using h

abbrev cleanInputs : Cmd 15 23 := .seq (clearFront 4) (.seq (clearFront 5) (clearFront 6))
def cleanFront (front : Front) : Front :=
  Function.update (Function.update (Function.update front 4 []) 5 []) 6 []

theorem cleanInputs_eval (regs : Regs) (front : Front) :
    Eval cleanInputs (2 * ((front 4).length + (front 5).length + (front 6).length) + 9)
      (idle regs front) (idle (reset regs) (cleanFront front)) := by
  have h1 := clearFront_eval 4 regs front
  have h2 := clearFront_eval 5 (reset regs) (Function.update front 4 [])
  have h3 := clearFront_eval 6 (reset (reset regs)) (Function.update (Function.update front 4 []) 5 [])
  have h := h1.seq (h2.seq h3)
  simp only [Function.update_of_ne (by decide : (5 : Fin 7) ≠ 4),
    Function.update_of_ne (by decide : (6 : Fin 7) ≠ 5),
    Function.update_of_ne (by decide : (6 : Fin 7) ≠ 4), reset_reset] at h
  convert h using 1
  · omega
  · rfl

end SubexponentialSAT.ExecBranchControllerSupport

end OAI.Algorithms
