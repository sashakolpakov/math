import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafAssignmentRegisterFrameBase
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactor

namespace OAI.Algorithms

/-! Every actual assignment-callback execution preserves the wide moment
assembler's registers 16--39, independently of all tape contents and flags. -/
namespace SubexponentialSAT.SqrtLog.LeafAssignmentRegisterFrame
open SubexponentialSAT BitProgram StructuredCalls
open MomentsAssembly.RegisterFrame
open LeafProgram

theorem setupMove (src dst : Fin 768) (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves (LeafAssignmentSetupProgram.move src dst) i := by
  unfold LeafAssignmentSetupProgram.move
  exact fun {n} {a} {b} => seq (MomentsAssembly.RegisterFrame.transfer src 359 i hi)
    (MomentsAssembly.RegisterFrame.transfer 359 dst i hi)

theorem setupBefore (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves LeafAssignmentSetupProgram.beforeCommand i := by
  unfold LeafAssignmentSetupProgram.beforeCommand
  have hm : Preserves LeafAssignmentSetupProgram.mergeCommand i := by
    unfold LeafAssignmentSetupProgram.mergeCommand
    apply lowLift (i := i) <;> try exact hi
    intro j
    change j.val < 16
    omega
  have hw : Preserves LeafAssignmentSetupProgram.weightCommand i := by
    unfold LeafAssignmentSetupProgram.weightCommand
    apply lowLift (i := i) <;> try exact hi
    intro j
    change j.val < 16
    omega
  exact fun {n} {a} {b} => seq (setupMove 40 146 i hi) (seq (setupMove 42 147 i hi) (seq hm hw))

theorem setupAfter (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves LeafAssignmentSetupProgram.afterCommand i := by
  unfold LeafAssignmentSetupProgram.afterCommand
  exact fun {n} {a} {b} => seq (MomentsAssembly.RegisterFrame.clear 40 i hi)
    (seq (MomentsAssembly.RegisterFrame.clear 42 i hi)
      (seq (setupMove 67 41 i hi) (seq (setupMove 146 40 i hi)
        (seq (setupMove 147 42 i hi) (seq (setupMove 148 44 i hi)
          (seq (MomentsAssembly.RegisterFrame.clear 145 i hi)
            (MomentsAssembly.RegisterFrame.clear 174 i hi)))))))

theorem factorMove (src dst : Fin 768) (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves (Factor.move src dst) i := by
  unfold Factor.move
  exact fun {n} {a} {b} => seq (LeafAssignmentRegisterFrame.copy src dst 159 i hi)
    (MomentsAssembly.RegisterFrame.clear src i hi)

theorem factorID (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves FactorID.command i := by
  unfold FactorID.command
  exact fun {n} {a} {b} => seq (LeafAssignmentRegisterFrame.copy 149 556 359 i hi)
    (pop 556 0 1 i hi (by decide) (by decide))

theorem dispatch (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves FactorDispatch.command i := by
  unfold FactorDispatch.command
  have hd : Preserves FactorDispatch.dispatch i := by
    unfold FactorDispatch.dispatch
    apply lowLift (i := i) <;> try exact hi
    intro j
    change j.val < 16
    omega
  exact fun {n} {a} {b} => seq (seq (LeafAssignmentRegisterFrame.copy 149 152 359 i hi)
    (LeafAssignmentRegisterFrame.peek 706 7 0 i hi (by decide) (by decide))) hd

theorem incidence (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves Incidence.caller i := by
  unfold Incidence.caller
  apply lowLift (i := i) <;> try exact hi
  intro j
  exact j.isLt

theorem expansion (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves Expansion.forwardCommand i := by
  unfold Expansion.forwardCommand
  have he : Preserves Expansion.command i := by
    unfold Expansion.command
    apply lowLift (i := i) <;> try exact hi
    intro j
    change j.val < 16
    omega
  exact fun {n} {a} {b} => seq (reverse 154 358 359 i hi) he

theorem clause (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves Clause.caller i := by
  unfold Clause.caller
  apply lowLift (i := i) <;> try exact hi
  intro j
  change j.val < 16
  omega

theorem indicator (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves Factor.indicator i := by
  unfold Factor.indicator
  have hr : Preserves Factor.indicatorReady i :=
    by
      unfold Factor.indicatorReady
      exact fun {n} {a} {b} => seq (setReg 0 i false hi (by decide))
        (seq (setReg 1 i true hi (by decide)) (setReg 2 i false hi (by decide)))
  apply seq hr
  apply lowLift (i := i) <;> try exact hi
  intro j
  change j.val < 16
  omega

theorem multiply (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves Factor.multiply i := by
  unfold Factor.multiply
  apply lowLift (i := i) <;> try exact hi
  intro j
  change j.val < 16
  omega

theorem accumulate (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves Factor.accumulate i := by
  unfold Factor.accumulate
  exact fun {n} {a} {b} => seq (factorMove 67 61 i hi)
    (seq (factorMove 151 67 i hi) (seq (multiply i hi) (factorMove 67 151 i hi)))

theorem prepareIncidence (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves Factor.prepareIncidence i := by
  unfold Factor.prepareIncidence
  exact fun {n} {a} {b} => seq (factorID i hi) (incidence i hi)

theorem hashFactor (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves Factor.hashFactor i := by
  unfold Factor.hashFactor
  exact fun {n} {a} {b} => seq (prepareIncidence i hi) (seq (expansion i hi)
    (seq (indicator i hi) (seq (MomentsAssembly.RegisterFrame.clear 68 i hi)
      (seq (MomentsAssembly.RegisterFrame.clear 62 i hi) (accumulate i hi)))))

theorem markedFactor (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves Factor.markedFactor i := by
  unfold Factor.markedFactor
  exact fun {n} {a} {b} => seq (prepareIncidence i hi) (seq (factorMove 154 63 i hi)
    (seq (clause i hi) (seq (MomentsAssembly.RegisterFrame.clear 62 i hi) (accumulate i hi))))

theorem choose (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves Factor.choose i := by
  unfold Factor.choose
  exact fun {n} {a} {b} => branch 5 i (hashFactor i hi) (branch 6 i (markedFactor i hi) (skip i))

theorem returnToRecords (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves Factor.returnToRecords i := by
  unfold Factor.returnToRecords
  exact fun {n} {a} {b} => seq (setReg 13 i false hi (by decide))
    (seq (setReg 14 i true hi (by decide)) (setReg 15 i false hi (by decide)))

theorem callback (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves Factor.callback i := by
  unfold Factor.callback
  exact fun {n} {a} {b} => seq (dispatch i hi) (seq (choose i hi)
    (seq (MomentsAssembly.RegisterFrame.clear 149 i hi) (returnToRecords i hi)))

theorem factorLoop (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves Factor.loop i := by
  unfold Factor.loop
  exact fun {n} {a} {b} => records Factor.ports Factor.callback (by decide) (by decide) (by decide) i hi (callback i hi)

theorem command (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves Factor.command i := by
  unfold Factor.command
  exact fun {n} {a} {b} => seq (LeafAssignmentRegisterFrame.copy 175 150 159 i hi)
    (seq (LeafAssignmentRegisterFrame.copy 69 151 159 i hi)
      (seq (factorLoop i hi) (factorMove 151 67 i hi)))

/-- Universal structural preservation: the only premise of an application is
an actual execution of the concrete assignment command. -/
theorem assignment (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves Factor.assignment i := by
  unfold Factor.assignment
  exact fun {n} {a} {b} => seq (setupBefore i hi) (seq (command i hi) (setupAfter i hi))

theorem assignment_eval_register {n : ℕ} {a b : Data}
    (h : Eval Factor.assignment n a b) (i : Fin 40) (hi : 16 ≤ i.val) :
    b.regs i = a.regs i := assignment i hi h

end SubexponentialSAT.SqrtLog.LeafAssignmentRegisterFrame

end OAI.Algorithms
