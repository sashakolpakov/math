import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCandidateFinalize
import OAI.Algorithms.SubexponentialSAT.SubexpClauseRowProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-!
# Finish a materialized local candidate with an actual clause evaluation

The input is a packed bit array, a unary declared-variable count, the accumulated
label-validity bit, and a preserved encoded clause. The program checks trailing
padding, evaluates the clause by actual indexed reads, combines the two results,
and clears the working assignment. No semantic predicate is an instruction.
-/

namespace SubexponentialSAT.SubexpCandidateRowProgram

open BitProgram StructuredCalls StackRoutines

abbrev Data := State 4 13

def zeroRegs : Fin 4 → Bool := fun _ => false

def tapes (assignment array width clause prior valid master : List Bool) : Fin 13 → List Bool :=
  ![assignment, array, [], width, [], [], [], [], clause, [], prior, valid, master]

private theorem tapes_eq (assignment array width clause prior valid master : List Bool) :
    tapes assignment array width clause prior valid master = fun i =>
      if i = 0 then assignment else if i = 1 then array else
      if i = 3 then width else if i = 8 then clause else
      if i = 10 then prior else if i = 11 then valid else
      if i = 12 then master else [] := by
  funext i
  fin_cases i <;> rfl

def data (assignment array width clause prior valid master : List Bool) : Data :=
  ⟨zeroRegs, tapes assignment array width clause prior valid master⟩

private theorem state_ext {r s : ℕ} {a b : State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; simp_all

private theorem read_zero : readRegs zeroRegs (0 : Fin 4) 1 none = zeroRegs := by
  funext i; fin_cases i <;> simp [readRegs, zeroRegs]

def finalizeRegisters : Fin 3 → Fin 4 := Fin.castAdd 1

def finalizeStacks : Fin 10 → Fin 13 := ![8, 0, 10, 3, 4, 5, 6, 7, 1, 11]

theorem finalizeRegisters_injective : Function.Injective finalizeRegisters := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 4 => x.val) h)

theorem finalizeStacks_injective : Function.Injective finalizeStacks := by decide

private theorem embed_finalize (assignment array width prior valid master : List Bool)
    (oldAssignment oldArray oldWidth oldPrior oldValid : List Bool) :
    embedState finalizeRegisters finalizeStacks
      (data oldAssignment oldArray oldWidth [] oldPrior oldValid master)
      (SubexpCandidateMaterializer.state [] assignment prior width [] [] [] [] array valid) =
        data assignment array width [] prior valid master := by
  apply embedState_eq_of_ports _ _ _ _ _ finalizeRegisters_injective finalizeStacks_injective
  · intro i; rfl
  · intro i hi; rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨1, h.symm⟩
    have h1 : i ≠ 1 := fun h => hi ⟨8, h.symm⟩
    have h3 : i ≠ 3 := fun h => hi ⟨3, h.symm⟩
    have h10 : i ≠ 10 := fun h => hi ⟨2, h.symm⟩
    have h11 : i ≠ 11 := fun h => hi ⟨9, h.symm⟩
    change tapes assignment array width [] prior valid master i =
      tapes oldAssignment oldArray oldWidth [] oldPrior oldValid master i
    simp only [tapes_eq, h0, h1, h3, h10, h11, ite_false]

abbrev finalize : Cmd 4 13 := .call
  (ProgramLinking.liftProgram SubexpCandidateFinalize.program finalizeRegisters finalizeStacks)

theorem finalize_eval (assignment padding width master : List Bool) (prior : Bool)
    (hw : width.length = assignment.length) :
    Eval finalize (SubexpCandidateFinalize.workCost assignment.length padding.length + 1)
      (data [] (assignment ++ padding) width [] [prior] [] master)
      (data assignment [] width [] [] [prior && SubexpFactorProgram.allZero padding] master) := by
  have h := SubexpCandidateFinalize.lifted_eval finalizeRegisters finalizeStacks
    finalizeRegisters_injective finalizeStacks_injective
    (data [] (assignment ++ padding) width [] [prior] [] master)
    assignment padding width prior hw
  simpa only [SubexpCandidateMaterializer.inputState,
    SubexpCandidateMaterializer.outputState, embed_finalize] using h

private theorem clear_eval (source : Fin 13) (stk : Fin 13 → List Bool) :
    Eval (.call (clearProgram source (0 : Fin 4) 1)) (2 * (stk source).length + 3)
      ⟨zeroRegs, stk⟩ ⟨zeroRegs, clearStacks source stk⟩ := by
  have h := halt_after_trace _ (clearProgram_trace source (0 : Fin 4) 1 zeroRegs stk) 2 rfl rfl
  apply Eval.call
  simpa [StructuredProgram.State.withPC, clearResult, clearProgram, Nat.add_assoc, read_zero] using h

abbrev clearWidth : Cmd 4 13 := .call (clearProgram 3 0 1)

theorem clearWidth_eval (assignment width valid master : List Bool) :
    Eval clearWidth (2 * width.length + 3)
      (data assignment [] width [] [] valid master)
      (data assignment [] [] [] [] valid master) := by
  have h := clear_eval 3 (tapes assignment [] width [] [] valid master)
  have he : clearStacks (3 : Fin 13) (tapes assignment [] width [] [] valid master) =
      tapes assignment [] [] [] [] valid master := by
    funext i; fin_cases i <;> simp [clearStacks, tapes]
  rw [he] at h
  exact h

abbrev copyClause : Cmd 4 13 := .call (copyProgram 12 8 7 0 1)

theorem copyClause_eval (assignment valid master : List Bool) :
    Eval copyClause (7 * master.length + 5)
      (data assignment [] [] [] [] valid master)
      (data assignment [] [] master [] valid master) := by
  have h := ListRegisterProgram.copy_run (12 : Fin 13) 8 7 (0 : Fin 4) 1
    (by decide) (by decide) (by decide) (by decide) zeroRegs
    (tapes assignment [] [] [] [] valid master) rfl
  have he : copyStacks (12 : Fin 13) 8 (tapes assignment [] [] [] [] valid master) =
      tapes assignment [] [] master [] valid master := by
    funext i; fin_cases i <;> simp [copyStacks, tapes]
  rw [he, read_zero] at h
  exact .call _ h

def rowStacks (i : Fin 10) : Fin 13 := i.castAdd 3

theorem rowStacks_injective : Function.Injective rowStacks := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 13 => x.val) h)

private theorem embed_row (assignment answer clause valid master : List Bool)
    (oldAssignment oldAnswer oldClause : List Bool) :
    embedState id rowStacks (data oldAssignment oldAnswer [] oldClause [] valid master)
      (SubexpClauseRowProgram.data false false false false assignment answer [] [] clause []) =
        data assignment answer [] clause [] valid master := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id rowStacks_injective
  · intro i; fin_cases i <;> rfl
  · intro i hi; rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
    have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
    have h8 : i ≠ 8 := fun h => hi ⟨8, h.symm⟩
    change tapes assignment answer [] clause [] valid master i =
      tapes oldAssignment oldAnswer [] oldClause [] valid master i
    simp only [tapes_eq, h0, h1, h8, ite_false]

abbrev row : Cmd 4 13 := .call
  (ProgramLinking.liftProgram SubexpClauseRowProgram.program id rowStacks)

theorem row_eval {n : ℕ} (assignment : List Bool) (hlen : assignment.length = n)
    (ls : List (SAT.Literal (Fin n))) (valid : List Bool) :
    Eval row (SubexpClauseRowProgram.rowCost ls + 12)
      (data assignment [] [] (SubexpClauseRowProgram.clauseBytes ls) [] valid
        (SubexpClauseRowProgram.clauseBytes ls))
      (data assignment [ls.any (fun l => l.eval
        (SubexpClauseRowProgram.wordAssignment assignment hlen))] [] [] [] valid
        (SubexpClauseRowProgram.clauseBytes ls)) := by
  have he := SubexpClauseRowProgram.eval_word assignment hlen ls false false false false []
  have ht := compiled_halt_trace he (8 : Fin 10) 1
  have h := eval_call_lifted SubexpClauseRowProgram.program id rowStacks
    (data assignment [] [] (SubexpClauseRowProgram.clauseBytes ls) [] valid
      (SubexpClauseRowProgram.clauseBytes ls)) Function.injective_id rowStacks_injective ht
  simpa only [List.append_nil, embed_row, Nat.add_assoc] using h

private def straight : List (StructuredProgram.Atom 4 13) → StructuredProgram.Cmd 4 13
  | [] => .skip
  | a :: as => .seq (.atom a) (straight as)

private def straightResult : List (StructuredProgram.Atom 4 13) → Data → Data
  | [], d => d
  | a :: as, d => straightResult as (a.eval d)

private theorem straight_eval (as : List (StructuredProgram.Atom 4 13)) (d : Data) :
    StructuredProgram.Eval (straight as) as.length d (straightResult as d) := by
  induction as generalizing d with
  | nil => exact .skip d
  | cons a as ih =>
      simpa only [straight, straightResult, List.length_cons, Nat.add_comm 1] using
        StructuredProgram.Eval.seq (.atom a d) (ih (a.eval d))

private def combineOps : List (StructuredProgram.Atom 4 13) :=
  [.pop 1 0 2, .pop 11 1 2, .band 0 1 0, .push 1 0,
    .set 0 false, .set 1 false, .set 2 false]

abbrev combine : Cmd 4 13 := .base (straight combineOps)

theorem combine_eval (assignment master : List Bool) (answer valid : Bool) :
    Eval combine 7 (data assignment [answer] [] [] [] [valid] master)
      (data assignment [valid && answer] [] [] [] [] master) := by
  have h := straight_eval combineOps (data assignment [answer] [] [] [] [valid] master)
  have he : straightResult combineOps (data assignment [answer] [] [] [] [valid] master) =
      data assignment [valid && answer] [] [] [] [] master := by
    apply state_ext
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [he] at h
  exact .base (by simpa only [combineOps, List.length_cons, List.length_nil] using h)

abbrev clearAssignment : Cmd 4 13 := .call (clearProgram 0 0 1)

theorem clearAssignment_eval (assignment answer master : List Bool) :
    Eval clearAssignment (2 * assignment.length + 3)
      (data assignment answer [] [] [] [] master)
      (data [] answer [] [] [] [] master) := by
  have h := clear_eval 0 (tapes assignment answer [] [] [] [] master)
  have he : clearStacks (0 : Fin 13) (tapes assignment answer [] [] [] [] master) =
      tapes [] answer [] [] [] [] master := by
    funext i; fin_cases i <;> simp [clearStacks, tapes]
  rw [he] at h
  exact h

abbrev command : Cmd 4 13 := .seq finalize (.seq clearWidth
  (.seq copyClause (.seq row (.seq combine clearAssignment))))

def workCost {n : ℕ} (ls : List (SAT.Literal (Fin n))) (paddingWidth : ℕ) : ℕ :=
  18 * n + 4 * paddingWidth + 7 * (SubexpClauseRowProgram.clauseBytes ls).length +
    SubexpClauseRowProgram.rowCost ls + 57

/-- End-to-end execution, including invalid-label and trailing-padding rejection. -/
theorem command_eval {n : ℕ} (assignment padding width : List Bool)
    (hlen : assignment.length = n) (hw : width.length = n)
    (ls : List (SAT.Literal (Fin n))) (prior : Bool) :
    Eval command (workCost ls padding.length)
      (data [] (assignment ++ padding) width [] [prior] []
        (SubexpClauseRowProgram.clauseBytes ls))
      (data [] [(prior && SubexpFactorProgram.allZero padding) &&
        ls.any (fun l => l.eval (SubexpClauseRowProgram.wordAssignment assignment hlen))]
        [] [] [] [] (SubexpClauseRowProgram.clauseBytes ls)) := by
  have h := (finalize_eval assignment padding width _ prior (hw.trans hlen.symm)).seq
    ((clearWidth_eval assignment width _ _).seq ((copyClause_eval assignment _ _).seq
      ((row_eval assignment hlen ls _).seq ((combine_eval assignment _ _ _).seq
        (clearAssignment_eval assignment _ _)))))
  convert h using 1
  simp only [workCost, SubexpCandidateFinalize.workCost, hlen, hw]
  ring

def program := compiled command (1 : Fin 13) 1

theorem trace {n : ℕ} (assignment padding width : List Bool)
    (hlen : assignment.length = n) (hw : width.length = n)
    (ls : List (SAT.Literal (Fin n))) (prior : Bool) :
    Trace program (workCost ls padding.length + 1)
      ((data [] (assignment ++ padding) width [] [prior] []
        (SubexpClauseRowProgram.clauseBytes ls)).withPC (some program.entry))
      ((data [] [(prior && SubexpFactorProgram.allZero padding) &&
        ls.any (fun l => l.eval (SubexpClauseRowProgram.wordAssignment assignment hlen))]
        [] [] [] [] (SubexpClauseRowProgram.clauseBytes ls)).withPC none) :=
  compiled_halt_trace (command_eval assignment padding width hlen hw ls prior) 1 1

theorem primitive_execution {n : ℕ} (assignment padding width : List Bool)
    (hlen : assignment.length = n) (hw : width.length = n)
    (ls : List (SAT.Literal (Fin n))) (prior : Bool) :
    Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * (workCost ls padding.length + 1))
      (BitProgram.primitiveCfg program
        ((data [] (assignment ++ padding) width [] [prior] []
          (SubexpClauseRowProgram.clauseBytes ls)).withPC (some program.entry)))
      (BitProgram.primitiveCfg program
        ((data [] [(prior && SubexpFactorProgram.allZero padding) &&
          ls.any (fun l => l.eval (SubexpClauseRowProgram.wordAssignment assignment hlen))]
          [] [] [] [] (SubexpClauseRowProgram.clauseBytes ls)).withPC none)) :=
  BitProgram.primitive_trace program (trace assignment padding width hlen hw ls prior)

end SubexponentialSAT.SubexpCandidateRowProgram

end OAI.Algorithms
