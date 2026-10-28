import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFieldRowPreparation
import OAI.Algorithms.SubexponentialSAT.SubexpScopeMaterializer
import OAI.Algorithms.SubexponentialSAT.SubexpCandidateRowProgram
import OAI.Algorithms.SubexponentialSAT.RankAssignmentLift

namespace OAI.Algorithms

/-!
# Preserving field-candidate evaluation

One scalar rank is unranked only over the factor's local scope. The resulting
labels are materialized into an actually allocated zero array, checked for
invalid high bits and last-chunk padding, and passed to the indexed clause
program. All factor descriptors and enumeration counters are preserved.
-/

namespace SubexponentialSAT.SubexpFieldRowProgram

open BitProgram StructuredCalls StackRoutines

structure Masters where
  modulus : List Bool
  rank : List Bool
  arity : List Bool
  nShape : List Bool
  fullShape : List Bool
  ell : List Bool
  scope : List Bool
  clause : List Bool
  width : List Bool
  fuel : List Bool
  scratch : List Bool
  output : List Bool

abbrev Data := State 8 30

def tapes (m : Masters) (array ell scope labels width valid : List Bool) : Fin 30 → List Bool :=
  fun i => if i = 0 then array else if i = 3 then ell else if i = 10 then scope
    else if i = 11 then labels else if i = 12 then width else if i = 17 then valid
    else if i = 18 then m.modulus else if i = 19 then m.rank else if i = 20 then m.arity
    else if i = 21 then m.nShape else if i = 22 then m.fullShape else if i = 23 then m.ell
    else if i = 24 then m.scope else if i = 25 then m.clause else if i = 26 then m.width
    else if i = 27 then m.fuel else if i = 28 then m.scratch else if i = 29 then m.output
    else []

def data (regs : Fin 8 → Bool) (m : Masters) (array ell scope labels width valid : List Bool) : Data :=
  ⟨regs, tapes m array ell scope labels width valid⟩

def zeroRegs : Fin 8 → Bool := fun _ => false

private theorem state_ext {r s : ℕ} {a b : State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; simp_all

@[simp] theorem tapes_0 (m : Masters) (a e s l w v : List Bool) : tapes m a e s l w v 0 = a := rfl
@[simp] theorem tapes_3 (m : Masters) (a e s l w v : List Bool) : tapes m a e s l w v 3 = e := rfl
@[simp] theorem tapes_10 (m : Masters) (a e s l w v : List Bool) : tapes m a e s l w v 10 = s := rfl
@[simp] theorem tapes_11 (m : Masters) (a e s l w v : List Bool) : tapes m a e s l w v 11 = l := rfl
@[simp] theorem tapes_12 (m : Masters) (a e s l w v : List Bool) : tapes m a e s l w v 12 = w := rfl
@[simp] theorem tapes_14 (m : Masters) (a e s l w v : List Bool) : tapes m a e s l w v 14 = [] := rfl
@[simp] theorem tapes_17 (m : Masters) (a e s l w v : List Bool) : tapes m a e s l w v 17 = v := rfl
@[simp] theorem tapes_23 (m : Masters) (a e s l w v : List Bool) : tapes m a e s l w v 23 = m.ell := rfl
@[simp] theorem tapes_24 (m : Masters) (a e s l w v : List Bool) : tapes m a e s l w v 24 = m.scope := rfl
@[simp] theorem tapes_26 (m : Masters) (a e s l w v : List Bool) : tapes m a e s l w v 26 = m.width := rfl

@[simp] theorem tapes_update_0 (m : Masters) (a e s l w v x : List Bool) :
    Function.update (tapes m a e s l w v) 0 x = tapes m x e s l w v := by
  funext i; fin_cases i <;> simp [tapes]
@[simp] theorem tapes_update_3 (m : Masters) (a e s l w v x : List Bool) :
    Function.update (tapes m a e s l w v) 3 x = tapes m a x s l w v := by
  funext i; fin_cases i <;> simp [tapes]
@[simp] theorem tapes_update_10 (m : Masters) (a e s l w v x : List Bool) :
    Function.update (tapes m a e s l w v) 10 x = tapes m a e x l w v := by
  funext i; fin_cases i <;> simp [tapes]
@[simp] theorem tapes_update_12 (m : Masters) (a e s l w v x : List Bool) :
    Function.update (tapes m a e s l w v) 12 x = tapes m a e s l x v := by
  funext i; fin_cases i <;> simp [tapes]

/-- The preserving rank decoder shares only its three read-only descriptors
with the enumeration state; its output port is the materializer's label stream. -/
def preparePorts : Fin 15 → Fin 30 :=
  ![0, 1, 2, 4, 5, 18, 6, 7, 8, 9, 13, 14, 11, 19, 20]

theorem preparePorts_injective : Function.Injective preparePorts := by decide

private theorem embed_prepare (regs oldRegs : Fin 8 → Bool) (m : Masters) (labels : List Bool) :
    embedState id preparePorts (data oldRegs m [] [] [] [] [] [])
      (SubexpFieldRowPreparation.data regs m.modulus m.rank m.arity [] [] labels) =
        data regs m [] [] [] labels [] [] := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id preparePorts_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h11 : i ≠ 11 := fun h => hi ⟨12, by simpa [preparePorts] using h.symm⟩
    simp only [data, tapes, h11, ite_false]

abbrev prepare : Cmd 8 30 := .call
  (ProgramLinking.liftProgram SubexpFieldRowPreparation.program id preparePorts)

theorem prepare_eval (regs : Fin 8 → Bool) (m : Masters) :
    ∃ n ≤ SubexpFieldRowPreparation.budget m.modulus m.rank m.arity + 1, ∃ rf,
      Eval prepare n (data regs m [] [] [] [] [] [])
        (data rf m [] [] []
          (SubexpBasePUnranking.digitWords m.modulus m.arity.length m.rank).flatten [] []) := by
  obtain ⟨rf, n, hn, ht⟩ := SubexpFieldRowPreparation.program_runsIn regs m.modulus m.rank m.arity []
  have h := eval_call_lifted SubexpFieldRowPreparation.program id preparePorts
    (data regs m [] [] [] [] [] []) Function.injective_id preparePorts_injective ht
  simp only [List.append_nil, embed_prepare] at h
  exact ⟨n, hn, rf, h⟩

def allocationPorts : Fin 6 ↪ Fin 30 :=
  ⟨![1, 22, 0, 4, 5, 6], by decide⟩

abbrev allocate : Cmd 8 30 := .call (RankAssignmentLift.programAt allocationPorts)

theorem allocate_eval (regs : Fin 8 → Bool) (m : Masters) (labels : List Bool) :
    ∃ rf, Eval allocate (14 * m.fullShape.length + 17)
      (data regs m [] [] [] labels [] [])
      (data rf m (List.replicate m.fullShape.length false) [] [] labels [] []) := by
  obtain ⟨rf, h, _⟩ := RankAssignmentLift.programAt_eval allocationPorts [] m.fullShape regs
    (tapes m [] [] [] labels [] []) rfl rfl (by simp) rfl rfl rfl rfl
  refine ⟨rf, ?_⟩
  have hp : ModularArithmetic.padTo m.fullShape [] = List.replicate m.fullShape.length false := by
    simpa using RankAssignmentProgram.padTo_eq_append_zeros m.fullShape [] (by simp)
  simp only [List.length_nil, Nat.mul_zero, Nat.zero_add] at h
  change Eval allocate (14 * m.fullShape.length + 17)
    (data regs m [] [] [] labels [] [])
    ⟨rf, Function.update (tapes m [] [] [] labels [] []) (0 : Fin 30)
      (ModularArithmetic.padTo m.fullShape [])⟩ at h
  rw [hp, tapes_update_0] at h
  exact h

private theorem copy_eval (src dst : Fin 30) (hsd : src ≠ dst)
    (hst : src ≠ 14) (htd : (14 : Fin 30) ≠ dst)
    (regs : Fin 8 → Bool) (stk : Fin 30 → List Bool) (ht : stk 14 = []) :
    Eval (.call (copyProgram src dst 14 (0 : Fin 8) 1)) (7 * (stk src).length + 5)
      ⟨regs, stk⟩ ⟨readRegs regs 0 1 none, copyStacks src dst stk⟩ :=
  .call _ (ListRegisterProgram.copy_run src dst 14 (0 : Fin 8) 1 hsd hst htd (by decide) regs stk ht)

abbrev copyDescriptors : Cmd 8 30 := .seq (.call (copyProgram 23 3 14 0 1))
  (.seq (.call (copyProgram 26 12 14 0 1)) (.call (copyProgram 24 10 14 0 1)))

theorem copyDescriptors_eval (regs : Fin 8 → Bool) (m : Masters) (array labels : List Bool) :
    Eval copyDescriptors (7 * m.ell.length + 7 * m.width.length + 7 * m.scope.length + 15)
      (data regs m array [] [] labels [] [])
      (data (readRegs regs 0 1 none) m array m.ell m.scope labels m.width []) := by
  have h₁ := copy_eval 23 3 (by decide) (by decide) (by decide) regs
    (tapes m array [] [] labels [] []) rfl
  simp only [copyStacks, tapes_23, tapes_3, List.append_nil, tapes_update_3] at h₁
  have h₂ := copy_eval 26 12 (by decide) (by decide) (by decide) (readRegs regs 0 1 none)
    (tapes m array m.ell [] labels [] []) rfl
  simp only [copyStacks, tapes_26, tapes_12, List.append_nil, tapes_update_12, readRegs_reset] at h₂
  have h₃ := copy_eval 24 10 (by decide) (by decide) (by decide) (readRegs regs 0 1 none)
    (tapes m array m.ell [] labels m.width []) rfl
  simp only [copyStacks, tapes_24, tapes_10, List.append_nil, tapes_update_10, readRegs_reset] at h₃
  convert h₁.seq (h₂.seq h₃) using 1 <;> first | rfl | ring

private def straight : List (StructuredProgram.Atom 8 30) → StructuredProgram.Cmd 8 30
  | [] => .skip
  | a :: as => .seq (.atom a) (straight as)

private def straightResult : List (StructuredProgram.Atom 8 30) → Data → Data
  | [], d => d
  | a :: as, d => straightResult as (a.eval d)

private theorem straight_eval (as : List (StructuredProgram.Atom 8 30)) (d : Data) :
    StructuredProgram.Eval (straight as) as.length d (straightResult as d) := by
  induction as generalizing d with
  | nil => exact .skip d
  | cons a as ih =>
      simpa only [straight, straightResult, List.length_cons, Nat.add_comm 1] using
        StructuredProgram.Eval.seq (.atom a d) (ih (a.eval d))

private def initializeOps : List (StructuredProgram.Atom 8 30) :=
  [.set 0 true, .push 17 0, .set 0 false, .set 1 false, .set 2 false, .set 3 false,
    .set 4 false, .set 5 false, .set 6 false, .set 7 false]

abbrev initializeRow : Cmd 8 30 := .base (straight initializeOps)

theorem initialize_eval (regs : Fin 8 → Bool) (m : Masters) (array labels : List Bool) :
    Eval initializeRow 10 (data regs m array m.ell m.scope labels m.width [])
      (data zeroRegs m array m.ell m.scope labels m.width [true]) := by
  have h := straight_eval initializeOps (data regs m array m.ell m.scope labels m.width [])
  have he : straightResult initializeOps (data regs m array m.ell m.scope labels m.width []) =
      data zeroRegs m array m.ell m.scope labels m.width [true] := by
    apply state_ext
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [he] at h
  exact .base (by simpa only [initializeOps, List.length_cons, List.length_nil] using h)


def scopeRegisters : Fin 6 → Fin 8 := Fin.castAdd 2
def scopeStacks : Fin 18 → Fin 30 := Fin.castAdd 12

theorem scopeRegisters_injective : Function.Injective scopeRegisters := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 8 => x.val) h)
theorem scopeStacks_injective : Function.Injective scopeStacks := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 30 => x.val) h)

def scopeRegs (tag present : Bool) : Fin 8 → Bool :=
  fun i => if i = 3 then tag else if i = 4 then present else false

private theorem scopeRegs_false : scopeRegs false false = zeroRegs := by
  funext i; fin_cases i <;> rfl

private theorem embed_scope (m : Masters) (tag present oldTag oldPresent : Bool)
    (array ell scope labels width : List Bool) (valid : Bool)
    (oldArray oldEll oldScope oldLabels oldWidth : List Bool) (oldValid : Bool) :
    embedState scopeRegisters scopeStacks
      (data (scopeRegs oldTag oldPresent) m oldArray oldEll oldScope oldLabels oldWidth [oldValid])
      (SubexpScopeMaterializer.resting tag present array ell scope labels width valid) =
      data (scopeRegs tag present) m array ell scope labels width [valid] := by
  apply embedState_eq_of_ports _ _ _ _ _ scopeRegisters_injective scopeStacks_injective
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h3 : i ≠ 3 := fun h => hi ⟨3, by simpa [scopeRegisters] using h.symm⟩
    have h4 : i ≠ 4 := fun h => hi ⟨4, by simpa [scopeRegisters] using h.symm⟩
    simp only [data, scopeRegs, h3, h4, ite_false]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0, by simpa [scopeStacks] using h.symm⟩
    have h3 : i ≠ 3 := fun h => hi ⟨3, by simpa [scopeStacks] using h.symm⟩
    have h10 : i ≠ 10 := fun h => hi ⟨10, by simpa [scopeStacks] using h.symm⟩
    have h11 : i ≠ 11 := fun h => hi ⟨11, by simpa [scopeStacks] using h.symm⟩
    have h12 : i ≠ 12 := fun h => hi ⟨12, by simpa [scopeStacks] using h.symm⟩
    have h17 : i ≠ 17 := fun h => hi ⟨17, by simpa [scopeStacks] using h.symm⟩
    simp only [data, tapes, h0, h3, h10, h11, h12, h17, ite_false]

abbrev materialize : Cmd 8 30 := .call
  (ProgramLinking.liftProgram SubexpScopeMaterializer.program scopeRegisters scopeStacks)

theorem materialize_eval {D : ℕ} (m : Masters) (jobs : List (Fin D × List Bool))
    (chunks : List (List Bool)) (hcount : chunks.length = D)
    (hrows : ∀ row ∈ chunks, row.length = m.ell.length)
    (hwidth : ∀ job ∈ jobs, job.2.length = m.width.length)
    (hell : m.ell.length ≤ m.width.length) :
    Eval materialize (SubexpScopeMaterializer.rowCost m.ell.length m.width.length jobs + 3)
      (data zeroRegs m chunks.flatten m.ell (SubexpScopeMaterializer.scopeBytes jobs)
        (SubexpScopeMaterializer.labelBytes jobs) m.width [true])
      (data (scopeRegs false true) m
        (SubexpScopeMaterializer.materialize m.ell.length jobs chunks true).1.flatten
        m.ell [] [] m.width
        [(SubexpScopeMaterializer.materialize m.ell.length jobs chunks true).2]) := by
  have h := SubexpScopeMaterializer.lifted_eval scopeRegisters scopeStacks
    scopeRegisters_injective scopeStacks_injective
    (data (scopeRegs false false) m chunks.flatten m.ell
      (SubexpScopeMaterializer.scopeBytes jobs) (SubexpScopeMaterializer.labelBytes jobs)
      m.width [true]) jobs chunks m.ell m.width [] [] true hcount hrows hwidth hell
  simp only [List.append_nil, embed_scope] at h
  simpa only [scopeRegs_false] using h

private theorem clear_eval (source : Fin 30) (regs : Fin 8 → Bool) (stk : Fin 30 → List Bool) :
    Eval (.call (clearProgram source (0 : Fin 8) 1)) (2 * (stk source).length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs 0 1 none, clearStacks source stk⟩ := by
  apply Eval.call
  have h := halt_after_trace _ (clearProgram_trace source (0 : Fin 8) 1 regs stk) 2 rfl rfl
  simpa [StructuredProgram.State.withPC, clearResult, clearProgram, Nat.add_assoc] using h

private def resetOps : List (StructuredProgram.Atom 8 30) :=
  [.set 0 false, .set 1 false, .set 2 false, .set 3 false,
    .set 4 false, .set 5 false, .set 6 false, .set 7 false]

abbrev reset : Cmd 8 30 := .base (straight resetOps)

theorem reset_eval (regs : Fin 8 → Bool) (stk : Fin 30 → List Bool) :
    Eval reset 8 ⟨regs, stk⟩ ⟨zeroRegs, stk⟩ := by
  have h := straight_eval resetOps ⟨regs, stk⟩
  have he : straightResult resetOps ⟨regs, stk⟩ = (⟨zeroRegs, stk⟩ : Data) := by
    apply state_ext
    · funext i; fin_cases i <;> rfl
    · rfl
  rw [he] at h
  exact .base (by simpa only [resetOps, List.length_cons, List.length_nil] using h)

abbrev prepareFinish : Cmd 8 30 := .seq (.call (clearProgram 3 0 1))
  (.seq (.call (clearProgram 12 0 1)) (.seq (.call (copyProgram 21 3 14 0 1)) reset))

theorem prepareFinish_eval (regs : Fin 8 → Bool) (m : Masters) (array : List Bool) (valid : Bool) :
    Eval prepareFinish (2 * m.ell.length + 2 * m.width.length + 7 * m.nShape.length + 19)
      (data regs m array m.ell [] [] m.width [valid])
      (data zeroRegs m array m.nShape [] [] [] [valid]) := by
  have h₁ := clear_eval 3 regs (tapes m array m.ell [] [] m.width [valid])
  simp only [clearStacks, tapes_3, tapes_update_3] at h₁
  have h₂ := clear_eval 12 (readRegs regs 0 1 none) (tapes m array [] [] [] m.width [valid])
  simp only [clearStacks, tapes_12, tapes_update_12, readRegs_reset] at h₂
  have h₃ := copy_eval 21 3 (by decide) (by decide) (by decide) (readRegs regs 0 1 none)
    (tapes m array [] [] [] [] [valid]) rfl
  have h21 : tapes m array [] [] [] [] [valid] 21 = m.nShape := rfl
  simp only [copyStacks, h21, tapes_3, List.append_nil, tapes_update_3, readRegs_reset] at h₃
  have h₄ := reset_eval (readRegs regs 0 1 none) (tapes m array m.nShape [] [] [] [valid])
  convert h₁.seq (h₂.seq (h₃.seq h₄)) using 1 <;> first | rfl | ring

def finishRegisters : Fin 4 → Fin 8 := Fin.castAdd 4
def finishStacks : Fin 13 → Fin 30 := ![1, 0, 4, 3, 5, 6, 7, 8, 9, 10, 17, 2, 25]

theorem finishRegisters_injective : Function.Injective finishRegisters := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 8 => x.val) h)
theorem finishStacks_injective : Function.Injective finishStacks := by decide

private theorem embed_finish (m : Masters) (array width prior oldArray oldWidth oldPrior : List Bool) :
    embedState finishRegisters finishStacks (data zeroRegs m oldArray oldWidth [] [] [] oldPrior)
      (SubexpCandidateRowProgram.data [] array width [] prior [] m.clause) =
      data zeroRegs m array width [] [] [] prior := by
  apply embedState_eq_of_ports _ _ _ _ _ finishRegisters_injective finishStacks_injective
  · intro i; rfl
  · intro i hi; rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨1, by simpa [finishStacks] using h.symm⟩
    have h3 : i ≠ 3 := fun h => hi ⟨3, by simpa [finishStacks] using h.symm⟩
    have h17 : i ≠ 17 := fun h => hi ⟨10, by simpa [finishStacks] using h.symm⟩
    simp only [data, tapes, h0, h3, h17, ite_false]

abbrev finish : Cmd 8 30 := .call
  (ProgramLinking.liftProgram SubexpCandidateRowProgram.program finishRegisters finishStacks)

theorem finish_eval {n : ℕ} (m : Masters) (assignment padding : List Bool)
    (hlen : assignment.length = n) (hw : m.nShape.length = n)
    (ls : List (SAT.Literal (Fin n))) (hclause : m.clause = SubexpClauseRowProgram.clauseBytes ls)
    (prior : Bool) :
    Eval finish (SubexpCandidateRowProgram.workCost ls padding.length + 1)
      (data zeroRegs m (assignment ++ padding) m.nShape [] [] [] [prior])
      (data zeroRegs m [(prior && SubexpFactorProgram.allZero padding) &&
        ls.any (fun l => l.eval (SubexpClauseRowProgram.wordAssignment assignment hlen))]
        [] [] [] [] []) := by
  have h := eval_call_lifted SubexpCandidateRowProgram.program finishRegisters finishStacks
    (data zeroRegs m (assignment ++ padding) m.nShape [] [] [] [prior])
    finishRegisters_injective finishStacks_injective
    (SubexpCandidateRowProgram.trace assignment padding m.nShape hlen hw ls prior)
  rw [← hclause] at h
  simpa only [embed_finish] using h

abbrev emit : Cmd 8 30 := .call (transferProgram 0 29 0 1)

theorem emit_eval (m : Masters) (answer : Bool) :
    Eval emit 6 (data zeroRegs m [answer] [] [] [] [] [])
      (data zeroRegs {m with output := answer :: m.output} [] [] [] [] [] []) := by
  have h := ListRegisterProgram.transfer_run (0 : Fin 30) 29 (0 : Fin 8) 1
    (by decide) (by decide) zeroRegs (tapes m [answer] [] [] [] [] [])
  have hr : readRegs zeroRegs (0 : Fin 8) 1 none = zeroRegs := by
    funext i; fin_cases i <;> simp [zeroRegs, readRegs]
  have he : transferStacks (0 : Fin 30) 29 (tapes m [answer] [] [] [] [] []) =
      tapes {m with output := answer :: m.output} [] [] [] [] [] [] := by
    funext i; fin_cases i <;> simp [transferStacks, tapes]
  apply Eval.call
  simpa only [tapes_0, List.length_cons, List.length_nil, hr, he,
    data, StructuredProgram.State.withPC] using h

abbrev command : Cmd 8 30 := .seq prepare (.seq allocate (.seq copyDescriptors
  (.seq initializeRow (.seq materialize (.seq prepareFinish (.seq finish emit))))))


def zeroChunks (D ell : ℕ) : List (List Bool) :=
  List.replicate D (List.replicate ell false)

theorem zeroChunks_flatten (D ell : ℕ) :
    (zeroChunks D ell).flatten = List.replicate (D * ell) false := by
  induction D with
  | zero => simp [zeroChunks]
  | succ D ih =>
      change List.replicate ell false ++ (zeroChunks D ell).flatten =
        List.replicate ((D + 1) * ell) false
      rw [ih, ← List.replicate_add]
      congr 1
      ring

private theorem flatten_length (ell : ℕ) (chunks : List (List Bool))
    (hrows : ∀ row ∈ chunks, row.length = ell) :
    chunks.flatten.length = chunks.length * ell := by
  induction chunks with
  | nil => simp
  | cons row rest ih =>
      have hr := hrows row (by simp)
      have ht := ih (fun r h => hrows r (by simp [h]))
      simp only [List.flatten_cons, List.length_append, hr, ht, List.length_cons]
      ring

private theorem digitWords_width (modulus rank : List Bool) (k : ℕ) :
    ∀ word ∈ SubexpBasePUnranking.digitWords modulus k rank,
      word.length = modulus.length := by
  induction k generalizing rank with
  | zero => simp [SubexpBasePUnranking.digitWords]
  | succ k ih =>
      intro word hw
      simp only [SubexpBasePUnranking.digitWords, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact SubexpBasePUnranking.digit_length _ _
      · exact ih _ word hw

def rowBudget {D n : ℕ} (m : Masters) (jobs : List (Fin D × List Bool))
    (ls : List (SAT.Literal (Fin n))) : ℕ :=
  (SubexpFieldRowPreparation.budget m.modulus m.rank m.arity + 1) +
  (14 * m.fullShape.length + 17) +
  (7 * m.ell.length + 7 * m.width.length + 7 * m.scope.length + 15) + 10 +
  (SubexpScopeMaterializer.rowCost m.ell.length m.width.length jobs + 3) +
  (2 * m.ell.length + 2 * m.width.length + 7 * m.nShape.length + 19) +
  (SubexpCandidateRowProgram.workCost ls (m.fullShape.length - n) + 1) + 6

/-- Every hypothesis describes actual input bytes or widths. The witness is a
complete execution of the fixed program, including its data preparation. -/
theorem command_eval {D n : ℕ} (regs : Fin 8 → Bool) (m : Masters)
    (jobs : List (Fin D × List Bool)) (ls : List (SAT.Literal (Fin n)))
    (hwords : jobs.map Prod.snd =
      SubexpBasePUnranking.digitWords m.modulus m.arity.length m.rank)
    (hwidth : m.width.length = m.modulus.length)
    (hell : m.ell.length ≤ m.width.length)
    (hfull : m.fullShape.length = D * m.ell.length)
    (hnshape : m.nShape.length = n) (hn : n ≤ m.fullShape.length)
    (hscope : m.scope = SubexpScopeMaterializer.scopeBytes jobs)
    (hclause : m.clause = SubexpClauseRowProgram.clauseBytes ls) :
    let result := SubexpScopeMaterializer.materialize m.ell.length jobs
      (zeroChunks D m.ell.length) true
    let array := result.1.flatten
    ∃ hlen : (array.take n).length = n,
      ∃ t ≤ rowBudget m jobs ls,
        Eval command t (data regs m [] [] [] [] [] [])
          (data zeroRegs {m with output :=
            ((result.2 && SubexpFactorProgram.allZero (array.drop n)) &&
              ls.any (fun l => l.eval
                (SubexpClauseRowProgram.wordAssignment (array.take n) hlen))) :: m.output}
            [] [] [] [] [] []) := by
  let chunks := zeroChunks D m.ell.length
  let result := SubexpScopeMaterializer.materialize m.ell.length jobs chunks true
  let array := result.1.flatten
  have hcount : chunks.length = D := by simp [chunks, zeroChunks]
  have hrows : ∀ row ∈ chunks, row.length = m.ell.length := by
    intro row hr
    have he : row = List.replicate m.ell.length false := (List.mem_replicate.mp hr).2
    simp [he]
  have hzero : chunks.flatten = List.replicate m.fullShape.length false := by
    rw [hfull]
    exact zeroChunks_flatten D m.ell.length
  have hjobWidth : ∀ job ∈ jobs, job.2.length = m.width.length := by
    intro job hj
    have hjw : job.2 ∈ SubexpBasePUnranking.digitWords m.modulus m.arity.length m.rank := by
      rw [← hwords]
      exact List.mem_map.mpr ⟨job, hj, rfl⟩
    exact (digitWords_width m.modulus m.rank m.arity.length job.2 hjw).trans hwidth.symm
  have harray : array.length = m.fullShape.length := by
    have hc := SubexpScopeMaterializer.materialize_length m.ell.length jobs chunks true
    have hu := SubexpScopeMaterializer.materialize_uniform m.ell.length m.width.length
      jobs chunks true hrows hjobWidth hell
    change result.1.length = chunks.length at hc
    calc
      array.length = result.1.length * m.ell.length :=
        flatten_length m.ell.length result.1 hu
      _ = D * m.ell.length := by rw [hc, hcount]
      _ = m.fullShape.length := hfull.symm
  have hlen : (array.take n).length = n := by
    simp only [List.length_take, harray, Nat.min_eq_left hn]
  have hpadding : (array.drop n).length = m.fullShape.length - n := by
    simp [harray]
  obtain ⟨np, hnp, rp, hp⟩ := prepare_eval regs m
  rw [← hwords] at hp
  change Eval prepare np (data regs m [] [] [] [] [] [])
    (data rp m [] [] [] (SubexpScopeMaterializer.labelBytes jobs) [] []) at hp
  obtain ⟨ra, ha⟩ := allocate_eval rp m (SubexpScopeMaterializer.labelBytes jobs)
  rw [← hzero] at ha
  have hd := copyDescriptors_eval ra m chunks.flatten (SubexpScopeMaterializer.labelBytes jobs)
  have hi := initialize_eval (readRegs ra 0 1 none) m chunks.flatten
    (SubexpScopeMaterializer.labelBytes jobs)
  rw [hscope] at hi
  have hm := materialize_eval m jobs chunks hcount hrows hjobWidth hell
  have hf := prepareFinish_eval (scopeRegs false true) m array result.2
  have hv := finish_eval m (array.take n) (array.drop n) hlen hnshape ls hclause result.2
  rw [List.take_append_drop, hpadding] at hv
  have he := emit_eval m ((result.2 && SubexpFactorProgram.allZero (array.drop n)) &&
    ls.any (fun l => l.eval (SubexpClauseRowProgram.wordAssignment (array.take n) hlen)))
  rw [hscope] at hd
  have h := hp.seq (ha.seq (hd.seq (hi.seq (hm.seq (hf.seq (hv.seq he))))))
  refine ⟨hlen, _, ?_, h⟩
  unfold rowBudget
  rw [hscope]
  omega

def program := compiled command (19 : Fin 30) 29

theorem program_runsIn {D n : ℕ} (regs : Fin 8 → Bool) (m : Masters)
    (jobs : List (Fin D × List Bool)) (ls : List (SAT.Literal (Fin n)))
    (hwords : jobs.map Prod.snd =
      SubexpBasePUnranking.digitWords m.modulus m.arity.length m.rank)
    (hwidth : m.width.length = m.modulus.length)
    (hell : m.ell.length ≤ m.width.length)
    (hfull : m.fullShape.length = D * m.ell.length)
    (hnshape : m.nShape.length = n) (hn : n ≤ m.fullShape.length)
    (hscope : m.scope = SubexpScopeMaterializer.scopeBytes jobs)
    (hclause : m.clause = SubexpClauseRowProgram.clauseBytes ls) :
    let result := SubexpScopeMaterializer.materialize m.ell.length jobs
      (zeroChunks D m.ell.length) true
    let array := result.1.flatten
    ∃ hlen : (array.take n).length = n,
      RunsIn program (rowBudget m jobs ls + 1)
        ((data regs m [] [] [] [] [] []).withPC (some program.entry))
        ((data zeroRegs {m with output :=
          ((result.2 && SubexpFactorProgram.allZero (array.drop n)) &&
            ls.any (fun l => l.eval
              (SubexpClauseRowProgram.wordAssignment (array.take n) hlen))) :: m.output}
          [] [] [] [] [] []).withPC none) := by
  obtain ⟨hlen, t, ht, he⟩ := command_eval regs m jobs ls hwords hwidth hell hfull
    hnshape hn hscope hclause
  exact ⟨hlen, t + 1, Nat.add_le_add_right ht 1, compiled_halt_trace he 19 29⟩


/-- Pair the digits with this factor's actual ordered scope, never all D chunks. -/
def jobsFor {D : ℕ} (m : Masters) (scope : List (Fin D)) : List (Fin D × List Bool) :=
  scope.zip (SubexpBasePUnranking.digitWords m.modulus m.arity.length m.rank)

theorem jobsFor_words {D : ℕ} (m : Masters) (scope : List (Fin D))
    (hcount : scope.length = m.arity.length) :
    (jobsFor m scope).map Prod.snd =
      SubexpBasePUnranking.digitWords m.modulus m.arity.length m.rank := by
  apply List.map_snd_zip
  simp only [SubexpBasePUnranking.digitWords_length, hcount, le_refl]

theorem jobsFor_scope {D : ℕ} (m : Masters) (scope : List (Fin D))
    (hcount : scope.length = m.arity.length) :
    SubexpScopeMaterializer.scopeBytes (jobsFor m scope) =
      Encoding.encodeList Encoding.encodeNat (scope.map Fin.val) := by
  have hfst : (jobsFor m scope).map Prod.fst = scope := by
    apply List.map_fst_zip
    simp only [SubexpBasePUnranking.digitWords_length, hcount, le_refl]
  unfold SubexpScopeMaterializer.scopeBytes
  have hm : (jobsFor m scope).map (fun job => job.1.val) = scope.map Fin.val := by
    simpa only [List.map_map, Function.comp_def] using congrArg (List.map Fin.val) hfst
  rw [hm]

/-- The only data supplied here are the encoded descriptors and an ordered
scope. The local digit stream and its pairing are constructed by the program. -/
theorem scope_program_runsIn {D n : ℕ} (regs : Fin 8 → Bool) (m : Masters)
    (scope : List (Fin D)) (ls : List (SAT.Literal (Fin n)))
    (hcount : scope.length = m.arity.length)
    (hwidth : m.width.length = m.modulus.length)
    (hell : m.ell.length ≤ m.width.length)
    (hfull : m.fullShape.length = D * m.ell.length)
    (hnshape : m.nShape.length = n) (hn : n ≤ m.fullShape.length)
    (hscope : m.scope = Encoding.encodeList Encoding.encodeNat (scope.map Fin.val))
    (hclause : m.clause = SubexpClauseRowProgram.clauseBytes ls) :
    let result := SubexpScopeMaterializer.materialize m.ell.length (jobsFor m scope)
      (zeroChunks D m.ell.length) true
    let array := result.1.flatten
    ∃ hlen : (array.take n).length = n,
      RunsIn program (rowBudget m (jobsFor m scope) ls + 1)
        ((data regs m [] [] [] [] [] []).withPC (some program.entry))
        ((data zeroRegs {m with output :=
          ((result.2 && SubexpFactorProgram.allZero (array.drop n)) &&
            ls.any (fun l => l.eval
              (SubexpClauseRowProgram.wordAssignment (array.take n) hlen))) :: m.output}
          [] [] [] [] [] []).withPC none) :=
  program_runsIn regs m (jobsFor m scope) ls (jobsFor_words m scope hcount)
    hwidth hell hfull hnshape hn (hscope.trans (jobsFor_scope m scope hcount).symm) hclause

end SubexponentialSAT.SubexpFieldRowProgram

end OAI.Algorithms
