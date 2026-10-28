import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFieldRowValues
import OAI.Algorithms.SubexponentialSAT.SubexpEnumerationSchedule

namespace OAI.Algorithms

/-!
# Actual enumeration of a clause's local field table

The callback is the concrete preserving field-row program. The loop visits a
scalar interval and emits one Boolean value per rank, so the output order is
descending rank and each rank is interpreted with least-significant base-p
coordinate first. All costs include the growing number of local rows.
-/

namespace SubexponentialSAT.SubexpFieldTableEnumeration

open BitProgram StructuredCalls CounterPrograms SubexpEnumerationProgram
open SubexpFieldRowProgram (Masters)

abbrev Data := State 8 30

def ports : Ports 8 30 where
  register := ⟨Fin.castAdd 5, by
    intro i j h; exact Fin.ext (congrArg (fun x : Fin 8 => x.val) h)⟩
  current := 19
  remaining := 27
  scratch := 28
  current_ne_remaining := by decide
  current_ne_scratch := by decide
  remaining_ne_scratch := by decide

def current (m : Masters) (rank fuel output : List Bool) : Masters :=
  {m with rank := rank, fuel := fuel, scratch := [], output := output}

def resting (m : Masters) (regs : Fin 8 → Bool) (rank fuel output : List Bool) : Data :=
  SubexpFieldRowProgram.data regs (current m rank fuel output) [] [] [] [] [] []

abbrev body : Cmd 8 30 := SubexpFieldRowProgram.command
def program := SubexpEnumerationProgram.program ports body

structure Valid {D n : ℕ} (m : Masters) (scope : List (Fin D))
    (ls : List (SAT.Literal (Fin n))) : Prop where
  positive : 0 < BinaryArithmetic.toNat m.modulus
  arity : scope.length = m.arity.length
  width : m.width.length = m.modulus.length
  ell : m.ell.length ≤ m.width.length
  full : m.fullShape.length = D * m.ell.length
  shape : m.nShape.length = n
  covered : n ≤ m.fullShape.length
  scope : m.scope = Encoding.encodeList Encoding.encodeNat (scope.map Fin.val)
  clause : m.clause = SubexpClauseRowProgram.clauseBytes ls

theorem value_current {D n : ℕ} (m : Masters) (scope : List (Fin D))
    (ls : List (SAT.Literal (Fin n))) (rank fuel output : List Bool) (i : ℕ) :
    SubexpFieldRowValues.value (current m rank fuel output) scope ls i =
      SubexpFieldRowValues.value m scope ls i := rfl

def rows {D n : ℕ} (m : Masters) (scope : List (Fin D))
    (ls : List (SAT.Literal (Fin n))) (count : ℕ) : List Bool :=
  (List.range count).reverse.map (SubexpFieldRowValues.value m scope ls)

@[simp] theorem rows_zero {D n : ℕ} (m : Masters) (scope : List (Fin D))
    (ls : List (SAT.Literal (Fin n))) : rows m scope ls 0 = [] := rfl

theorem rows_succ {D n : ℕ} (m : Masters) (scope : List (Fin D))
    (ls : List (SAT.Literal (Fin n))) (count : ℕ) :
    rows m scope ls (count + 1) =
      SubexpFieldRowValues.value m scope ls count :: rows m scope ls count := by
  simp [rows, List.range_succ, List.reverse_append]

/-- A deliberately explicit bound polynomial in the row count and descriptor
sizes; the rank width is bounded by the number of executed increments. -/
def callbackBound {D n : ℕ} (m : Masters) (scope : List (Fin D))
    (ls : List (SAT.Literal (Fin n))) (rankWidth : ℕ) : ℕ :=
  (m.arity.length * (100 * (m.modulus.length + rankWidth + 1) ^ 2 +
    14 * m.modulus.length + 8 * rankWidth + 19) + 6 +
      9 * rankWidth + 7 * m.arity.length + 13 + 1) +
  (14 * m.fullShape.length + 17) +
  (7 * m.ell.length + 7 * m.width.length + 7 * m.scope.length + 15) + 10 +
  (scope.length * (D * (14 * m.ell.length + 19) +
    36 * m.ell.length + 18 * m.width.length + 78) + 3) +
  (2 * m.ell.length + 2 * m.width.length + 7 * m.nShape.length + 19) +
  (SubexpCandidateRowProgram.workCost ls (m.fullShape.length - n) + 1) + 6

theorem callback_bound {D n : ℕ} (m : Masters) (scope : List (Fin D))
    (ls : List (SAT.Literal (Fin n))) (hv : Valid m scope ls)
    (rank fuel output : List Bool) (L : ℕ) (hL : rank.length ≤ L) :
    SubexpFieldRowProgram.rowBudget (current m rank fuel output)
        (SubexpFieldRowValues.jobs (current m rank fuel output) scope
          (BinaryArithmetic.toNat rank)) ls ≤ callbackBound m scope ls L := by
  let jobs := SubexpFieldRowValues.jobs (current m rank fuel output) scope
    (BinaryArithmetic.toNat rank)
  have hw : ∀ job ∈ jobs, job.2.length = m.width.length := by
    intro job hj
    have hm := (List.of_mem_zip hj).2
    rcases List.mem_map.mp hm with ⟨i, hi, he⟩
    rw [← he, SubexpLiftRing.fixedBits_length, hv.width]
    rfl
  have hjlen : jobs.length ≤ scope.length := by
    simp only [jobs, SubexpFieldRowValues.jobs, List.length_zip]
    exact Nat.min_le_left _ _
  have hc := SubexpScopeMaterializer.rowCost_le m.ell.length m.width.length jobs hw
  have hcc : SubexpScopeMaterializer.rowCost m.ell.length m.width.length jobs ≤
      scope.length * (D * (14 * m.ell.length + 19) +
        36 * m.ell.length + 18 * m.width.length + 78) :=
    hc.trans (Nat.mul_le_mul_right _ hjlen)
  have hp : SubexpFieldRowPreparation.budget m.modulus rank m.arity ≤
      m.arity.length * (100 * (m.modulus.length + L + 1) ^ 2 +
        14 * m.modulus.length + 8 * L + 19) + 6 + 9 * L + 7 * m.arity.length + 13 := by
    unfold SubexpFieldRowPreparation.budget SubexpBasePUnranking.budget
    gcongr
  change SubexpFieldRowProgram.rowBudget (current m rank fuel output) jobs ls ≤ _
  unfold SubexpFieldRowProgram.rowBudget callbackBound current
  dsimp only
  omega

private theorem state_ext {a b : Data}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; simp_all

theorem next_resting (m : Masters) (regs : Fin 8 → Bool) (rank fuel output : List Bool) :
    nextState ports (resting m regs rank fuel output) =
      resting m (nextState ports (resting m regs rank fuel output)).regs
        (ripple true rank) (ripple false fuel) output := by
  apply state_ext
  · rfl
  · funext i
    by_cases hc : i = 19
    · subst i
      exact nextState_current ports (resting m regs rank fuel output)
    by_cases hr : i = 27
    · subst i
      exact nextState_remaining ports (resting m regs rank fuel output)
    by_cases hs : i = 28
    · subst i
      exact nextState_scratch ports (resting m regs rank fuel output)
    rw [nextState_other_stack ports _ i hc hr hs]
    simp only [resting, SubexpFieldRowProgram.data, SubexpFieldRowProgram.tapes,
      current, hc, hr, hs, ite_false]

theorem test_resting (m : Masters) (regs : Fin 8 → Bool) (rank fuel output : List Bool) :
    testResult ports (resting m regs rank fuel output) =
      resting m (testResult ports (resting m regs rank fuel output)).regs rank fuel output := by
  apply state_ext
  · rfl
  · exact testResult_stacks ports _ rfl

def Invariant {D n : ℕ} (m : Masters) (scope : List (Fin D))
    (ls : List (SAT.Literal (Fin n))) (count fuelWidth : ℕ) (d : Data) : Prop :=
  ∃ regs rank fuel done,
    d = resting m regs rank fuel (rows m scope ls done ++ m.output) ∧
    done ≤ count ∧ value rank = done ∧ value fuel = count - done ∧
    rank.length + value fuel ≤ count ∧ fuel.length = fuelWidth

/-- The quantified callback premise is closed with the concrete row program. -/
theorem body_step {D n : ℕ} (m : Masters) (scope : List (Fin D))
    (ls : List (SAT.Literal (Fin n))) (hv : Valid m scope ls) (count fuelWidth : ℕ) :
    SubexpEnumerationSchedule.BodyStep ports body (Invariant m scope ls count fuelWidth)
      (fun _ => callbackBound m scope ls count) := by
  intro d hd hs hp hf
  rcases hd with ⟨regs, rank, fuel, done, rfl, hdone, hcur, hrem, hwidth, hfwidth⟩
  change 0 < value fuel at hp
  have hcurNat : BinaryArithmetic.toNat rank = done := by
    simpa only [value_eq_toNat] using hcur
  let out := rows m scope ls done ++ m.output
  let now := current m rank fuel out
  obtain ⟨t, ht, he⟩ := SubexpFieldRowValues.command_eval regs now scope ls
    hv.positive hv.arity hv.width hv.ell hv.full hv.shape hv.covered hv.scope hv.clause
  let e := resting m SubexpFieldRowProgram.zeroRegs rank fuel
    (rows m scope ls (done + 1) ++ m.output)
  have hvalue : SubexpFieldRowValues.value now scope ls
      (BinaryArithmetic.toNat now.rank) = SubexpFieldRowValues.value m scope ls done := by
    rw [show BinaryArithmetic.toNat now.rank = done by simpa only [now, current] using hcurNat]
    rfl
  have hmodel : { now with output :=
      SubexpFieldRowValues.value now scope ls (BinaryArithmetic.toNat now.rank) :: now.output } =
      current m rank fuel (rows m scope ls (done + 1) ++ m.output) := by
    rw [hvalue]
    dsimp [now, out, current]
    rw [rows_succ]
    simp only [List.cons_append]
  have he' : Eval body t (resting m regs rank fuel out) e := by
    rw [hmodel] at he
    simpa only [body, now, resting, e] using he
  have hdnext : done + 1 ≤ count := by omega
  have hdec := value_decrement hp
  have hripple := ripple_length_le true rank
  have hInv : Invariant m scope ls count fuelWidth (nextState ports e) := by
    rw [show e = resting m SubexpFieldRowProgram.zeroRegs rank fuel
      (rows m scope ls (done + 1) ++ m.output) from rfl, next_resting]
    refine ⟨_, ripple true rank, ripple false fuel, done + 1, rfl, hdnext, ?_, ?_, ?_, ?_⟩
    · rw [value_increment, hcur]
    · omega
    · omega
    · exact (decrement_length hp).trans hfwidth
  refine ⟨t, e, he', rfl, rfl, rfl, hInv, ?_⟩
  exact ht.trans (callback_bound m scope ls hv rank fuel out count (by omega))

/-- Complete table enumeration with explicitly supplied binary fuel. The fuel
is tied to p^arity by `table_runsIn`; setup is an actual separate program. -/
theorem enumerate_runsIn {D n : ℕ} (m : Masters) (scope : List (Fin D))
    (ls : List (SAT.Literal (Fin n))) (hv : Valid m scope ls)
    (regs : Fin 8 → Bool) (fuel : List Bool) (count : ℕ) (hcount : value fuel = count) :
    ∃ finalRegs rank remaining,
      RunsIn program
        (SubexpEnumerationSchedule.programBudget ports (fun _ => callbackBound m scope ls count)
          (resting m regs [] fuel m.output))
        ((resting m regs [] fuel m.output).withPC (some program.entry))
        ((resting m finalRegs rank remaining (rows m scope ls count ++ m.output)).withPC none) ∧
      value rank = count ∧ value remaining = 0 ∧ rank.length ≤ count ∧
        remaining.length = fuel.length := by
  have hstart : Invariant m scope ls count fuel.length
      (testResult ports (resting m regs [] fuel m.output)) := by
    rw [test_resting]
    refine ⟨(testResult ports (resting m regs [] fuel m.output)).regs,
      [], fuel, 0, ?_, by omega, rfl, ?_, ?_, rfl⟩
    · simp only [rows_zero, List.nil_append]
    · simpa only [Nat.sub_zero] using hcount
    · simpa only [List.length_nil, Nat.zero_add, hcount] using (Nat.le_refl count)
  obtain ⟨e, hInv, he, hcur, hrem, hs⟩ := SubexpEnumerationSchedule.program_runsIn
    ports body (Invariant m scope ls count fuel.length) (fun _ => callbackBound m scope ls count)
    (body_step m scope ls hv count fuel.length) (resting m regs [] fuel m.output) hstart rfl
  rcases hInv with ⟨rf, rank, remaining, done, rfl, hdone, hrank, hremaining, hwidth, hfwidth⟩
  change value remaining = 0 at hrem
  have heq : done = count := by omega
  refine ⟨rf, rank, remaining, ?_, hrank.trans heq, hrem, by omega, hfwidth⟩
  simpa only [program, heq] using he

/-- The table has exactly p^arity rows, with no enumeration of all D labels. -/
theorem table_runsIn {D n : ℕ} (m : Masters) (scope : List (Fin D))
    (ls : List (SAT.Literal (Fin n))) (hv : Valid m scope ls)
    (regs : Fin 8 → Bool) (fuel : List Bool)
    (hfuel : value fuel = BinaryArithmetic.toNat m.modulus ^ scope.length) :
    ∃ finalRegs rank remaining,
      RunsIn program
        (SubexpEnumerationSchedule.programBudget ports
          (fun _ => callbackBound m scope ls (BinaryArithmetic.toNat m.modulus ^ scope.length))
          (resting m regs [] fuel m.output))
        ((resting m regs [] fuel m.output).withPC (some program.entry))
        ((resting m finalRegs rank remaining
          (rows m scope ls (BinaryArithmetic.toNat m.modulus ^ scope.length) ++ m.output)).withPC none) ∧
      value rank = BinaryArithmetic.toNat m.modulus ^ scope.length ∧ value remaining = 0 ∧
        rank.length ≤ BinaryArithmetic.toNat m.modulus ^ scope.length ∧
        remaining.length = fuel.length :=
  enumerate_runsIn m scope ls hv regs fuel _ hfuel

/-- A closed allowance when the supplied fuel has a known word-width bound.
The local row count remains explicit in both the callback and loop costs. -/
def enumerationBound {D n : ℕ} (m : Masters) (scope : List (Fin D))
    (ls : List (SAT.Literal (Fin n))) (count fuelWidth : ℕ) : ℕ :=
  8 * fuelWidth + 8 +
    (count * (callbackBound m scope ls count + 8 * count + 16 * fuelWidth + 24) + 1)

theorem programBudget_le {D n : ℕ} (m : Masters) (scope : List (Fin D))
    (ls : List (SAT.Literal (Fin n))) (regs : Fin 8 → Bool)
    (fuel output : List Bool) (count fuelWidth : ℕ)
    (hcount : value fuel = count) (hwidth : fuel.length ≤ fuelWidth) :
    SubexpEnumerationSchedule.programBudget ports
      (fun _ => callbackBound m scope ls count) (resting m regs [] fuel output) ≤
      enumerationBound m scope ls count fuelWidth := by
  have hl := SubexpEnumerationSchedule.loopBudget_le
    (fun _ => callbackBound m scope ls count) 0 count count fuel.length
    (callbackBound m scope ls count) (by intro i hi; exact Nat.le_refl _)
  change 8 * fuel.length + 8 + SubexpEnumerationSchedule.loopBudget
      (fun _ => callbackBound m scope ls count) 0 (value fuel) (0 + value fuel)
      fuel.length ≤ _
  rw [hcount, Nat.zero_add]
  calc
    _ ≤ 8 * fuel.length + 8 +
        (count * (callbackBound m scope ls count + 8 * count + 16 * fuel.length + 24) + 1) :=
      Nat.add_le_add_left hl _
    _ ≤ enumerationBound m scope ls count fuelWidth := by
      unfold enumerationBound
      gcongr

end SubexponentialSAT.SubexpFieldTableEnumeration

end OAI.Algorithms
