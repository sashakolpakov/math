import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms
import OAI.Algorithms.SubexponentialSAT.RecordPrograms

namespace OAI.Algorithms

/-!
# A fixed program gathering runtime-selected rows

The packed assignment is on stack 0 and its unary row width on stack 3.
Stack 8 contains `ProgramEncoding.encodeRecords` of unary index words.
The program preserves the assignment and width and writes the selected rows,
in plan order, to stack 1. All widths and indices are stack data.
-/

namespace SubexponentialSAT.Subexp.GatherProgram

open BitProgram StackRoutines StructuredCalls

def ports : RecordPrograms.Ports 3 10 where
  tag := 0
  present := 1
  found := 2
  source := 8
  payload := 2
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

/-- The existing eight-stack persistent lookup occupies the first eight ports. -/
def lookupPort : Fin 8 → Fin 10 := Fin.castAdd 2

theorem lookupPort_injective : Function.Injective lookupPort := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 10 => x.val) h)

abbrev lookup : Cmd 3 10 :=
  .call (ProgramLinking.liftProgram
    (ArrayUpdatePrograms.readProgram (0 : Fin 3) 1) id lookupPort)

/-- The parser supplies a reversed unary index. Only its length is read.
Each selected row is reversed into the growing accumulator on stack 9. -/
abbrev callback : Cmd 3 10 :=
  .seq lookup (.seq (.call (transferProgram (1 : Fin 10) 9 (0 : Fin 3) 1))
    (RecordPrograms.atom (.set 1 true)))

abbrev command : Cmd 3 10 :=
  .seq (RecordPrograms.iterate ports callback)
    (.call (transferProgram (9 : Fin 10) 1 (0 : Fin 3) 1))

abbrev program : Program 3 10 (StructuredCalls.size command + 1) :=
  StructuredCalls.compiled command 8 1

def indexRecords (plan : List ℕ) : List (List Bool) :=
  plan.map (fun i => List.replicate i true)

def gathered (rows : List (List Bool)) (plan : List ℕ) : List Bool :=
  plan.flatMap (fun i => rows.getD i [])

def baseState (array width acc : List Bool) : State 3 10 :=
  ⟨fun _ => false,
   fun j => if j = 0 then array else if j = 3 then width else if j = 9 then acc else []⟩

def inputState (rows : List (List Bool)) (width : List Bool) (plan : List ℕ) : State 3 10 :=
  RecordPrograms.state ports (baseState rows.flatten width []) false false false
    (ProgramEncoding.encodeRecords (indexRecords plan)) []

def outputState (rows : List (List Bool)) (width : List Bool) (plan : List ℕ) : State 3 10 :=
  ⟨fun _ => false,
   fun j => if j = 0 then rows.flatten else if j = 3 then width
     else if j = 1 then gathered rows plan else []⟩

private theorem transfer_eval (src dst : Fin 10) (hsd : src ≠ dst)
    (regs : Fin 3 → Bool) (stk : Stacks (Fin 10)) :
    Eval (.call (transferProgram src dst (0 : Fin 3) 1)) (3 * (stk src).length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs 0 1 none, transferStacks src dst stk⟩ := by
  apply Eval.call
  have t := halt_after_trace _
    (transferProgram_trace src dst (0 : Fin 3) 1 hsd (by decide) regs stk) 3 rfl rfl
  simpa [StructuredProgram.State.withPC, transferResult, transferProgram, Nat.add_assoc] using t

private theorem embed_lookup_input (a : State 3 10) :
    embedState id lookupPort a ⟨a.regs, a.stacks ∘ lookupPort⟩ = a := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext j
    exact embedState_register id lookupPort a _ Function.injective_id j
  · funext j
    by_cases hj : j.val < 8
    · let i : Fin 8 := ⟨j.val, hj⟩
      have hi : lookupPort i = j := Fin.ext rfl
      rw [← hi]
      exact embedState_stack id lookupPort a _ lookupPort_injective i
    · exact embedState_stack_frame id lookupPort a _ j (by
        rintro ⟨i, hi⟩
        have hv := congrArg Fin.val hi
        exact hj (hv ▸ i.isLt))

private theorem embed_lookup_output (a : State 3 10) (row : List Bool) :
    embedState id lookupPort a
      ⟨readRegs a.regs 0 1 none, ArrayUpdatePrograms.readStacks row (a.stacks ∘ lookupPort)⟩ =
      ⟨readRegs a.regs 0 1 none,
        Function.update (Function.update a.stacks 2 []) 1 (row ++ a.stacks 1)⟩ := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext j
    exact embedState_register id lookupPort a _ Function.injective_id j
  · funext j
    by_cases hj : j.val < 8
    · let i : Fin 8 := ⟨j.val, hj⟩
      have hi : lookupPort i = j := Fin.ext rfl
      rw [← hi, lookupPort_injective.extend_apply]
      clear hi
      clear_value i
      clear hj j
      fin_cases i <;> simp [ArrayUpdatePrograms.readStacks, lookupPort]
    · rw [Function.extend_apply' _ _ _ (by
        rintro ⟨i, hi⟩
        have hv := congrArg Fin.val hi
        exact hj (hv ▸ i.isLt))]
      have h1 : j ≠ 1 := by intro h; subst j; norm_num at hj
      have h2 : j ≠ 2 := by intro h; subst j; norm_num at hj
      simp [h1, h2]

theorem lookup_eval (earlier : List (List Bool)) (row rest width index : List Bool)
    (a : State 3 10)
    (ha : a.stacks 0 = earlier.flatten ++ (row ++ rest))
    (hw : a.stacks 3 = width) (hi : a.stacks 2 = index)
    (hil : index.length = earlier.length)
    (hrows : ∀ r ∈ earlier, r.length = width.length) (hr : row.length = width.length)
    (h4 : a.stacks 4 = []) (h5 : a.stacks 5 = [])
    (h6 : a.stacks 6 = []) (h7 : a.stacks 7 = []) :
    Eval lookup (earlier.length * (14 * width.length + 10) + 15 * width.length + 16) a
      ⟨readRegs a.regs 0 1 none,
        Function.update (Function.update a.stacks 2 []) 1 (row ++ a.stacks 1)⟩ := by
  have t := ArrayUpdatePrograms.readProgram_trace (0 : Fin 3) 1 (by decide)
    earlier row rest width index a.regs (a.stacks ∘ lookupPort)
    ha hw hi hil hrows hr h4 h5 h6 h7
  have h := eval_call_lifted (ArrayUpdatePrograms.readProgram (0 : Fin 3) 1)
    id lookupPort a Function.injective_id lookupPort_injective
    (a := ⟨a.regs, a.stacks ∘ lookupPort⟩)
    (b := ⟨readRegs a.regs 0 1 none,
      ArrayUpdatePrograms.readStacks row (a.stacks ∘ lookupPort)⟩) t
  simpa only [embed_lookup_input, embed_lookup_output, lookup] using h

theorem callback_eval (earlier : List (List Bool)) (row rest width bits tail acc : List Bool)
    (hil : bits.length = earlier.length)
    (hrows : ∀ r ∈ earlier, r.length = width.length) (hr : row.length = width.length) :
    Eval callback (earlier.length * (14 * width.length + 10) + 18 * width.length + 20)
      (RecordPrograms.state ports (baseState (earlier.flatten ++ (row ++ rest)) width acc)
        false true false tail bits.reverse)
      (RecordPrograms.state ports
        (baseState (earlier.flatten ++ (row ++ rest)) width (row.reverse ++ acc))
        false true false tail []) := by
  let a := RecordPrograms.state ports
    (baseState (earlier.flatten ++ (row ++ rest)) width acc) false true false tail bits.reverse
  let b : State 3 10 := ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update a.stacks 2 []) 1 (row ++ a.stacks 1)⟩
  have hl := lookup_eval earlier row rest width bits.reverse a
    (by simp [a, ports, RecordPrograms.state, baseState])
    (by simp [a, ports, RecordPrograms.state, baseState])
    (by simp [a, ports, RecordPrograms.state, baseState])
    (by simpa using hil) hrows hr
    (by simp [a, ports, RecordPrograms.state, baseState])
    (by simp [a, ports, RecordPrograms.state, baseState])
    (by simp [a, ports, RecordPrograms.state, baseState])
    (by simp [a, ports, RecordPrograms.state, baseState])
  have ht := transfer_eval (1 : Fin 10) 9 (by decide) b.regs b.stacks
  have hfinal : (⟨readRegs b.regs 0 1 none, transferStacks 1 9 b.stacks⟩ : State 3 10) =
      RecordPrograms.state ports
        (baseState (earlier.flatten ++ (row ++ rest)) width (row.reverse ++ acc))
        false false false tail [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      fin_cases j <;> simp [a, b, ports, RecordPrograms.state, baseState, readRegs]
    · funext j
      fin_cases j <;> simp [a, b, ports, RecordPrograms.state, baseState, transferStacks]
  rw [hfinal] at ht
  have hs : Eval (RecordPrograms.atom (.set (1 : Fin 3) true)) 1
      (RecordPrograms.state ports
        (baseState (earlier.flatten ++ (row ++ rest)) width (row.reverse ++ acc))
        false false false tail [])
      (RecordPrograms.state ports
        (baseState (earlier.flatten ++ (row ++ rest)) width (row.reverse ++ acc))
        false true false tail []) := by
    have he : (StructuredProgram.Atom.set (1 : Fin 3) true).eval
        (RecordPrograms.state ports
          (baseState (earlier.flatten ++ (row ++ rest)) width (row.reverse ++ acc))
          false false false tail []) =
        RecordPrograms.state ports
          (baseState (earlier.flatten ++ (row ++ rest)) width (row.reverse ++ acc))
          false true false tail [] := by
      apply congrArg₂ StructuredProgram.State.mk
      · funext j
        fin_cases j <;> simp [ StructuredProgram.Atom.instr, execInstr,
          ports, RecordPrograms.state, baseState]
      · rfl
    rw [← he]
    exact .base (.atom _ _)
  have t := hl.seq (ht.seq hs)
  dsimp [callback]
  convert t using 1 ; simp [a, b, ports, RecordPrograms.state, baseState, hr] ; omega

theorem row_decomposition (rows : List (List Bool)) (i : ℕ) (hi : i < rows.length) :
    rows.flatten = (rows.take i).flatten ++
      (rows.getD i [] ++ (rows.drop (i + 1)).flatten) := by
  have hs : rows.take i ++ rows.getD i [] :: rows.drop (i + 1) = rows := by
    rw [List.getD_eq_getElem rows [] hi, List.cons_getElem_drop_succ]
    exact List.take_append_drop i rows
  simpa only [List.flatten_append, List.flatten_cons] using congrArg List.flatten hs.symm

theorem callback_index_eval (rows : List (List Bool)) (width bits tail acc : List Bool)
    (hi : bits.length < rows.length)
    (hrows : ∀ row ∈ rows, row.length = width.length) :
    Eval callback (bits.length * (14 * width.length + 10) + 18 * width.length + 20)
      (RecordPrograms.state ports (baseState rows.flatten width acc)
        false true false tail bits.reverse)
      (RecordPrograms.state ports
        (baseState rows.flatten width ((rows.getD bits.length []).reverse ++ acc))
        false true false tail []) := by
  have ht : ∀ row ∈ rows.take bits.length, row.length = width.length := by
    intro row hr
    exact hrows row (List.mem_of_mem_take hr)
  have hr : (rows.getD bits.length []).length = width.length := by
    rw [List.getD_eq_getElem rows [] hi]
    exact hrows _ (List.getElem_mem hi)
  have h := callback_eval (rows.take bits.length) (rows.getD bits.length [])
    (rows.drop (bits.length + 1)).flatten width bits tail acc
    (by simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]) ht hr
  simpa only [← row_decomposition rows bits.length hi,
    List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)] using h

/-- An exact per-record callback budget in actual bit-program instructions. -/
def callbackCost (width : ℕ) (bits : List Bool) : ℕ :=
  bits.length * (14 * width + 10) + 18 * width + 20

def invariant (rows : List (List Bool)) (width : List Bool) (a : State 3 10) : Prop :=
  ∃ acc, a = baseState rows.flatten width acc

def effect (rows : List (List Bool)) (bits : List Bool) (a b : State 3 10) : Prop :=
  b.stacks 9 = (rows.getD bits.length []).reverse ++ a.stacks 9

theorem gathered_length (rows : List (List Bool)) (plan : List ℕ) (w : ℕ)
    (hrows : ∀ row ∈ rows, row.length = w) (hplan : ∀ i ∈ plan, i < rows.length) :
    (gathered rows plan).length = plan.length * w := by
  induction plan with
  | nil => simp [gathered]
  | cons i plan ih =>
      have hi := hplan i (by simp)
      have htail : ∀ j ∈ plan, j < rows.length := fun j hj => hplan j (by simp [hj])
      have hr : (rows.getD i []).length = w := by
        rw [List.getD_eq_getElem rows [] hi]
        exact hrows _ (List.getElem_mem hi)
      change (rows.getD i [] ++ gathered rows plan).length = (plan.length + 1) * w
      rw [List.length_append, hr, ih htail]
      ring

theorem accumulator_fold (rows : List (List Bool)) (plan : List ℕ) (acc : List Bool) :
    (indexRecords plan).foldl
      (fun out bits => (rows.getD bits.length []).reverse ++ out) acc =
      (gathered rows plan).reverse ++ acc := by
  induction plan generalizing acc with
  | nil => simp [indexRecords, gathered]
  | cons i plan ih =>
      simpa only [indexRecords, List.map_cons, List.foldl_cons, List.length_replicate,
        gathered, List.flatMap_cons, List.reverse_append, List.append_assoc] using
        ih ((rows.getD i []).reverse ++ acc)

theorem indexRecords_valid (rows : List (List Bool)) (plan : List ℕ)
    (hplan : ∀ i ∈ plan, i < rows.length) :
    ∀ bits ∈ indexRecords plan, bits.length < rows.length := by
  intro bits hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  simpa using hplan i hi

/-- The concrete trace budget, including the final reversal and halt. -/
def traceCost (rows : List (List Bool)) (width : ℕ) (plan : List ℕ) : ℕ :=
  7 + RecordPrograms.budget (callbackCost width) (indexRecords plan) +
    3 * (gathered rows plan).length

theorem iterator_budget_eq (width : ℕ) (plan : List ℕ) :
    RecordPrograms.budget (callbackCost width) (indexRecords plan) =
      (14 * width + 16) * plan.sum + (18 * width + 27) * plan.length := by
  induction plan with
  | nil => simp [RecordPrograms.budget, indexRecords]
  | cons i plan ih =>
      change 6 * (List.replicate i true).length + callbackCost width (List.replicate i true) +
        7 + RecordPrograms.budget (callbackCost width) (indexRecords plan) = _
      rw [ih]
      simp only [List.length_replicate, callbackCost, List.sum_cons, List.length_cons]
      ring

theorem plan_sum_le (plan : List ℕ) (n : ℕ) (hp : ∀ i ∈ plan, i < n) :
    plan.sum ≤ plan.length * n := by
  induction plan with
  | nil => simp
  | cons i plan ih =>
      have hi := hp i (by simp)
      have ht := ih (fun j hj => hp j (by simp [hj]))
      simp only [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem traceCost_le (rows : List (List Bool)) (width : ℕ) (plan : List ℕ)
    (hrows : ∀ row ∈ rows, row.length = width) (hplan : ∀ i ∈ plan, i < rows.length) :
    traceCost rows width plan ≤
      7 + plan.length * (rows.length * (14 * width + 16) + 21 * width + 27) := by
  have hs := Nat.mul_le_mul_left (14 * width + 16) (plan_sum_le plan rows.length hplan)
  rw [traceCost, iterator_budget_eq, gathered_length rows plan width hrows hplan]
  calc
    _ ≤ 7 + ((14 * width + 16) * (plan.length * rows.length) +
        (18 * width + 27) * plan.length) + 3 * (plan.length * width) := by omega
    _ = _ := by ring

theorem traceCost_le_cubic (rows : List (List Bool)) (width : ℕ) (plan : List ℕ)
    (hrows : ∀ row ∈ rows, row.length = width) (hplan : ∀ i ∈ plan, i < rows.length) :
    traceCost rows width plan ≤ 100 * (rows.length + width + plan.length + 1)^3 := by
  let t := rows.length + width + plan.length + 1
  have ht : 1 ≤ t := by dsimp [t]; omega
  have hr : rows.length ≤ t := by dsimp [t]; omega
  have hw : width ≤ t := by dsimp [t]; omega
  have hp : plan.length ≤ t := by dsimp [t]; omega
  have hmono : 7 + plan.length * (rows.length * (14 * width + 16) + 21 * width + 27) ≤
      7 + t * (t * (14 * t + 16) + 21 * t + 27) := by gcongr
  have ht2 : t ≤ t^2 := by nlinarith
  have ht3 : t^2 ≤ t^3 := by
    have h := Nat.mul_le_mul_left (t*t) ht
    nlinarith
  exact (traceCost_le rows width plan hrows hplan).trans (hmono.trans (by
    change 7 + t * (t * (14 * t + 16) + 21 * t + 27) ≤ 100 * t^3
    nlinarith))

theorem encoded_plan_length (plan : List ℕ) :
    (ProgramEncoding.encodeRecords (indexRecords plan)).length =
      2 * plan.sum + 2 * plan.length + 1 := by
  rw [ProgramEncoding.encodeRecords_length]
  have hm : (indexRecords plan).map List.length = plan := by
    simp [indexRecords, List.map_map, Function.comp_def]
  rw [hm]
  simp [indexRecords]

theorem callback_contract (rows : List (List Bool)) (width : List Bool)
    (hrows : ∀ row ∈ rows, row.length = width.length) :
    RecordPrograms.CallbackContractWithOn ports callback (fun _ => false)
      (callbackCost width.length) (invariant rows width) (effect rows)
      (fun bits => bits.length < rows.length) := by
  intro bits tail base hi hinv
  obtain ⟨acc, rfl⟩ := hinv
  refine ⟨callbackCost width.length bits,
    baseState rows.flatten width ((rows.getD bits.length []).reverse ++ acc),
    le_rfl, ⟨_, rfl⟩, ?_, ?_⟩
  · simp [effect, baseState]
  · exact callback_index_eval rows width bits tail acc hi hrows

private theorem unread_false (records : List (List Bool)) (suffix : List Bool) :
    RecordPrograms.unread (fun _ => false) records suffix = suffix := by
  induction records with
  | nil => rfl
  | cons bits rest ih => simpa only [RecordPrograms.unread, Bool.false_eq_true, ite_false] using ih

private theorem any_false (records : List (List Bool)) :
    records.any (fun _ => false) = false := by
  induction records with
  | nil => rfl
  | cons bits rest ih => exact ih

/-- Execution of the single fixed command. The only input hypotheses are
uniform row widths and validity of the runtime plan indices. -/
theorem command_eval (rows : List (List Bool)) (width : List Bool) (plan : List ℕ)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hplan : ∀ i ∈ plan, i < rows.length) :
    ∃ n, n + 1 ≤ traceCost rows width.length plan ∧
      Eval command n (inputState rows width plan) (outputState rows width plan) := by
  obtain ⟨n, next, hn, hnext, history, run⟩ := RecordPrograms.iterate_run_with_on
    ports callback (fun _ => false) (callbackCost width.length) (invariant rows width)
    (effect rows) (fun bits => bits.length < rows.length)
    (callback_contract rows width hrows) (indexRecords plan) []
    (baseState rows.flatten width []) (indexRecords_valid rows plan hplan) ⟨[], rfl⟩
    false false false
  obtain ⟨acc, rfl⟩ := hnext
  have hacc : acc = (gathered rows plan).reverse := by
    have hh := history.fold_of_false (fun _ _ => rfl)
      (fun s => s.stacks 9)
      (fun out bits => (rows.getD bits.length []).reverse ++ out)
      (fun _ _ _ h => h)
    simpa only [baseState, ite_eq_left, ite_false, Fin.reduceEq, accumulator_fold,
      List.append_nil] using hh
  subst acc
  let middle := RecordPrograms.state ports
    (baseState rows.flatten width (gathered rows plan).reverse) false true false [] []
  have hrun : Eval (RecordPrograms.iterate ports callback) n
      (inputState rows width plan) middle := by
    simpa [inputState, middle, ProgramEncoding.encodeRecords, unread_false, any_false] using run
  have ht := transfer_eval (9 : Fin 10) 1 (by decide) middle.regs middle.stacks
  have hfinal : (⟨readRegs middle.regs 0 1 none,
      transferStacks 9 1 middle.stacks⟩ : State 3 10) = outputState rows width plan := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      fin_cases j <;> simp [middle, ports, RecordPrograms.state, baseState, readRegs]
    · funext j
      fin_cases j <;> simp [middle, ports, RecordPrograms.state, baseState,
        transferStacks]
  have ht' : Eval (.call (transferProgram (9 : Fin 10) 1 (0 : Fin 3) 1))
      (3 * (gathered rows plan).length + 3) middle (outputState rows width plan) := by
    rw [hfinal] at ht
    simpa [middle, ports, RecordPrograms.state, baseState] using ht
  refine ⟨n + (3 * (gathered rows plan).length + 3), ?_, hrun.seq ht'⟩
  dsimp [traceCost]
  omega

/-- The full, halted trace of the generated finite instruction table. -/
theorem program_run (rows : List (List Bool)) (width : List Bool) (plan : List ℕ)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hplan : ∀ i ∈ plan, i < rows.length) :
    RunsIn program (traceCost rows width.length plan)
      ((inputState rows width plan).withPC (some program.entry))
      ((outputState rows width plan).withPC none) := by
  obtain ⟨n, hn, h⟩ := command_eval rows width plan hrows hplan
  exact ⟨n + 1, hn, StructuredCalls.compiled_halt_trace h 8 1⟩

/-- A polynomial bound in actual serialized width and plan data. In particular,
even a zero-width array needs no unencoded row-count parameter in the bound. -/
theorem traceCost_le_serialized (rows : List (List Bool)) (width : ℕ) (plan : List ℕ)
    (hrows : ∀ row ∈ rows, row.length = width) (hplan : ∀ i ∈ plan, i < rows.length) :
    traceCost rows width plan ≤
      100 * (width + (ProgramEncoding.encodeRecords (indexRecords plan)).length + 1)^2 := by
  let t := width + (ProgramEncoding.encodeRecords (indexRecords plan)).length + 1
  have ht : 1 ≤ t := by dsimp [t]; omega
  have hw : width ≤ t := by dsimp [t]; omega
  have hs : plan.sum ≤ t := by dsimp [t]; rw [encoded_plan_length]; omega
  have hp : plan.length ≤ t := by dsimp [t]; rw [encoded_plan_length]; omega
  have heq : traceCost rows width plan =
      7 + (14 * width + 16) * plan.sum + (21 * width + 27) * plan.length := by
    rw [traceCost, iterator_budget_eq, gathered_length rows plan width hrows hplan]
    ring
  rw [heq]
  have hmono : 7 + (14 * width + 16) * plan.sum + (21 * width + 27) * plan.length ≤
      7 + (14 * t + 16) * t + (21 * t + 27) * t := by gcongr
  have ht2 : t ≤ t^2 := by nlinarith
  exact hmono.trans (by change _ ≤ 100 * t^2; nlinarith)

theorem program_run_serialized (rows : List (List Bool)) (width : List Bool) (plan : List ℕ)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hplan : ∀ i ∈ plan, i < rows.length) :
    RunsIn program
      (100 * (width.length + (ProgramEncoding.encodeRecords (indexRecords plan)).length + 1)^2)
      ((inputState rows width plan).withPC (some program.entry))
      ((outputState rows width plan).withPC none) := by
  obtain ⟨n, hn, h⟩ := program_run rows width plan hrows hplan
  exact ⟨n, hn.trans (traceCost_le_serialized rows width.length plan hrows hplan), h⟩

/-- Refinement to the project's primitive binary-machine transitions; the
compiler overhead is a constant of this fixed program. -/
theorem primitive_run (rows : List (List Bool)) (width : List Bool) (plan : List ℕ)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hplan : ∀ i ∈ plan, i < rows.length) :
    Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * traceCost rows width.length plan)
      (BitProgram.primitiveCfg program
        ((inputState rows width plan).withPC (some program.entry)))
      (BitProgram.primitiveCfg program ((outputState rows width plan).withPC none)) :=
  BitProgram.primitive_execution program (program_run rows width plan hrows hplan)

theorem primitive_run_serialized (rows : List (List Bool)) (width : List Bool) (plan : List ℕ)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hplan : ∀ i ∈ plan, i < rows.length) :
    Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program *
        (100 * (width.length + (ProgramEncoding.encodeRecords (indexRecords plan)).length + 1)^2))
      (BitProgram.primitiveCfg program
        ((inputState rows width plan).withPC (some program.entry)))
      (BitProgram.primitiveCfg program ((outputState rows width plan).withPC none)) :=
  BitProgram.primitive_execution program (program_run_serialized rows width plan hrows hplan)

@[simp] theorem inputState_array (rows : List (List Bool)) (width : List Bool) (plan : List ℕ) :
    (inputState rows width plan).stacks 0 = rows.flatten := by
  simp [inputState, ports, RecordPrograms.state, baseState]

@[simp] theorem inputState_width (rows : List (List Bool)) (width : List Bool) (plan : List ℕ) :
    (inputState rows width plan).stacks 3 = width := by
  simp [inputState, ports, RecordPrograms.state, baseState]

@[simp] theorem inputState_plan (rows : List (List Bool)) (width : List Bool) (plan : List ℕ) :
    (inputState rows width plan).stacks 8 = ProgramEncoding.encodeRecords (indexRecords plan) := by
  simp [inputState, ports, RecordPrograms.state, baseState]

@[simp] theorem outputState_array (rows : List (List Bool)) (width : List Bool) (plan : List ℕ) :
    (outputState rows width plan).stacks 0 = rows.flatten := by simp [outputState]

@[simp] theorem outputState_width (rows : List (List Bool)) (width : List Bool) (plan : List ℕ) :
    (outputState rows width plan).stacks 3 = width := by simp [outputState]

@[simp] theorem outputState_output (rows : List (List Bool)) (width : List Bool) (plan : List ℕ) :
    (outputState rows width plan).stacks 1 = gathered rows plan := by simp [outputState]

end SubexponentialSAT.Subexp.GatherProgram

end OAI.Algorithms
