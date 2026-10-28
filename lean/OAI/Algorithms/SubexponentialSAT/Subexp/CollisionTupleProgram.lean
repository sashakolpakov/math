import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CollisionStreamProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.PaddedCompletion

namespace OAI.Algorithms

/-!
# Streaming collisions from framed runtime tuples

The current word array and selected read plans are preserved. Each parsed
tuple is appended to the current array by actual transfer/copy routines, then
the fixed collision callback gathers the two types and emits one bit.
-/

namespace SubexponentialSAT.Subexp.CollisionTupleProgram

open BitProgram StackRoutines StructuredCalls

abbrev Data := StructuredProgram.State 8 18

def byteGather (table : List Bool) (width : ℕ) (plan : List ℕ) : List Bool :=
  plan.flatMap fun i => (table.drop (i * width)).take width

theorem slice_flatten (rows : List (List Bool)) (width : ℕ)
    (hrows : ∀ row ∈ rows, row.length = width) (i : ℕ) :
    (rows.flatten.drop (i * width)).take width = rows.getD i [] := by
  induction rows generalizing i with
  | nil => simp
  | cons row rows ih =>
    have hr := hrows row (by simp)
    have ht : ∀ r ∈ rows, r.length = width := fun r h => hrows r (by simp [h])
    cases i with
    | zero => simpa using (List.take_left' (l₁ := row) (l₂ := rows.flatten) hr)
    | succ i =>
      have hm : (i + 1) * width = row.length + i * width := by rw [hr]; ring
      rw [List.flatten_cons, hm, ← List.drop_drop, List.drop_left]
      simpa using ih ht i

theorem byteGather_flatten (rows : List (List Bool)) (width : ℕ)
    (hrows : ∀ row ∈ rows, row.length = width) (plan : List ℕ) :
    byteGather rows.flatten width plan = GatherProgram.gathered rows plan := by
  unfold byteGather GatherProgram.gathered
  apply congrArg (fun f : ℕ → List Bool => plan.flatMap f)
  funext i
  exact slice_flatten rows width hrows i

def leafBit (current : List Bool) (width : ℕ) (left right : List ℕ)
    (tuple : List Bool) : Bool :=
  decide (byteGather (current ++ tuple) width left = byteGather (current ++ tuple) width right)

theorem leafBit_eq_collision (current candidate : List (List Bool)) (width : ℕ)
    (hrows : ∀ row ∈ current ++ candidate, row.length = width) (left right : List ℕ) :
    leafBit current.flatten width left right candidate.flatten =
      CollisionStreamProgram.collisionBit (current ++ candidate) left right := by
  unfold leafBit CollisionStreamProgram.collisionBit
  rw [← List.flatten_append, byteGather_flatten _ _ hrows, byteGather_flatten _ _ hrows]

def ports : RecordPrograms.Ports 8 18 where
  tag := 5
  present := 6
  found := 7
  source := 16
  payload := 17
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

structure Frame where
  current : List Bool
  width : List Bool
  left : List ℕ
  right : List ℕ
  tail : List Bool

/-- Parser flags are false/true/false during a callback. All low registers are
scratch of the collision program. -/
def state (f : Frame) (table workLeft workRight stream payload : List Bool) : Data :=
  ⟨fun j => decide (j = 6), fun j =>
    if j = 0 then table else if j = 3 then f.width
    else if j = 8 then workLeft else if j = 10 then workRight else if j = 11 then stream
    else if j = 13 then f.current
    else if j = 14 then CollisionStreamProgram.planBytes f.left
    else if j = 15 then CollisionStreamProgram.planBytes f.right
    else if j = 16 then f.tail else if j = 17 then payload else []⟩

private theorem state_ext {r s : ℕ} {a b : StructuredProgram.State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; cases hr; cases hs; rfl

def lowRegs : Fin 5 → Fin 8 := Fin.castAdd 3
def lowStacks : Fin 13 → Fin 18 := Fin.castAdd 5

theorem lowRegs_injective : Function.Injective lowRegs := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 8 => k.val) h)

theorem lowStacks_injective : Function.Injective lowStacks := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 18 => k.val) h)

abbrev collision : Cmd 8 18 := .call (ProgramLinking.liftProgram
  CollisionStreamProgram.program lowRegs lowStacks)

private theorem embed_state (f : Frame) (table workLeft workRight stream : List Bool)
    (rows : List (List Bool)) (htable : rows.flatten = table) :
    embedState lowRegs lowStacks (state f table workLeft workRight stream [])
      (CollisionStreamProgram.stageState rows f.width [] [] workLeft workRight stream) =
        state f table workLeft workRight stream [] := by
  apply state_ext
  · funext j
    by_cases hj : j.val < 5
    · let i : Fin 5 := ⟨j.val, hj⟩
      have hi : lowRegs i = j := Fin.ext rfl
      rw [← hi, embedState_register _ _ _ _ lowRegs_injective]
      clear_value i
      fin_cases i <;> simp [lowRegs, state, CollisionStreamProgram.stageState]
    · rw [embedState_register_frame _ _ _ _ j (by
        rintro ⟨i, hi⟩; apply hj
        have he := congrArg Fin.val hi; exact he ▸ i.isLt)]
  · funext j
    by_cases hj : j.val < 13
    · let i : Fin 13 := ⟨j.val, hj⟩
      have hi : lowStacks i = j := Fin.ext rfl
      rw [← hi, embedState_stack _ _ _ _ lowStacks_injective]
      clear_value i
      fin_cases i <;> simp [lowStacks, state, CollisionStreamProgram.stageState, htable]
    · rw [embedState_stack_frame _ _ _ _ j (by
        rintro ⟨i, hi⟩; apply hj
        have he := congrArg Fin.val hi; exact he ▸ i.isLt)]

private theorem embed_output (f : Frame) (rows : List (List Bool)) (stream answer : List Bool) :
    embedState lowRegs lowStacks
      (state f rows.flatten (CollisionStreamProgram.planBytes f.left)
        (CollisionStreamProgram.planBytes f.right) stream [])
      (CollisionStreamProgram.outputState rows f.width answer) =
        state f rows.flatten [] [] answer [] := by
  apply state_ext
  · funext j
    by_cases hj : j.val < 5
    · let i : Fin 5 := ⟨j.val, hj⟩
      have hi : lowRegs i = j := Fin.ext rfl
      rw [← hi, embedState_register _ _ _ _ lowRegs_injective]
      clear_value i
      fin_cases i <;> simp [lowRegs, state, CollisionStreamProgram.outputState,
        CollisionStreamProgram.stageState]
    · rw [embedState_register_frame _ _ _ _ j (by
        rintro ⟨i, hi⟩; apply hj
        have he := congrArg Fin.val hi; exact he ▸ i.isLt)]
      rfl
  · funext j
    by_cases hj : j.val < 13
    · let i : Fin 13 := ⟨j.val, hj⟩
      have hi : lowStacks i = j := Fin.ext rfl
      rw [← hi, embedState_stack _ _ _ _ lowStacks_injective]
      clear_value i
      fin_cases i <;> simp [lowStacks, state, CollisionStreamProgram.outputState,
        CollisionStreamProgram.stageState]
    · rw [embedState_stack_frame _ _ _ _ j (by
        rintro ⟨i, hi⟩; apply hj
        have he := congrArg Fin.val hi; exact he ▸ i.isLt)]
      have h0 : j ≠ 0 := by intro h; subst j; exact hj (by decide)
      have h3 : j ≠ 3 := by intro h; subst j; exact hj (by decide)
      have h8 : j ≠ 8 := by intro h; subst j; exact hj (by decide)
      have h10 : j ≠ 10 := by intro h; subst j; exact hj (by decide)
      have h11 : j ≠ 11 := by intro h; subst j; exact hj (by decide)
      simp [state, h0, h3, h8, h10, h11]

theorem collision_eval (f : Frame) (rows : List (List Bool)) (stream : List Bool)
    (hrows : ∀ row ∈ rows, row.length = f.width.length)
    (hl : ∀ i ∈ f.left, i < rows.length) (hr : ∀ i ∈ f.right, i < rows.length) :
    ∃ n ≤ CollisionStreamProgram.planBudget f.width.length f.left f.right,
      Eval collision n
        (state f rows.flatten (CollisionStreamProgram.planBytes f.left)
          (CollisionStreamProgram.planBytes f.right) stream [])
        (state f rows.flatten [] []
          (CollisionStreamProgram.collisionBit rows f.left f.right :: stream) []) := by
  obtain ⟨n, hn, ht⟩ := CollisionStreamProgram.program_trace rows f.width f.left f.right
    stream hrows hl hr
  rw [CollisionStreamProgram.sourceBudget_eq_planBudget rows f.width.length f.left f.right
    hrows hl hr] at hn
  have he := eval_call_lifted CollisionStreamProgram.program lowRegs lowStacks
    (state f rows.flatten (CollisionStreamProgram.planBytes f.left)
      (CollisionStreamProgram.planBytes f.right) stream []) lowRegs_injective lowStacks_injective ht
  rw [show CollisionStreamProgram.inputState rows f.width f.left f.right stream =
    CollisionStreamProgram.stageState rows f.width [] [] (CollisionStreamProgram.planBytes f.left)
      (CollisionStreamProgram.planBytes f.right) stream from rfl,
    embed_state f _ _ _ _ rows rfl, embed_output] at he
  exact ⟨n, hn, he⟩

def transferState (d : Data) (src dst : Fin 18) : Data :=
  ⟨readRegs d.regs 0 1 none, transferStacks src dst d.stacks⟩

def copyState (d : Data) (src dst : Fin 18) : Data :=
  ⟨readRegs d.regs 0 1 none, copyStacks src dst d.stacks⟩

def clearState (d : Data) (src : Fin 18) : Data :=
  ⟨readRegs d.regs 0 1 none, clearStacks src d.stacks⟩

private theorem transfer_eval (d : Data) (src dst : Fin 18) (hsd : src ≠ dst) :
    Eval (.call (transferProgram src dst (0 : Fin 8) 1))
      (3 * (d.stacks src).length + 3) d (transferState d src dst) := by
  apply Eval.call
  have h := halt_after_trace _
    (transferProgram_trace src dst (0 : Fin 8) 1 hsd (by decide) d.regs d.stacks) 3 rfl rfl
  simpa [transferState, StructuredProgram.State.withPC, transferResult, transferProgram,
    Nat.add_assoc] using h

private theorem copy_eval (d : Data) (src dst : Fin 18)
    (hsd : src ≠ dst) (hs4 : src ≠ 4) (h4d : (4 : Fin 18) ≠ dst)
    (ht : d.stacks 4 = []) :
    Eval (.call (copyProgram src dst (4 : Fin 18) (0 : Fin 8) 1))
      (7 * (d.stacks src).length + 5) d (copyState d src dst) := by
  apply Eval.call
  have h := halt_after_trace _
    (copyProgram_trace src dst (4 : Fin 18) (0 : Fin 8) 1 hsd hs4 h4d
      (by decide) d.regs d.stacks ht) 7 rfl rfl
  simpa [copyState, StructuredProgram.State.withPC, copyResult, copyProgram,
    Nat.add_assoc] using h

private theorem clear_eval (d : Data) (src : Fin 18) :
    Eval (.call (clearProgram src (0 : Fin 8) 1))
      (2 * (d.stacks src).length + 3) d (clearState d src) := by
  apply Eval.call
  have h := halt_after_trace _ (clearProgram_trace src (0 : Fin 8) 1 d.regs d.stacks) 2 rfl rfl
  simpa [clearState, StructuredProgram.State.withPC, clearResult, clearProgram,
    Nat.add_assoc] using h

abbrev callback : Cmd 8 18 :=
  .seq (.call (transferProgram 17 0 0 1))
    (.seq (.call (copyProgram 13 0 4 0 1))
      (.seq (.call (copyProgram 14 8 4 0 1))
        (.seq (.call (copyProgram 15 10 4 0 1))
          (.seq collision (.call (clearProgram 0 0 1))))))

def callbackCost (current : List Bool) (width : ℕ) (left right : List ℕ)
    (tuple : List Bool) : ℕ :=
  5 * tuple.length + 9 * current.length +
    7 * (CollisionStreamProgram.planBytes left).length +
    7 * (CollisionStreamProgram.planBytes right).length +
    CollisionStreamProgram.planBudget width left right + 21

theorem callback_eval (current candidate : List (List Bool)) (width : List Bool)
    (left right : List ℕ) (tail stream : List Bool)
    (hrows : ∀ row ∈ current ++ candidate, row.length = width.length)
    (hl : ∀ i ∈ left, i < (current ++ candidate).length)
    (hr : ∀ i ∈ right, i < (current ++ candidate).length) :
    let f : Frame := ⟨current.flatten, width, left, right, tail⟩
    ∃ n ≤ callbackCost current.flatten width.length left right candidate.flatten,
      Eval callback n (state f [] [] [] stream candidate.flatten.reverse)
        (state f [] [] [] (leafBit current.flatten width.length left right candidate.flatten :: stream) []) := by
  dsimp only
  let f : Frame := ⟨current.flatten, width, left, right, tail⟩
  let d0 := state f [] [] [] stream candidate.flatten.reverse
  let d1 := transferState d0 17 0
  let d2 := copyState d1 13 0
  let d3 := copyState d2 14 8
  let d4 := copyState d3 15 10
  have he : d4 = state f (current ++ candidate).flatten
      (CollisionStreamProgram.planBytes left) (CollisionStreamProgram.planBytes right) stream [] := by
    apply state_ext
    · funext j; fin_cases j <;> simp [d4, d3, d2, d1, d0, f, state, copyState,
        transferState, readRegs]
    · funext j; fin_cases j <;> simp [d4, d3, d2, d1, d0, f, state, copyState,
        transferState, copyStacks, transferStacks]
  have t0 := transfer_eval d0 17 0 (by decide)
  have t1 := copy_eval d1 13 0 (by decide) (by decide) (by decide)
    (by simp [d1, d0, f, transferState, state, transferStacks])
  have t2 := copy_eval d2 14 8 (by decide) (by decide) (by decide)
    (by simp [d2, d1, d0, f, copyState, transferState, state, copyStacks, transferStacks])
  have t3 := copy_eval d3 15 10 (by decide) (by decide) (by decide)
    (by simp [d3, d2, d1, d0, f, copyState, transferState, state, copyStacks, transferStacks])
  obtain ⟨n, hn, t4⟩ := collision_eval f (current ++ candidate) stream hrows hl hr
  rw [← he] at t4
  let d5 := state f (current ++ candidate).flatten [] []
    (CollisionStreamProgram.collisionBit (current ++ candidate) left right :: stream) []
  have t5 := clear_eval d5 0
  have hf : clearState d5 0 = state f [] [] []
      (leafBit current.flatten width.length left right candidate.flatten :: stream) [] := by
    rw [leafBit_eq_collision current candidate width.length hrows left right]
    apply state_ext
    · funext j; fin_cases j <;> simp [d5, state, clearState, readRegs]
    · funext j; fin_cases j <;> simp [d5, state, clearState, clearStacks]
  rw [hf] at t5
  have t := t0.seq (t1.seq (t2.seq (t3.seq (t4.seq t5))))
  refine ⟨_, ?_, t⟩
  simp [d5, d3, d2, d1, d0, f, state, copyState, transferState,
    copyStacks, transferStacks, callbackCost] at hn ⊢
  omega

def baseState (current : List Bool) (width : List Bool) (left right : List ℕ)
    (stream : List Bool) : Data :=
  state ⟨current, width, left, right, []⟩ [] [] [] stream []

def invariant (current : List Bool) (width : List Bool) (left right : List ℕ)
    (d : Data) : Prop := ∃ stream, d = baseState current width left right stream

/-- This schema only describes the serialized tuple's row widths and the
validity of the two numeric plans. It places no condition on the answer bit. -/
def validPayload (current : List (List Bool)) (width : ℕ) (left right : List ℕ)
    (bits : List Bool) : Prop :=
  ∃ candidate : List (List Bool), candidate.flatten = bits ∧
    (∀ row ∈ current ++ candidate, row.length = width) ∧
    (∀ i ∈ left, i < (current ++ candidate).length) ∧
    (∀ i ∈ right, i < (current ++ candidate).length)

def effect (current : List Bool) (width : ℕ) (left right : List ℕ)
    (bits : List Bool) (a b : Data) : Prop :=
  b.stacks 11 = leafBit current width left right bits :: a.stacks 11

private theorem parser_state_eq (current width : List Bool) (left right : List ℕ)
    (stream tail payload : List Bool) :
    RecordPrograms.state ports (baseState current width left right stream)
      false true false tail payload =
      state ⟨current, width, left, right, tail⟩ [] [] [] stream payload := by
  apply state_ext
  · funext j; fin_cases j <;> simp [RecordPrograms.state, ports, baseState, state]
  · funext j; fin_cases j <;> simp [RecordPrograms.state, ports, baseState, state]

theorem callback_contract (current : List (List Bool)) (width : List Bool)
    (left right : List ℕ) :
    RecordPrograms.CallbackContractWithOn ports callback (fun _ => false)
      (callbackCost current.flatten width.length left right)
      (invariant current.flatten width left right)
      (effect current.flatten width.length left right)
      (validPayload current width.length left right) := by
  intro bits tail base hv hi
  obtain ⟨candidate, rfl, hrows, hl, hr⟩ := hv
  obtain ⟨stream, rfl⟩ := hi
  obtain ⟨n, hn, he⟩ := callback_eval current candidate width left right tail stream hrows hl hr
  refine ⟨n, baseState current.flatten width left right
      (leafBit current.flatten width.length left right candidate.flatten :: stream), hn,
      ⟨_, rfl⟩, ?_, ?_⟩
  · simp [effect, baseState, state]
  · simpa only [parser_state_eq] using he

abbrev command : Cmd 8 18 := RecordPrograms.iterate ports callback

abbrev program : Program 8 18 (StructuredCalls.size command + 1) :=
  StructuredCalls.compiled command 16 11

def inputState (current width : List Bool) (left right : List ℕ)
    (tuples : List (List Bool)) (stream : List Bool) : Data :=
  RecordPrograms.state ports (baseState current width left right stream)
    false false false (ProgramEncoding.encodeRecords tuples) []

def streamed (current : List Bool) (width : ℕ) (left right : List ℕ)
    (tuples : List (List Bool)) (stream : List Bool) : List Bool :=
  tuples.foldl (fun acc bits => leafBit current width left right bits :: acc) stream

theorem streamed_eq_reverse_map (current : List Bool) (width : ℕ) (left right : List ℕ)
    (tuples : List (List Bool)) (stream : List Bool) :
    streamed current width left right tuples stream =
      (tuples.map (leafBit current width left right)).reverse ++ stream := by
  induction tuples generalizing stream with
  | nil => rfl
  | cons bits tuples ih =>
    simp only [streamed, List.foldl_cons]
    change streamed current width left right tuples
      (leafBit current width left right bits :: stream) = _
    rw [ih]
    simp

def sourceBudget (current : List Bool) (width : ℕ) (left right : List ℕ)
    (tuples : List (List Bool)) : ℕ :=
  4 + RecordPrograms.budget (callbackCost current width left right) tuples

def fixedCost (current : List Bool) (width : ℕ) (left right : List ℕ) : ℕ :=
  9 * current.length + 7 * (CollisionStreamProgram.planBytes left).length +
    7 * (CollisionStreamProgram.planBytes right).length +
    CollisionStreamProgram.planBudget width left right + 21

theorem sourceBudget_le_serialized (current : List Bool) (width : ℕ)
    (left right : List ℕ) (tuples : List (List Bool)) :
    sourceBudget current width left right tuples ≤
      (fixedCost current width left right + 22) *
        ((ProgramEncoding.encodeRecords tuples).length + 1) := by
  have h := RecordPrograms.program_budget_le_input (callbackCost current width left right)
    tuples 5 (fixedCost current width left right) (by
      intro bits _
      simp [callbackCost, fixedCost]
      omega)
  have hk : 5 + fixedCost current width left right + 17 =
      fixedCost current width left right + 22 := by omega
  simpa only [sourceBudget, hk] using h

theorem streamed_length (current : List Bool) (width : ℕ) (left right : List ℕ)
    (tuples : List (List Bool)) (stream : List Bool) :
    (streamed current width left right tuples stream).length = tuples.length + stream.length := by
  rw [streamed_eq_reverse_map]
  simp

theorem streamed_trueCount (current : List Bool) (width : ℕ) (left right : List ℕ)
    (tuples : List (List Bool)) (stream : List Bool) :
    PaddedCompletion.trueCount (streamed current width left right tuples stream) =
      PaddedCompletion.trueCount (tuples.map (leafBit current width left right)) +
        PaddedCompletion.trueCount stream := by
  rw [streamed_eq_reverse_map]
  simp [PaddedCompletion.trueCount, PaddedCompletion.successful, List.filter_reverse]

private theorem unread_false (records : List (List Bool)) :
    RecordPrograms.unread (fun _ => false) records [] = [] := by
  induction records with
  | nil => rfl
  | cons bits rest ih => simpa only [RecordPrograms.unread, Bool.false_eq_true, ite_false] using ih

/-- Every framed tuple is parsed and processed by the fixed callback. The
result is the reverse visit-order leaf stream, suitable for unary tallying. -/
theorem command_eval (current : List (List Bool)) (width : List Bool)
    (left right : List ℕ) (tuples : List (List Bool)) (stream : List Bool)
    (hv : ∀ bits ∈ tuples, validPayload current width.length left right bits) :
    ∃ n, n + 1 ≤ sourceBudget current.flatten width.length left right tuples ∧
      Eval command n (inputState current.flatten width left right tuples stream)
        (baseState current.flatten width left right
          (streamed current.flatten width.length left right tuples stream)) := by
  obtain ⟨n, next, hn, hnext, history, he⟩ := RecordPrograms.iterate_run_with_on
    ports callback (fun _ => false) (callbackCost current.flatten width.length left right)
    (invariant current.flatten width left right)
    (effect current.flatten width.length left right)
    (validPayload current width.length left right)
    (callback_contract current width left right) tuples []
    (baseState current.flatten width left right stream) hv ⟨stream, rfl⟩ false false false
  obtain ⟨out, rfl⟩ := hnext
  have hout : out = streamed current.flatten width.length left right tuples stream := by
    have h := history.fold_of_false (by simp) (fun d => d.stacks 11)
      (fun acc bits => leafBit current.flatten width.length left right bits :: acc)
      (fun _ _ _ h => h)
    simpa only [baseState, state, Fin.reduceEq, ite_true, ite_false, streamed] using h
  subst out
  have hany : tuples.any (fun _ => false) = false := by
    induction tuples <;> simp_all
  refine ⟨n, by dsimp [sourceBudget]; omega, ?_⟩
  have hfinal : RecordPrograms.state ports
      (baseState current.flatten width left right
        (streamed current.flatten width.length left right tuples stream))
      false true false [] [] =
      baseState current.flatten width left right
        (streamed current.flatten width.length left right tuples stream) := by
    rw [parser_state_eq]
    rfl
  simpa only [hany, unread_false, hfinal, ProgramEncoding.encodeRecords,
    inputState, List.append_nil, command] using he

theorem program_run (current : List (List Bool)) (width : List Bool)
    (left right : List ℕ) (tuples : List (List Bool)) (stream : List Bool)
    (hv : ∀ bits ∈ tuples, validPayload current width.length left right bits) :
    RunsIn program (sourceBudget current.flatten width.length left right tuples)
      ((inputState current.flatten width left right tuples stream).withPC (some program.entry))
      ((baseState current.flatten width left right
        (streamed current.flatten width.length left right tuples stream)).withPC none) := by
  obtain ⟨n, hn, he⟩ := command_eval current width left right tuples stream hv
  exact ⟨n + 1, hn, compiled_halt_trace he 16 11⟩

theorem primitive_run (current : List (List Bool)) (width : List Bool)
    (left right : List ℕ) (tuples : List (List Bool)) (stream : List Bool)
    (hv : ∀ bits ∈ tuples, validPayload current width.length left right bits) :
    Computation.RunsIn (primitive program).step
      (primitiveOverhead program * sourceBudget current.flatten width.length left right tuples)
      (primitiveCfg program
        ((inputState current.flatten width left right tuples stream).withPC (some program.entry)))
      (primitiveCfg program
        ((baseState current.flatten width left right
          (streamed current.flatten width.length left right tuples stream)).withPC none)) :=
  BitProgram.primitive_execution program (program_run current width left right tuples stream hv)

section Completion

open MulticolorTypes SlotAssignment SubexpTypeVariance

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]
variable {r Q Δ : ℕ} (P : Factor.Pattern V E) (slots : SlotMap P Δ)

def tupleBytes (candidate : List (Word r Q)) : List Bool :=
  (candidate.map ReadPlan.encodeWord).flatten

theorem completion_validPayload (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (current candidate : List (Word r Q)) (remaining : List ℕ)
    (hc : (AssignmentEnumeration.seedIndices vertices factors Δ).length ≤ current.length)
    (hr : remaining.length ≤ candidate.length) (pair : V × V) :
    validPayload (current.map ReadPlan.encodeWord) (ReadPlan.wordWidth r Q)
      (CollisionStreamProgram.completionPlan P slots vertices factors current.length remaining pair.1)
      (CollisionStreamProgram.completionPlan P slots vertices factors current.length remaining pair.2)
      (tupleBytes candidate) := by
  refine ⟨candidate.map ReadPlan.encodeWord, rfl, ?_, ?_, ?_⟩
  · intro row hrow
    have hm : row ∈ CollisionStreamProgram.completionRows current candidate := by
      simpa [CollisionStreamProgram.completionRows] using hrow
    exact CollisionStreamProgram.completionRows_width current candidate row hm
  · intro i hi
    have h := CollisionStreamProgram.completionPlan_valid P slots vertices factors hv he
      current candidate remaining hc hr pair.1 i hi
    simpa [CollisionStreamProgram.completionRows] using h
  · intro i hi
    have h := CollisionStreamProgram.completionPlan_valid P slots vertices factors hv he
      current candidate remaining hc hr pair.2 i hi
    simpa [CollisionStreamProgram.completionRows] using h

theorem leafBit_completed (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (default : Word r Q) (current candidate : List (Word r Q)) (remaining : List ℕ)
    (hc : (AssignmentEnumeration.seedIndices vertices factors Δ).length ≤ current.length)
    (hr : remaining.length ≤ candidate.length) (pair : V × V) :
    leafBit (tupleBytes current) (ReadPlan.wordWidth r Q)
      (CollisionStreamProgram.completionPlan P slots vertices factors current.length remaining pair.1)
      (CollisionStreamProgram.completionPlan P slots vertices factors current.length remaining pair.2)
      (tupleBytes candidate) =
      decide (LocalExpectation.naturalPairTerm P slots pair
        (ReadPlan.completedAssignment vertices factors default current remaining candidate) = 1) := by
  have hrows : ∀ row ∈ current.map ReadPlan.encodeWord ++ candidate.map ReadPlan.encodeWord,
      row.length = ReadPlan.wordWidth r Q := by
    intro row hrow
    apply CollisionStreamProgram.completionRows_width current candidate row
    simpa [CollisionStreamProgram.completionRows] using hrow
  rw [tupleBytes, tupleBytes, leafBit_eq_collision _ _ _ hrows]
  simpa [CollisionStreamProgram.completionRows] using
    CollisionStreamProgram.collisionBit_completed P slots vertices factors hv he
      default current candidate remaining hc hr pair

end Completion

end SubexponentialSAT.Subexp.CollisionTupleProgram

end OAI.Algorithms
