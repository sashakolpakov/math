import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ReadPlan
import OAI.Algorithms.SubexponentialSAT.Subexp.UnaryCompare
import OAI.Algorithms.SubexponentialSAT.ExecCNFMembership
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

/-!
# Computing the active completion positions

A fixed program filters a runtime list of unary seed positions. It retains a
position precisely when it is at least the runtime threshold and belongs to
the runtime pair read plan. The plan and threshold are preserved. Applying the
program to the complete ascending seed list gives a duplicate-free completion
plan in ascending order.
-/

namespace SubexponentialSAT.Subexp.ActivePlanProgram

open BitProgram StructuredCalls StackRoutines

abbrev Regs := Fin 10 → Bool
abbrev Data := State 10 12

abbrev state (regs : Regs) (source plan threshold acc query output : List Bool) : Data :=
  ⟨regs, ![[], [], query, [], [], source, plan, threshold, acc, [], [], output]⟩

def reset (regs : Regs) : Regs := readRegs regs 0 1 none

abbrev copy (src dst tmp : Fin 12) : Cmd 10 12 := .call (copyProgram src dst tmp 0 1)
abbrev copied (src dst : Fin 12) (d : Data) : Data :=
  ⟨reset d.regs, copyStacks src dst d.stacks⟩
abbrev clear (src : Fin 12) : Cmd 10 12 := .call (clearProgram src 0 1)
abbrev cleared (src : Fin 12) (d : Data) : Data :=
  ⟨reset d.regs, clearStacks src d.stacks⟩

theorem copy_eval (src dst tmp : Fin 12) (d : Data)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (htmp : d.stacks tmp = []) :
    Eval (copy src dst tmp) (7 * (d.stacks src).length + 5) d (copied src dst d) :=
  .call _ (ListRegisterProgram.copy_run src dst tmp 0 1 hsd hst htd (by decide)
    d.regs d.stacks htmp)

theorem clear_eval (src : Fin 12) (d : Data) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (cleared src d) :=
  .call _ (ListRegisterProgram.clear_run src 0 1 d.regs d.stacks)

def low7 : Fin 7 → Fin 10 := Fin.castAdd 3
def low5 : Fin 5 → Fin 12 := Fin.castAdd 7

theorem low7_injective : Function.Injective low7 := Fin.castAdd_injective 7 3
theorem low5_injective : Function.Injective low5 := Fin.castAdd_injective 5 7

abbrev membershipCall : Cmd 10 12 :=
  .call (ProgramLinking.liftProgram ExecCNFMembership.membershipProgram low7 low5)

abbrev member : Cmd 10 12 :=
  .seq (copy 6 0 4) (.seq membershipCall (.seq (clear 0) (clear 1)))

private theorem unread_length_le (test : List Bool → Bool) (records : List (List Bool)) :
    (RecordPrograms.unread test records []).length ≤ (Encoding.encodeList id records).length := by
  induction records with
  | nil => simp [RecordPrograms.unread, Encoding.encodeList]
  | cons x xs ih =>
    simp only [RecordPrograms.unread]
    split
    · simp [Encoding.length_encodeList_cons]
    · exact ih.trans (by simp [Encoding.length_encodeList_cons])

/-- The membership phase copies the persistent pair plan, calls the existing
actual encoded-membership scanner, and clears every scan residual. -/
theorem member_eval (records : List (List Bool)) (query source threshold acc output : List Bool)
    (regs : Regs) :
    ∃ n ≤ (20 * query.length + 40) * (Encoding.encodeList id records).length + 20,
      ∃ rf : Regs, rf 4 = decide (query ∈ records) ∧
      (∀ j : Fin 10, 7 ≤ j.val → rf j = regs j) ∧
      Eval member n
        (state regs source (Encoding.encodeList id records) threshold acc query.reverse output)
        (state rf source (Encoding.encodeList id records) threshold acc query.reverse output) := by
  let start := state regs source (Encoding.encodeList id records) threshold acc query.reverse output
  let prepared := copied 6 0 start
  let inner : ExecCNFMembership.Data := ⟨prepared.regs ∘ low7, prepared.stacks ∘ low5⟩
  have hi : ExecCNFMembership.invariant query inner := by
    simp [ExecCNFMembership.invariant, inner, prepared, start, copyStacks, low5]
  obtain ⟨next, hnxt, n, hn, ht⟩ := ExecCNFMembership.membership_runsIn query records [] inner hi
    (inner.regs 5) (inner.regs 6) (inner.regs 4)
  let last := RecordPrograms.state ExecCNFMembership.ports next false true
    (decide (query ∈ records)) (RecordPrograms.unread (fun bits => decide (bits = query)) records [])
    [decide (query ∈ records)]
  have hinput : RecordPrograms.state ExecCNFMembership.ports inner
      (inner.regs 5) (inner.regs 6) (inner.regs 4)
      (Encoding.encodeList id records ++ []) [] = inner := by
    apply RecordPrograms.state_eq_self <;>
      simp [inner, prepared, start, copyStacks, low5 ]
  rw [hinput] at ht
  have hembed : embedState low7 low5 prepared inner = prepared := by
    apply embedState_eq_of_ports _ _ _ _ _ low7_injective low5_injective <;> intros <;> rfl
  let scanned := embedState low7 low5 prepared last
  have hscan : Eval membershipCall n prepared scanned := by
    have h := eval_call_lifted ExecCNFMembership.membershipProgram low7 low5 prepared
      low7_injective low5_injective ht
    simpa only [hembed, membershipCall, scanned, last] using h
  have hreg4 : scanned.regs 4 = decide (query ∈ records) := by
    change scanned.regs (low7 4) = _
    rw [embedState_register _ _ _ _ low7_injective]
    simp [last, RecordPrograms.state ]
  have hregs (j : Fin 10) (hj : 7 ≤ j.val) : scanned.regs j = regs j := by
    have hout : ¬ ∃ i, low7 i = j := by
      rintro ⟨i, h⟩
      have hv := congrArg Fin.val h
      change i.val = j.val at hv
      omega
    rw [embedState_register_frame _ _ _ _ j hout]
    have h0 : j ≠ 0 := by intro h; subst j; norm_num at hj
    have h1 : j ≠ 1 := by intro h; subst j; norm_num at hj
    simp [prepared, reset, start, readRegs, h0, h1]
  have hs (j : Fin 5) : scanned.stacks (low5 j) = last.stacks j :=
    embedState_stack _ _ _ _ low5_injective j
  have hframe (j : Fin 12) (hj : 5 ≤ j.val) : scanned.stacks j = start.stacks j := by
    have hout : ¬ ∃ i, low5 i = j := by
      rintro ⟨i, h⟩
      have hv := congrArg Fin.val h
      change i.val = j.val at hv
      omega
    rw [embedState_stack_frame _ _ _ _ j hout]
    have h0 : j ≠ 0 := by intro h; subst j; norm_num at hj
    simp [prepared, copyStacks, h0]
  have hs0 := hs 0
  have hs1 := hs 1
  have hs2 := hs 2
  have hs3 := hs 3
  have hs4 := hs 4
  simp only [low5 ] at hs0 hs1 hs2 hs3 hs4
  simp [last, RecordPrograms.state, hnxt.1, hnxt.2.1,
    hnxt.2.2] at hs0 hs1 hs2 hs3 hs4
  let finish := cleared 1 (cleared 0 scanned)
  have hfinish : finish = state finish.regs source (Encoding.encodeList id records)
      threshold acc query.reverse output := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j
    all_goals simp [ clearStacks, hs2, hs3, hs4,
      hframe 5 (by decide), hframe 6 (by decide), hframe 7 (by decide),
      hframe 8 (by decide), hframe 9 (by decide), hframe 10 (by decide),
      hframe 11 (by decide), start ]
  have hc := copy_eval 6 0 4 start (by decide) (by decide) (by decide) rfl
  have hz0 := clear_eval 0 scanned
  have hz1 := clear_eval 1 (cleared 0 scanned)
  have hall := hc.seq (hscan.seq (hz0.seq hz1))
  change Eval member _ start finish at hall
  rw [hfinish] at hall
  refine ⟨_, ?_, finish.regs, ?_, ?_, hall⟩
  · have hu := unread_length_le (fun bits => decide (bits = query)) records
    simp only [start, List.length_cons, List.length_nil, hs0, clearStacks, hs1, Function.update_of_ne (by decide : (1 : Fin 12) ≠ 0)]
    dsimp
    nlinarith
  · simp [finish, reset, readRegs, hreg4]
  · intro j hj
    have h0 : j ≠ 0 := by intro h; subst j; norm_num at hj
    have h1 : j ≠ 1 := by intro h; subst j; norm_num at hj
    simpa [finish, cleared, reset, readRegs, h0, h1] using hregs j hj

def low4 : Fin 4 → Fin 10 := Fin.castAdd 6
def compareStack : Fin 2 → Fin 12 := ![9, 10]
theorem low4_injective : Function.Injective low4 := Fin.castAdd_injective 4 6
theorem compareStack_injective : Function.Injective compareStack := by decide

abbrev compareCall : Cmd 10 12 :=
  .call (ProgramLinking.liftProgram UnaryCompare.program low4 compareStack)

abbrev compare : Cmd 10 12 :=
  .seq (copy 7 9 4) (.seq (copy 2 10 4) (.seq compareCall (.seq (clear 9) (clear 10))))

/-- The threshold comparison uses fresh copies and preserves both its unary
inputs, the membership answer, and the outer parser registers. -/
theorem compare_eval (query source plan threshold acc output : List Bool) (regs : Regs) :
    ∃ n ≤ 30 * (threshold.length + query.length + 1), ∃ rf : Regs,
      rf 3 = decide (threshold.length ≤ query.length) ∧
      (∀ j : Fin 10, 4 ≤ j.val → rf j = regs j) ∧
      Eval compare n (state regs source plan threshold acc query.reverse output)
        (state rf source plan threshold acc query.reverse output) := by
  let start := state regs source plan threshold acc query.reverse output
  let first := copied 7 9 start
  let prepared := copied 2 10 first
  obtain ⟨n, hn, c, ht, hpc, hans⟩ :=
    UnaryCompare.runs (prepared.regs ∘ low4) threshold query.reverse
  let inner : State 4 2 := ⟨prepared.regs ∘ low4, UnaryCompare.pairStacks threshold query.reverse⟩
  let last : State 4 2 := ⟨c.regs, c.stacks⟩
  have hc : last.withPC none = c := by cases c; simp_all [last, StructuredProgram.State.withPC]
  have ht' : Trace UnaryCompare.program n
      (inner.withPC (some UnaryCompare.program.entry)) (last.withPC none) := by
    rw [hc]
    exact ht
  have hembed : embedState low4 compareStack prepared inner = prepared := by
    apply embedState_eq_of_ports _ _ _ _ _ low4_injective compareStack_injective
    · intros; rfl
    · intros; rfl
    · intro i; fin_cases i <;>
        simp [inner, prepared, first, start, copyStacks, compareStack,
          UnaryCompare.pairStacks]
    · intros; rfl
  let scanned := embedState low4 compareStack prepared last
  have hscan : Eval compareCall n prepared scanned := by
    have h := eval_call_lifted UnaryCompare.program low4 compareStack prepared
      low4_injective compareStack_injective ht'
    simpa only [hembed, compareCall, scanned] using h
  have hreg3 : scanned.regs 3 = decide (threshold.length ≤ query.length) := by
    change scanned.regs (low4 3) = _
    rw [embedState_register _ _ _ _ low4_injective]
    simpa [last] using hans
  have hregs (j : Fin 10) (hj : 4 ≤ j.val) : scanned.regs j = regs j := by
    have hout : ¬ ∃ i, low4 i = j := by
      rintro ⟨i, h⟩
      have hv := congrArg Fin.val h
      change i.val = j.val at hv
      omega
    rw [embedState_register_frame _ _ _ _ j hout]
    have h0 : j ≠ 0 := by intro h; subst j; norm_num at hj
    have h1 : j ≠ 1 := by intro h; subst j; norm_num at hj
    simp [prepared, first, reset, start, readRegs, h0, h1]
  have hframe (j : Fin 12) (h9 : j ≠ 9) (h10 : j ≠ 10) :
      scanned.stacks j = start.stacks j := by
    have hout : ¬ ∃ i, compareStack i = j := by
      rintro ⟨i, h⟩
      fin_cases i <;> simp_all [compareStack]
    rw [embedState_stack_frame _ _ _ _ j hout]
    simp [prepared, first, copyStacks, h9, h10]
  have hlen9 : (scanned.stacks 9).length ≤ threshold.length := by
    have hh := UnaryCompare.trace_length_le ht 0
    change (scanned.stacks (compareStack 0)).length ≤ _
    rw [embedState_stack _ _ _ _ compareStack_injective]
    simpa [last, UnaryCompare.start, UnaryCompare.pairStacks] using hh
  have hlen10 : (scanned.stacks 10).length ≤ query.length := by
    have hh := UnaryCompare.trace_length_le ht 1
    change (scanned.stacks (compareStack 1)).length ≤ _
    rw [embedState_stack _ _ _ _ compareStack_injective]
    simpa [last, UnaryCompare.start, UnaryCompare.pairStacks] using hh
  let finish := cleared 10 (cleared 9 scanned)
  have hfinish : finish = state finish.regs source plan threshold acc query.reverse output := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j
    all_goals simp [ clearStacks,
      hframe 0 (by decide) (by decide), hframe 1 (by decide) (by decide),
      hframe 2 (by decide) (by decide), hframe 3 (by decide) (by decide),
      hframe 4 (by decide) (by decide), hframe 5 (by decide) (by decide),
      hframe 6 (by decide) (by decide), hframe 7 (by decide) (by decide),
      hframe 8 (by decide) (by decide), hframe 11 (by decide) (by decide), start ]
  have h1 := copy_eval 7 9 4 start (by decide) (by decide) (by decide) rfl
  have h2 := copy_eval 2 10 4 first (by decide) (by decide) (by decide) rfl
  have hz9 := clear_eval 9 scanned
  have hz10 := clear_eval 10 (cleared 9 scanned)
  have hall := h1.seq (h2.seq (hscan.seq (hz9.seq hz10)))
  change Eval compare _ start finish at hall
  rw [hfinish] at hall
  refine ⟨_, ?_, finish.regs, ?_, ?_, hall⟩
  · simp only [List.length_reverse] at hn
    have hm := Nat.min_le_left threshold.length query.length
    simp [start, first, copyStacks, clearStacks]
    omega
  · simpa [finish, cleared, reset, readRegs] using hreg3
  · intro j hj
    have h0 : j ≠ 0 := by intro h; subst j; norm_num at hj
    have h1 : j ≠ 1 := by intro h; subst j; norm_num at hj
    simpa [finish, cleared, reset, readRegs, h0, h1] using hregs j hj

def emitRegs : Fin 3 → Fin 10 := ![0, 1, 9]
def emitStack : Fin 4 → Fin 12 := ![5, 7, 8, 2]
theorem emitRegs_injective : Function.Injective emitRegs := by decide
theorem emitStack_injective : Function.Injective emitStack := by decide

abbrev flags (regs : Regs) (v p f : Bool) : Regs :=
  Function.update (Function.update (Function.update regs 0 v) 1 p) 9 f

@[simp] theorem flags_self (regs : Regs) : flags regs (regs 0) (regs 1) (regs 9) = regs := by
  funext i
  fin_cases i <;> simp [flags]

abbrev emit : Cmd 10 12 :=
  .call (ProgramLinking.liftProgram SubexpNormalizeProgram.emitIfSelectedProgram emitRegs emitStack)

private theorem embed_emit (regs : Regs) (v p f : Bool)
    (source plan threshold acc query output source' threshold' acc' query' : List Bool) :
    embedState emitRegs emitStack (state regs source plan threshold acc query output)
      (SubexpNormalizeProgram.filterState v p f source' threshold' acc' query') =
      state (flags regs v p f) source' plan threshold' acc' query' output := by
  apply embedState_eq_of_ports _ _ _ _ _ emitRegs_injective emitStack_injective
  · intro i; fin_cases i <;> simp [ flags, emitRegs, SubexpNormalizeProgram.filterState,
      SubexpPostfixControl.triple]
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
    have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨2, h.symm⟩
    simp [ flags, h0, h1, h9]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h5 : i ≠ 5 := fun h => hi ⟨0, h.symm⟩
    have h7 : i ≠ 7 := fun h => hi ⟨1, h.symm⟩
    have h8 : i ≠ 8 := fun h => hi ⟨2, h.symm⟩
    have h2 : i ≠ 2 := fun h => hi ⟨3, h.symm⟩
    fin_cases i <;> simp_all []

theorem emit_eval (bits source plan threshold acc output : List Bool) (regs : Regs) :
    Eval emit (SubexpNormalizeProgram.emitIfSelectedSteps (regs 9) bits + 1)
      (state regs source plan threshold acc bits.reverse output)
      (state (flags regs false true false) source plan threshold
        (if regs 9 then true :: (Encoding.frame bits ++ acc) else acc) [] output) := by
  have ht := eval_call_lifted SubexpNormalizeProgram.emitIfSelectedProgram emitRegs emitStack
    (state regs source plan threshold acc bits.reverse output) emitRegs_injective emitStack_injective
    (SubexpNormalizeProgram.emitIfSelected_trace (regs 9) bits source threshold acc (regs 0) (regs 1))
  simpa only [embed_emit, flags_self, emit] using ht

def keep (records : List (List Bool)) (threshold : List Bool) (bits : List Bool) : Bool :=
  decide (threshold.length ≤ bits.length ∧ bits ∈ records)

abbrev callback : Cmd 10 12 :=
  .seq member (.seq compare (.seq (RecordPrograms.atom (.band 9 4 3)) emit))

def callbackCost (records : List (List Bool)) (threshold bits : List Bool) : ℕ :=
  (20 * bits.length + 40) * (Encoding.encodeList id records).length +
    30 * (threshold.length + bits.length + 1) + 5 * bits.length + 40

theorem callback_eval (records : List (List Bool))
    (bits source threshold acc output : List Bool) (regs : Regs) :
    ∃ n ≤ callbackCost records threshold bits, ∃ rf : Regs,
      rf 7 = regs 7 ∧ rf 8 = regs 8 ∧ rf 9 = false ∧
      Eval callback n
        (state regs source (Encoding.encodeList id records) threshold acc bits.reverse output)
        (state rf source (Encoding.encodeList id records) threshold
          (if keep records threshold bits then true :: (Encoding.frame bits ++ acc) else acc)
          [] output) := by
  obtain ⟨n, hn, ra, ha, hframea, hea⟩ := member_eval records bits source threshold acc output regs
  obtain ⟨m, hm, rb, hb, hframeb, heb⟩ :=
    compare_eval bits source (Encoding.encodeList id records) threshold acc output ra
  let rc := Function.update rb 9 (rb 4 && rb 3)
  have hc : Eval (RecordPrograms.atom (.band 9 4 3)) 1
      (state rb source (Encoding.encodeList id records) threshold acc bits.reverse output)
      (state rc source (Encoding.encodeList id records) threshold acc bits.reverse output) :=
    .base (.atom _ _)
  have hselect : rc 9 = keep records threshold bits := by
    simp [rc, keep, hframeb 4 (by decide), ha, hb, Bool.and_comm]
  have hec := emit_eval bits source (Encoding.encodeList id records) threshold acc output rc
  rw [hselect] at hec
  refine ⟨_, ?_, flags rc false true false, ?_, ?_, ?_, hea.seq (heb.seq (hc.seq hec))⟩
  · have he := SubexpNormalizeProgram.emitIfSelected_steps_le (keep records threshold bits) bits
    dsimp [callbackCost]
    omega
  · simp [flags, rc, hframeb 7 (by decide), hframea 7 (by decide)]
  · simp [flags, rc, hframeb 8 (by decide), hframea 8 (by decide)]
  · simp [flags]

def ports : RecordPrograms.Ports 10 12 where
  tag := 7
  present := 8
  found := 9
  source := 5
  payload := 2
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

abbrev outerFlags (regs : Regs) (v p f : Bool) : Regs :=
  Function.update (Function.update (Function.update regs 7 v) 8 p) 9 f

theorem recordState_state (regs : Regs) (v p f : Bool)
    (source plan threshold acc query output source' query' : List Bool) :
    RecordPrograms.state ports (state regs source plan threshold acc query output) v p f source' query' =
      state (outerFlags regs v p f) source' plan threshold acc query' output := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> simp [ ports ]

def invariant (records : List (List Bool)) (threshold : List Bool) (d : Data) : Prop :=
  ∃ regs source acc query, d = state regs source (Encoding.encodeList id records) threshold acc query []

theorem callback_contract (records : List (List Bool)) (threshold : List Bool) :
    RecordPrograms.CallbackContractWith ports callback (fun _ => false)
      (callbackCost records threshold) (invariant records threshold)
      (SubexpNormalizeProgram.FilterEffect 8 (keep records threshold)) := by
  intro bits tail base hbase
  rcases hbase with ⟨regs, source, acc, query, rfl⟩
  obtain ⟨n, hn, rf, h7, h8, h9, he⟩ :=
    callback_eval records bits tail threshold acc [] (outerFlags regs false true false)
  let next := state rf tail (Encoding.encodeList id records) threshold
    (if keep records threshold bits then true :: (Encoding.frame bits ++ acc) else acc) [] []
  have hnext : RecordPrograms.state ports next false true false tail [] = next := by
    apply RecordPrograms.state_eq_self
    · simpa [next, state, ports, outerFlags] using h7
    · simpa [next, state, ports, outerFlags] using h8
    · exact h9
    · rfl
    · rfl
  refine ⟨n, next, hn, ⟨rf, tail, _, [], rfl⟩, ?_, ?_⟩
  · rfl
  · rw [hnext, recordState_state]
    exact he

@[simp] theorem outerFlags_self (regs : Regs) :
    outerFlags regs (regs 7) (regs 8) (regs 9) = regs := by
  funext i
  fin_cases i <;> simp [outerFlags]

theorem filter_eval (records seeds : List (List Bool)) (threshold : List Bool) (regs : Regs) :
    ∃ n ≤ 3 + RecordPrograms.budget (callbackCost records threshold) seeds, ∃ rf : Regs,
      Eval (RecordPrograms.iterate ports callback) n
        (state regs (Encoding.encodeList id seeds) (Encoding.encodeList id records) threshold [false] [] [])
        (state rf [] (Encoding.encodeList id records) threshold
          (Encoding.encodeList id (seeds.filter (keep records threshold)).reverse) [] []) := by
  let base := state regs (Encoding.encodeList id seeds) (Encoding.encodeList id records)
    threshold [false] [] []
  have hb : invariant records threshold base := ⟨regs, _, _, _, rfl⟩
  obtain ⟨n, next, hn, hnext, hout, he⟩ := SubexpNormalizeProgram.filter_iterate_run
    ports callback (keep records threshold) (callbackCost records threshold)
    (invariant records threshold) 8 (by decide) (by decide)
    (callback_contract records threshold) seeds [] [] base hb rfl (regs 7) (regs 8) (regs 9)
  rcases hnext with ⟨rr, ss, aa, qq, rfl⟩
  have haa : aa = Encoding.encodeList id (seeds.filter (keep records threshold)).reverse := by
    simpa [recordState_state, state] using hout
  rw [haa] at he
  refine ⟨n, hn, outerFlags rr false true false, ?_⟩
  simpa only [base, List.append_nil, recordState_state, outerFlags_self] using he

def reverseStack : Fin 4 → Fin 12 := ![8, 7, 11, 2]
theorem reverseStack_injective : Function.Injective reverseStack := by decide

abbrev reverseCall : Cmd 10 12 :=
  .call (ProgramLinking.liftProgram SubexpNormalizeProgram.reverseRecordsProgram emitRegs reverseStack)

private theorem embed_reverse (regs : Regs) (v p f : Bool)
    (source plan threshold acc query output src' threshold' out' query' : List Bool) :
    embedState emitRegs reverseStack (state regs source plan threshold acc query output)
      (SubexpNormalizeProgram.filterState v p f src' threshold' out' query') =
      state (flags regs v p f) source plan threshold' src' query' out' := by
  apply embedState_eq_of_ports _ _ _ _ _ emitRegs_injective reverseStack_injective
  · intro i; fin_cases i <;> simp [ flags, emitRegs, SubexpNormalizeProgram.filterState,
      SubexpPostfixControl.triple]
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
    have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨2, h.symm⟩
    simp [ flags, h0, h1, h9]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h8 : i ≠ 8 := fun h => hi ⟨0, h.symm⟩
    have h7 : i ≠ 7 := fun h => hi ⟨1, h.symm⟩
    have h11 : i ≠ 11 := fun h => hi ⟨2, h.symm⟩
    have h2 : i ≠ 2 := fun h => hi ⟨3, h.symm⟩
    fin_cases i <;> simp_all []

theorem reverse_eval (records : List (List Bool)) (source plan threshold : List Bool) (regs : Regs) :
    ∃ n ≤ 10 * (Encoding.encodeList id records).length,
      Eval reverseCall n
        (state regs source plan threshold (Encoding.encodeList id records) [] [false])
        (state (flags regs false true false) source plan threshold [] []
          (Encoding.encodeList id records.reverse)) := by
  obtain ⟨n, hn, ht⟩ := SubexpNormalizeProgram.reverseRecords_runsIn records [] [] threshold
    (regs 0) (regs 1) (regs 9)
  have he := eval_call_lifted SubexpNormalizeProgram.reverseRecordsProgram emitRegs reverseStack
    (state regs source plan threshold (Encoding.encodeList id records) [] [false])
    emitRegs_injective reverseStack_injective ht
  refine ⟨n, hn, ?_⟩
  simpa only [List.append_nil, Encoding.encodeList, embed_reverse, flags_self, reverseCall] using he

abbrev initAccumulator : Cmd 10 12 :=
  .seq (RecordPrograms.atom (.set 0 false)) (RecordPrograms.atom (.push 8 0))

abbrev initializeOutput : Cmd 10 12 :=
  .seq (RecordPrograms.atom (.set 0 false)) (RecordPrograms.atom (.push 11 0))

abbrev command : Cmd 10 12 :=
  .seq initAccumulator (.seq (RecordPrograms.iterate ports callback) (.seq initializeOutput reverseCall))

abbrev program : Program 10 12 (size command + 1) := compiled command 5 11

theorem initAccumulator_eval (regs : Regs) (source plan threshold : List Bool) :
    Eval initAccumulator 2 (state regs source plan threshold [] [] [])
      (state (Function.update regs 0 false) source plan threshold [false] [] []) := by
  have h1 : Eval (RecordPrograms.atom (.set 0 false)) 1
      (state regs source plan threshold [] [] [])
      (state (Function.update regs 0 false) source plan threshold [] [] []) := .base (.atom _ _)
  have h2 : Eval (RecordPrograms.atom (.push 8 0)) 1
      (state (Function.update regs 0 false) source plan threshold [] [] [])
      (state (Function.update regs 0 false) source plan threshold [false] [] []) := by
    convert Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push (8 : Fin 12) (0 : Fin 10))
      (state (Function.update regs 0 false) source plan threshold [] [] [])) using 1
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [ StructuredProgram.Atom.instr, execInstr ]
  exact h1.seq h2

theorem initializeOutput_eval (regs : Regs) (source plan threshold acc : List Bool) :
    Eval initializeOutput 2 (state regs source plan threshold acc [] [])
      (state (Function.update regs 0 false) source plan threshold acc [] [false]) := by
  have h1 : Eval (RecordPrograms.atom (.set 0 false)) 1
      (state regs source plan threshold acc [] [])
      (state (Function.update regs 0 false) source plan threshold acc [] []) := .base (.atom _ _)
  have h2 : Eval (RecordPrograms.atom (.push 11 0)) 1
      (state (Function.update regs 0 false) source plan threshold acc [] [])
      (state (Function.update regs 0 false) source plan threshold acc [] [false]) := by
    convert Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push (11 : Fin 12) (0 : Fin 10))
      (state (Function.update regs 0 false) source plan threshold acc [] [])) using 1
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [ StructuredProgram.Atom.instr, execInstr ]
  exact h1.seq h2

theorem encoded_filter_length_le (records : List (List Bool)) (test : List Bool → Bool) :
    (Encoding.encodeList id (records.filter test)).length ≤ (Encoding.encodeList id records).length := by
  induction records with
  | nil => simp
  | cons x xs ih =>
    cases h : test x <;> simp [ h, Encoding.length_encodeList_cons] <;> omega

theorem encoded_reverse_length (records : List (List Bool)) :
    (Encoding.encodeList id records.reverse).length = (Encoding.encodeList id records).length := by
  have ha := ProgramEncoding.encodeRecords_length records.reverse
  have hb := ProgramEncoding.encodeRecords_length records
  change (ProgramEncoding.encodeRecords records.reverse).length =
    (ProgramEncoding.encodeRecords records).length
  rw [ha, hb]
  simp

def sourceBound (records seeds : List (List Bool)) (threshold : List Bool) : ℕ :=
  8 + RecordPrograms.budget (callbackCost records threshold) seeds +
    10 * (Encoding.encodeList id seeds).length

/-- Complete execution of the fixed filter, including the order-restoring
pass. Its output is the encoded filtered list in the original input order. -/
theorem command_eval (records seeds : List (List Bool)) (threshold : List Bool) (regs : Regs) :
    ∃ n ≤ sourceBound records seeds threshold - 1, ∃ rf : Regs,
      Eval command n
        (state regs (Encoding.encodeList id seeds) (Encoding.encodeList id records) threshold [] [] [])
        (state rf [] (Encoding.encodeList id records) threshold [] []
          (Encoding.encodeList id (seeds.filter (keep records threshold)))) := by
  obtain ⟨n, hn, rf, he⟩ := filter_eval records seeds threshold (Function.update regs 0 false)
  obtain ⟨m, hm, hr⟩ := reverse_eval (seeds.filter (keep records threshold)).reverse []
    (Encoding.encodeList id records) threshold (Function.update rf 0 false)
  rw [List.reverse_reverse] at hr
  have hinit := initAccumulator_eval regs (Encoding.encodeList id seeds) (Encoding.encodeList id records) threshold
  have hout := initializeOutput_eval rf [] (Encoding.encodeList id records) threshold
    (Encoding.encodeList id (seeds.filter (keep records threshold)).reverse)
  refine ⟨_, ?_, flags (Function.update rf 0 false) false true false,
    hinit.seq (he.seq (hout.seq hr))⟩
  have hlen := encoded_filter_length_le seeds (keep records threshold)
  rw [encoded_reverse_length] at hm
  dsimp [sourceBound]
  omega

def unary (n : ℕ) : List Bool := List.replicate n true

def indexRecords (positions : List ℕ) : List (List Bool) := positions.map unary

def active (seeds plan : List ℕ) (fixedCount : ℕ) : List ℕ :=
  seeds.filter (fun n => decide (fixedCount ≤ n ∧ n ∈ plan))

abbrev inputState (regs : Regs) (seeds plan : List ℕ) (fixedCount : ℕ) : Data :=
  state regs (ProgramEncoding.encodeRecords (indexRecords seeds))
    (ProgramEncoding.encodeRecords (indexRecords plan)) (unary fixedCount) [] [] []

abbrev outputState (regs : Regs) (seeds plan : List ℕ) (fixedCount : ℕ) : Data :=
  state regs [] (ProgramEncoding.encodeRecords (indexRecords plan)) (unary fixedCount) [] []
    (ProgramEncoding.encodeRecords (indexRecords (active seeds plan fixedCount)))

def traceBound (seeds plan : List ℕ) (fixedCount : ℕ) : ℕ :=
  sourceBound (indexRecords plan) (indexRecords seeds) (unary fixedCount)

theorem unary_injective : Function.Injective unary := by
  intro m n h
  simpa [unary] using congrArg List.length h

theorem filter_indexRecords (seeds plan : List ℕ) (fixedCount : ℕ) :
    (indexRecords seeds).filter (keep (indexRecords plan) (unary fixedCount)) =
      indexRecords (active seeds plan fixedCount) := by
  simp only [indexRecords, active, List.filter_map]
  congr 1
  apply List.filter_congr
  intro n hn
  simp [keep, unary, List.mem_map ]

/-- Actual halted trace, with arbitrary runtime seed and plan lists. -/
theorem program_runsIn (regs : Regs) (seeds plan : List ℕ) (fixedCount : ℕ) :
    ∃ rf : Regs, RunsIn program (traceBound seeds plan fixedCount)
      ((inputState regs seeds plan fixedCount).withPC (some program.entry))
      ((outputState rf seeds plan fixedCount).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := command_eval (indexRecords plan) (indexRecords seeds) (unary fixedCount) regs
  rw [filter_indexRecords] at he
  refine ⟨rf, n + 1, ?_, ?_⟩
  · have hpos : 0 < traceBound seeds plan fixedCount := by
      simp [traceBound, sourceBound]
    dsimp [traceBound] at *
    omega
  · simpa [program, inputState, outputState, ProgramEncoding.encodeRecords] using compiled_halt_trace he 5 11

theorem primitive_run (regs : Regs) (seeds plan : List ℕ) (fixedCount : ℕ) :
    ∃ rf : Regs, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * traceBound seeds plan fixedCount)
      (primitiveCfg program ((inputState regs seeds plan fixedCount).withPC (some program.entry)))
      (primitiveCfg program ((outputState rf seeds plan fixedCount).withPC none)) := by
  obtain ⟨rf, h⟩ := program_runsIn regs seeds plan fixedCount
  exact ⟨rf, primitive_execution program h⟩

theorem active_nodup (seeds plan : List ℕ) (fixedCount : ℕ) (h : seeds.Nodup) :
    (active seeds plan fixedCount).Nodup := h.filter _

@[simp] theorem mem_active (seeds plan : List ℕ) (fixedCount n : ℕ) :
    n ∈ active seeds plan fixedCount ↔ n ∈ seeds ∧ fixedCount ≤ n ∧ n ∈ plan := by
  simp [active ]

theorem active_reverse_left (seeds left right : List ℕ) (fixedCount : ℕ) :
    active seeds (left.reverse ++ right) fixedCount = active seeds (left ++ right) fixedCount := by
  simp only [active]
  congr 1
  funext n
  simp

/-- Filtering the complete ascending seed enumeration is exactly filtering
the unprocessed suffix range; no sorting or deduplication is assumed. -/
theorem active_range_eq (seedCount fixedCount : ℕ) (plan : List ℕ) :
    active (List.range seedCount) plan fixedCount =
      (List.range' fixedCount (seedCount - fixedCount)).filter (fun n => decide (n ∈ plan)) := by
  have hleft : List.Pairwise (· < ·) (active (List.range seedCount) plan fixedCount) :=
    List.Pairwise.filter _ List.pairwise_lt_range
  have hrange : List.Pairwise (· < ·) (List.range' fixedCount (seedCount - fixedCount)) :=
    List.pairwise_lt_range'
  apply List.Pairwise.eq_of_mem_iff hleft (List.Pairwise.filter _ hrange)
  intro n
  by_cases hp : n ∈ plan
  · simp [mem_active, List.mem_filter, List.mem_range'_1, hp]
    omega
  · simp [mem_active, List.mem_filter, List.mem_range'_1, hp]

section ReadPlan

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]
variable (P : Factor.Pattern V E) {Δ : ℕ} (slots : SlotAssignment.SlotMap P Δ)

/-- The runtime filter computes precisely the completion-support enumeration
used in the collision-leaf refinement. -/
theorem active_eq_remainingPlan (vertices : List V) (factors : List E) (pair : V × V)
    (seedCount fixedCount : ℕ) :
    active (List.range seedCount) (ReadPlan.pairPlan P slots vertices factors pair) fixedCount =
      ReadPlan.remainingPlan P slots vertices factors pair fixedCount (seedCount - fixedCount) :=
  active_range_eq seedCount fixedCount _

theorem active_pair_length_le (vertices : List V) (factors : List E) (pair : V × V)
    (seedCount fixedCount : ℕ) :
    (active (List.range seedCount) (ReadPlan.pairPlan P slots vertices factors pair) fixedCount).length ≤
      2 * (Δ + 1) := by
  rw [active_eq_remainingPlan]
  exact ReadPlan.remainingPlan_length_le P slots vertices factors pair fixedCount (seedCount - fixedCount)

end ReadPlan

theorem callbackCost_le (records : List (List Bool)) (threshold bits : List Bool) :
    callbackCost records threshold bits ≤
      200 * ((Encoding.encodeList id records).length + threshold.length + 1) * (bits.length + 1) := by
  unfold callbackCost
  nlinarith [Nat.zero_le (bits.length * (Encoding.encodeList id records).length),
    Nat.zero_le (bits.length * threshold.length)]

theorem budget_le (records seeds : List (List Bool)) (threshold : List Bool) :
    RecordPrograms.budget (callbackCost records threshold) seeds ≤
      200 * ((Encoding.encodeList id records).length + threshold.length + 1) *
        (Encoding.encodeList id seeds).length := by
  let B := (Encoding.encodeList id records).length + threshold.length + 1
  have hB : 1 ≤ B := by dsimp [B]; omega
  induction seeds with
  | nil => simp [RecordPrograms.budget]
  | cons bits seeds ih =>
    have hc := callbackCost_le records threshold bits
    change callbackCost records threshold bits ≤ 200 * B * (bits.length + 1) at hc
    change RecordPrograms.budget (callbackCost records threshold) seeds ≤
      200 * B * (Encoding.encodeList id seeds).length at ih
    change _ ≤ 200 * B * (Encoding.encodeList id (bits :: seeds)).length
    rw [Encoding.length_encodeList_cons]
    simp only [RecordPrograms.budget, id_eq]
    have hprod : bits.length + 1 ≤ B * (bits.length + 1) := by nlinarith
    nlinarith

theorem sourceBound_le (records seeds : List (List Bool)) (threshold : List Bool) :
    sourceBound records seeds threshold ≤
      256 * ((Encoding.encodeList id records).length + threshold.length + 1) *
        ((Encoding.encodeList id seeds).length + 1) := by
  have hb := budget_le records seeds threshold
  have hB : 1 ≤ (Encoding.encodeList id records).length + threshold.length + 1 := by omega
  unfold sourceBound
  nlinarith [Nat.mul_le_mul_right (Encoding.encodeList id seeds).length hB]

/-- Quadratic in the total unary/encoded input size, with a fixed constant. -/
theorem traceBound_quadratic (seeds plan : List ℕ) (fixedCount : ℕ) :
    traceBound seeds plan fixedCount ≤ 256 *
      ((ProgramEncoding.encodeRecords (indexRecords seeds)).length +
       (ProgramEncoding.encodeRecords (indexRecords plan)).length + fixedCount + 2) ^ 2 := by
  have h := sourceBound_le (indexRecords plan) (indexRecords seeds) (unary fixedCount)
  simp only [unary, List.length_replicate] at h
  change traceBound seeds plan fixedCount ≤ _ at h
  let A := (ProgramEncoding.encodeRecords (indexRecords seeds)).length
  let B := (ProgramEncoding.encodeRecords (indexRecords plan)).length + fixedCount + 1
  change traceBound seeds plan fixedCount ≤ 256 * B * (A + 1) at h
  have heq : (ProgramEncoding.encodeRecords (indexRecords seeds)).length +
      (ProgramEncoding.encodeRecords (indexRecords plan)).length + fixedCount + 2 = A + B + 1 := by
    dsimp [A, B]
    omega
  rw [heq]
  nlinarith [Nat.zero_le (A ^ 2), Nat.zero_le (B ^ 2)]

/-- Raw counters are measured by length; their bit values are retained. -/
abbrev inputStateThreshold (regs : Regs) (seeds plan : List ℕ) (threshold : List Bool) : Data :=
  state regs (ProgramEncoding.encodeRecords (indexRecords seeds))
    (ProgramEncoding.encodeRecords (indexRecords plan)) threshold [] [] []

abbrev outputStateThreshold (regs : Regs) (seeds plan : List ℕ) (threshold : List Bool) : Data :=
  state regs [] (ProgramEncoding.encodeRecords (indexRecords plan)) threshold [] []
    (ProgramEncoding.encodeRecords (indexRecords (active seeds plan threshold.length)))

def traceBoundThreshold (seeds plan : List ℕ) (threshold : List Bool) : ℕ :=
  sourceBound (indexRecords plan) (indexRecords seeds) threshold

theorem filter_indexRecords_threshold (seeds plan : List ℕ) (threshold : List Bool) :
    (indexRecords seeds).filter (keep (indexRecords plan) threshold) =
      indexRecords (active seeds plan threshold.length) := by
  have hk : keep (indexRecords plan) threshold =
      keep (indexRecords plan) (unary threshold.length) := by
    funext bits
    simp [keep, unary]
  rw [hk]
  exact filter_indexRecords seeds plan threshold.length

/-- The actual program preserves an arbitrary raw threshold word and uses
only its length. In particular, a processed-counter prefix need not contain
canonical bit values. -/
theorem program_runsIn_threshold (regs : Regs) (seeds plan : List ℕ) (threshold : List Bool) :
    ∃ rf : Regs, RunsIn program (traceBoundThreshold seeds plan threshold)
      ((inputStateThreshold regs seeds plan threshold).withPC (some program.entry))
      ((outputStateThreshold rf seeds plan threshold).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := command_eval (indexRecords plan) (indexRecords seeds) threshold regs
  rw [filter_indexRecords_threshold] at he
  refine ⟨rf, n + 1, ?_, ?_⟩
  · have hpos : 0 < traceBoundThreshold seeds plan threshold := by
      simp [traceBoundThreshold, sourceBound]
    dsimp [traceBoundThreshold] at *
    omega
  · simpa [program, inputStateThreshold, outputStateThreshold, ProgramEncoding.encodeRecords] using
      compiled_halt_trace he 5 11

end SubexponentialSAT.Subexp.ActivePlanProgram

end OAI.Algorithms
