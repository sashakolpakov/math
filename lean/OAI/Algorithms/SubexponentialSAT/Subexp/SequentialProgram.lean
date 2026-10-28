import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MinimumProgram
import OAI.Algorithms.SubexponentialSAT.ArrayUpdateLifted

namespace OAI.Algorithms

/-!
# Fixed sequential assignment control

The loop counter, processed index, word width, alphabet, and assignment are
runtime stack data. A fixed score-building command is composed with the
verified minimum selector and preserving packed-array operations.
-/

namespace SubexponentialSAT.Subexp.SequentialProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev Data := State 16 48

abbrev atom (a : StructuredProgram.Atom 16 48) : Cmd 16 48 := .base (.atom a)

def minimumRegisters : Fin 9 → Fin 16 := Fin.castAdd 7
def minimumStacks : Fin 8 → Fin 48 := Fin.castAdd 40

theorem minimumRegisters_injective : Function.Injective minimumRegisters := by
  intro a b h
  have hv := congrArg (fun x : Fin 16 => x.val) h
  exact Fin.ext hv

theorem minimumStacks_injective : Function.Injective minimumStacks := by
  intro a b h
  have hv := congrArg (fun x : Fin 48 => x.val) h
  exact Fin.ext hv

abbrev minimumProgram : Program 16 48 (size MinimumProgram.command + 1) :=
  ProgramLinking.liftProgram MinimumProgram.program minimumRegisters minimumStacks

abbrev readPorts : Fin 8 → Fin 48 := ![9, 12, 7, 10, 13, 14, 15, 16]
abbrev replacePorts : Fin 8 → Fin 48 := ![8, 12, 17, 10, 13, 14, 15, 16]

abbrev readProgram : Program 16 48 38 :=
  ProgramLinking.liftProgram (ArrayUpdatePrograms.readProgram (9 : Fin 16) 8) id readPorts

abbrev replaceProgram : Program 16 48 44 :=
  ProgramLinking.liftProgram (ArrayUpdatePrograms.replaceProgram (9 : Fin 16) 8) id replacePorts

abbrev readEmbedding : Fin 8 ↪ Fin 48 := ⟨readPorts, by decide⟩
abbrev replaceEmbedding : Fin 8 ↪ Fin 48 := ⟨replacePorts, by decide⟩

abbrev wordUpdate : Cmd 16 48 :=
  .seq (.call readProgram)
    (.seq (.call (copyProgram (19 : Fin 48) 17 18 (9 : Fin 16) 8)) (.call replaceProgram))

abbrev resetRegisters : Cmd 16 48 :=
  ([0, 1, 2, 3, 4, 5, 6, 7, 8] : List (Fin 16)).foldr
    (fun j rest => .seq (atom (.set j false)) rest) (.base .skip)

abbrev cleanAuxiliary : Cmd 16 48 :=
  ([0, 1, 2, 3, 4, 5, 6, 7, 12] : List (Fin 48)).foldr
    (fun j rest => .seq (.call (clearProgram j (9 : Fin 16) 8)) rest) (.base .skip)

abbrev incrementProcessed : Cmd 16 48 :=
  .seq (atom (.set 9 false)) (atom (.push 19 9))

/-- The selected unary index is consumed by the alphabet lookup. The
processed index is copied before the assignment update consumes its copy. -/
abbrev selectAndUpdate : Cmd 16 48 :=
  .seq resetRegisters
    (.seq (.call minimumProgram)
      (.seq wordUpdate (.seq cleanAuxiliary incrementProcessed)))

abbrev step (scoreBuilder : Cmd 16 48) : Cmd 16 48 :=
  .seq scoreBuilder selectAndUpdate

abbrev peekRemaining : Cmd 16 48 := atom (.peek 11 9 10)
abbrev dropRemaining : Cmd 16 48 := atom (.pop 11 9 10)

abbrev body (scoreBuilder : Cmd 16 48) : Cmd 16 48 :=
  .seq dropRemaining (.seq (step scoreBuilder) peekRemaining)

abbrev loop (scoreBuilder : Cmd 16 48) : Cmd 16 48 :=
  .while 10 (body scoreBuilder)

abbrev command (scoreBuilder : Cmd 16 48) : Cmd 16 48 :=
  .seq peekRemaining (loop scoreBuilder)

abbrev program (scoreBuilder : Cmd 16 48) :
    Program 16 48 (size (command scoreBuilder) + 1) :=
  compiled (command scoreBuilder) 8 8

theorem instruction_stack_length_le {r s l : ℕ} (instr : Instr r s l)
    (c : Cfg r s l) (j : Fin s) :
    ((execInstr instr c).stacks j).length ≤ (c.stacks j).length + 1 := by
  cases instr <;> simp [execInstr, Function.update_apply]
  all_goals split_ifs <;> simp_all [List.length_tail] <;> omega

theorem trace_stack_length_le {r s l : ℕ} {p : Program r s l} {t : ℕ}
    {c e : Cfg r s l} (ht : Trace p t c e) (j : Fin s) :
    (e.stacks j).length ≤ (c.stacks j).length + t := by
  induction ht with
  | refl => simp
  | @cons n a b c hs ht ih =>
      have hb : (b.stacks j).length ≤ (a.stacks j).length + 1 := by
        cases hp : a.pc with
        | none => simp [BitProgram.step, hp] at hs
        | some q =>
            have h := Option.some.inj (by simpa [BitProgram.step, hp] using hs)
            rw [← h]
            exact instruction_stack_length_le _ _ j
      omega

private theorem embed_restrict (d : Data) :
    embedState minimumRegisters minimumStacks d
      ⟨fun i => d.regs (minimumRegisters i), fun i => d.stacks (minimumStacks i)⟩ = d := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext j
    by_cases h : ∃ i, minimumRegisters i = j
    · obtain ⟨i, rfl⟩ := h
      exact embedState_register minimumRegisters minimumStacks d _ minimumRegisters_injective i
    · exact embedState_register_frame minimumRegisters minimumStacks d _ j h
  · funext j
    by_cases h : ∃ i, minimumStacks i = j
    · obtain ⟨i, rfl⟩ := h
      exact embedState_stack minimumRegisters minimumStacks d _ minimumStacks_injective i
    · exact embedState_stack_frame minimumRegisters minimumStacks d _ j h

theorem minimum_eval {A : Type*} (score : A → ℕ) (a : A) (tail : List A)
    (d : Data)
    (hr : ∀ i, d.regs (minimumRegisters i) = false)
    (hs : d.stacks 0 = ProgramEncoding.encodeRecords
      ((a :: tail).map (fun x => UnaryCompare.encode (score x))))
    (he : ∀ i : Fin 8, i ≠ 0 → d.stacks (minimumStacks i) = []) :
    ∃ t ≤ 500 * (score a + (tail.map score).sum + tail.length + 1) ^ 2,
      ∃ e : Data, ∃ k < (a :: tail).length,
        Eval (.call minimumProgram) t d e ∧
        (e.stacks 7).length = k ∧
        (a :: tail)[k]? = some (NaturalAssignment.chooseMinNat score a tail) ∧
        (∀ j : Fin 48, 8 ≤ j.val → e.stacks j = d.stacks j) ∧
        (∀ j : Fin 16, 9 ≤ j.val → e.regs j = d.regs j) ∧
        (∀ j : Fin 48, j.val < 8 → (e.stacks j).length ≤
          (d.stacks 0).length + 500 * (score a + (tail.map score).sum + tail.length + 1) ^ 2) := by
  obtain ⟨small, k, hk, ⟨t, ht, htrace⟩, hout, hlookup⟩ :=
    MinimumProgram.program_candidates score a tail
  let initialSmall := MinimumProgram.inputState
    ((a :: tail).map (fun x => UnaryCompare.encode (score x)))
  have hi : (⟨fun i => d.regs (minimumRegisters i),
      fun i => d.stacks (minimumStacks i)⟩ : State 9 8) = initialSmall := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      simp [ MinimumProgram.emptyData, MinimumProgram.ports, hr]
    · funext j
      by_cases hj : j = 0
      · subst j
        simpa [initialSmall, MinimumProgram.inputState, RecordPrograms.state,
          MinimumProgram.ports, minimumStacks] using hs
      ·
        rw [he j hj]
        by_cases hj1 : j = 1 <;>
          simp [ MinimumProgram.emptyData, MinimumProgram.ports, hj, hj1, Function.update_apply]
  have hi' : embedState minimumRegisters minimumStacks d initialSmall = d := by
    rw [← hi]
    exact embed_restrict d
  let e := embedState minimumRegisters minimumStacks d small
  have hcall := eval_call_lifted MinimumProgram.program minimumRegisters minimumStacks d
    minimumRegisters_injective minimumStacks_injective htrace
  refine ⟨t, ht, e, k, hk, ?_, ?_, hlookup, ?_, ?_, ?_⟩
  · change Eval (.call (ProgramLinking.liftProgram MinimumProgram.program
      minimumRegisters minimumStacks)) t
      (embedState minimumRegisters minimumStacks d initialSmall)
      (embedState minimumRegisters minimumStacks d small) at hcall
    simpa only [hi', minimumProgram] using hcall
  · change ((embedState minimumRegisters minimumStacks d small).stacks (minimumStacks 7)).length = k
    rw [embedState_stack _ _ _ _ minimumStacks_injective]
    exact hout
  · intro j hj
    apply embedState_stack_frame
    rintro ⟨i, h⟩
    have hv := congrArg Fin.val h
    change i.val = j.val at hv
    omega

  · intro j hj
    apply embedState_register_frame
    rintro ⟨i, h⟩
    have hv := congrArg Fin.val h
    change i.val = j.val at hv
    omega
  · intro j hj
    let i : Fin 8 := ⟨j.val, hj⟩
    have hji : minimumStacks i = j := Fin.ext rfl
    rw [← hji]
    change ((embedState minimumRegisters minimumStacks d small).stacks (minimumStacks i)).length ≤ _
    rw [embedState_stack _ _ _ _ minimumStacks_injective]
    have hg := trace_stack_length_le htrace i
    change (small.stacks i).length ≤ (initialSmall.stacks i).length + t at hg
    have hlen : (initialSmall.stacks i).length ≤ (d.stacks 0).length := by
      rw [← hi]
      by_cases hz : i = 0
      · rw [hz]; exact le_rfl
      · simp [he i hz]
    omega

abbrev resetList (rs : List (Fin 16)) : Cmd 16 48 :=
  rs.foldr (fun j rest => .seq (atom (.set j false)) rest) (.base .skip)

abbrev resetState (rs : List (Fin 16)) (d : Data) : Data :=
  ⟨fun j => if j ∈ rs then false else d.regs j, d.stacks⟩

theorem resetList_eval (rs : List (Fin 16)) (d : Data) :
    Eval (resetList rs) rs.length d (resetState rs d) := by
  induction rs generalizing d with
  | nil =>
      simpa [resetList, resetState] using (Eval.base (StructuredProgram.Eval.skip d))
  | cons r rs ih =>
      let e : Data := ⟨Function.update d.regs r false, d.stacks⟩
      have ha : Eval (atom (.set r false)) 1 d e := .base (.atom _ _)
      have hh := ha.seq (ih e)
      have hs : resetState rs e = resetState (r :: rs) d := by
        apply congrArg₂ StructuredProgram.State.mk
        · funext j
          by_cases hj : j = r <;> by_cases hr : j ∈ rs <;>
            simp_all [resetState, e, Function.update_apply]
        · rfl
      simpa [resetList, hs, Nat.add_comm] using hh

theorem resetRegisters_eval (d : Data) :
    ∃ e : Data, Eval resetRegisters 9 d e ∧ e.stacks = d.stacks ∧
      (∀ i, e.regs (minimumRegisters i) = false) := by
  refine ⟨resetState [0, 1, 2, 3, 4, 5, 6, 7, 8] d,
    resetList_eval _ d, rfl, ?_⟩
  intro i
  fin_cases i <;> simp [ minimumRegisters]

abbrev clearList (rs : List (Fin 48)) : Cmd 16 48 :=
  rs.foldr (fun j rest => .seq (.call (clearProgram j (9 : Fin 16) 8)) rest) (.base .skip)

theorem clearList_eval (rs : List (Fin 48)) (d : Data) (bound : ℕ)
    (hb : ∀ j ∈ rs, (d.stacks j).length ≤ bound) :
    ∃ n ≤ rs.length * (2 * bound + 3), ∃ e : Data,
      Eval (clearList rs) n d e ∧
      (∀ j, e.stacks j = if j ∈ rs then [] else d.stacks j) := by
  induction rs generalizing d with
  | nil =>
      exact ⟨0, by simp, d, .base (.skip d), by simp⟩
  | cons r rs ih =>
      let middle : Data := ⟨readRegs d.regs 9 8 none, clearStacks r d.stacks⟩
      have hm : ∀ j ∈ rs, (middle.stacks j).length ≤ bound := by
        intro j hj
        by_cases he : j = r
        · subst j
          simp [middle, clearStacks]
        · simpa [middle, clearStacks, he] using hb j (by simp [hj])
      obtain ⟨n, hn, e, he, hs⟩ := ih middle hm
      have ht : Eval (.call (clearProgram r (9 : Fin 16) 8))
          (2 * (d.stacks r).length + 3) d middle :=
        .call _ (ListRegisterProgram.clear_run r 9 8 d.regs d.stacks)
      refine ⟨(2 * (d.stacks r).length + 3) + n, ?_, e, ht.seq he, ?_⟩
      · have hr := hb r (by simp)
        simp only [List.length_cons]
        nlinarith
      · intro j
        rw [hs]
        by_cases hj : j = r <;> by_cases hr : j ∈ rs <;>
          simp_all [middle, clearStacks, Function.update_apply]

theorem cleanAuxiliary_eval (d : Data) (bound : ℕ)
    (hb : ∀ j ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 12] : List (Fin 48)),
      (d.stacks j).length ≤ bound) :
    ∃ n ≤ 9 * (2 * bound + 3), ∃ e : Data,
      Eval cleanAuxiliary n d e ∧
      (∀ j, e.stacks j = if j ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 12] : List (Fin 48))
        then [] else d.stacks j) :=
  clearList_eval _ d bound hb

abbrev afterWordUpdate (d : Data) (assigned : List (List Bool)) (new rest : List Bool) : Data :=
  ⟨readRegs d.regs 9 8 none,
    Function.update (Function.update (Function.update d.stacks 7 []) 12 new)
      8 (assigned.flatten ++ (new ++ rest))⟩

/-- A preserving alphabet lookup followed by a preserving assignment write.
All indices and widths are runtime unary stacks. -/
theorem wordUpdate_eval (d : Data) (before assigned : List (List Bool))
    (new old after rest : List Bool)
    (hcandidates : d.stacks 9 = before.flatten ++ (new ++ after))
    (hassignment : d.stacks 8 = assigned.flatten ++ (old ++ rest))
    (hindex : (d.stacks 7).length = before.length)
    (hprocessed : (d.stacks 19).length = assigned.length)
    (hbefore : ∀ row ∈ before, row.length = (d.stacks 10).length)
    (hassigned : ∀ row ∈ assigned, row.length = (d.stacks 10).length)
    (hnew : new.length = (d.stacks 10).length)
    (hold : old.length = (d.stacks 10).length)
    (h12 : d.stacks 12 = []) (h13 : d.stacks 13 = []) (h14 : d.stacks 14 = [])
    (h15 : d.stacks 15 = []) (h16 : d.stacks 16 = []) (h17 : d.stacks 17 = [])
    (h18 : d.stacks 18 = []) :
    Eval wordUpdate
      ((before.length * (14 * (d.stacks 10).length + 10) + 15 * (d.stacks 10).length + 16) +
        ((7 * assigned.length + 5) +
          (assigned.length * (14 * (d.stacks 10).length + 10) +
            20 * (d.stacks 10).length + 21)))
      d (afterWordUpdate d assigned new rest) := by
  let r : Data := ⟨readRegs d.regs 9 8 none,
    ArrayUpdateLifted.readStacksAt readEmbedding new d.stacks⟩
  have hr : Eval (.call readProgram)
      (before.length * (14 * (d.stacks 10).length + 10) +
        15 * (d.stacks 10).length + 16) d r :=
    ArrayUpdateLifted.readProgramAt_eval readEmbedding 9 8 (by decide)
      before new after (d.stacks 10) (d.stacks 7) d.regs d.stacks
      hcandidates rfl rfl hindex hbefore hnew h13 h14 h15 h16
  let c : Data := ⟨readRegs r.regs 9 8 none, copyStacks 19 17 r.stacks⟩
  have hc : Eval (.call (copyProgram (19 : Fin 48) 17 18 (9 : Fin 16) 8))
      (7 * assigned.length + 5) r c := by
    have h := ListRegisterProgram.copy_run (19 : Fin 48) 17 18 (9 : Fin 16) 8
      (by decide) (by decide) (by decide) (by decide) r.regs r.stacks
      (by simpa [r, ArrayUpdateLifted.readStacksAt, readEmbedding, readPorts] using h18)
    have hc' : Eval (.call (copyProgram (19 : Fin 48) 17 18 (9 : Fin 16) 8))
        (7 * (r.stacks 19).length + 5) r c := .call _ h
    convert hc' using 1
    simp [r, ArrayUpdateLifted.readStacksAt, readEmbedding, readPorts, hprocessed]
  let e : Data := ⟨readRegs c.regs 9 8 none,
    ArrayUpdateLifted.replaceStacksAt replaceEmbedding assigned new rest c.stacks⟩
  have hrpl : Eval (.call replaceProgram)
      (assigned.length * (14 * (d.stacks 10).length + 10) +
        20 * (d.stacks 10).length + 21) c e := by
    apply ArrayUpdateLifted.replaceProgramAt_eval replaceEmbedding 9 8 (by decide)
      assigned old new rest (d.stacks 10) (d.stacks 19) c.regs c.stacks
    all_goals try simp [c, r, ArrayUpdateLifted.readStacksAt, copyStacks,
      readEmbedding, readPorts, replaceEmbedding, replacePorts,
      h12, h17, hassignment, hprocessed, hold, hnew, h13, h14, h15, h16]
    exact hassigned
  have heq : e = afterWordUpdate d assigned new rest := by
    apply congrArg₂ StructuredProgram.State.mk
    · simp [ c, r, readRegs_reset]
    · funext j
      simp only [ c, r, ArrayUpdateLifted.replaceStacksAt,
        ArrayUpdateLifted.readStacksAt, copyStacks, readEmbedding, readPorts,
        replaceEmbedding, replacePorts]
      by_cases h7 : j = 7 <;> by_cases h12j : j = 12 <;>
        by_cases h17j : j = 17 <;> by_cases h8 : j = 8 <;>
        subst_vars <;> simp_all []
  rw [← heq]
  exact hr.seq (hc.seq hrpl)

abbrev peeked (d : Data) : Data :=
  ⟨readRegs d.regs 9 10 (d.stacks 11).head?, d.stacks⟩

abbrev dropped (d : Data) : Data :=
  ⟨readRegs d.regs 9 10 (d.stacks 11).head?,
    Function.update d.stacks 11 (d.stacks 11).tail⟩

theorem peek_eval (d : Data) : Eval peekRemaining 1 d (peeked d) := by
  exact .base (.atom _ _)

theorem drop_eval (d : Data) : Eval dropRemaining 1 d (dropped d) := by
  exact .base (.atom _ _)

def scratchPorts : Finset (Fin 48) := {0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15, 16, 17, 18}

/-- All mathematical values in this invariant describe concrete packed
arrays or lengths of concrete unary stacks. -/
structure Memory {A : Type*} (encode : A → List Bool) (a : A) (tail : List A)
    (remaining : ℕ) (fixed : List A) (stk : Fin 48 → List Bool) : Prop where
  assignment : stk 8 = (fixed.reverse.map encode ++ List.replicate remaining (encode a)).flatten
  alphabet : stk 9 = ((a :: tail).map encode).flatten
  width : (stk 10).length = (encode a).length
  processed : (stk 19).length = fixed.length
  scratch : ∀ j ∈ scratchPorts, stk j = []

/-- Runtime read-only tables and restored scratch outside the controller ABI. -/
def HighState (environment stk : Fin 48 → List Bool) : Prop :=
  ∀ j, 20 ≤ j.val → stk j = environment j

theorem highState_counter_update {environment stk : Fin 48 → List Bool}
    (h : HighState environment stk) (counter : List Bool) :
    HighState environment (Function.update stk 11 counter) := by
  intro j hj
  have hne : j ≠ 11 := by intro heq; subst j; omega
  simpa [hne] using h j hj

theorem memory_counter_update {A : Type*} {encode : A → List Bool} {a : A}
    {tail : List A} {n : ℕ} {fixed : List A} {stk : Fin 48 → List Bool}
    (h : Memory encode a tail n fixed stk) (counter : List Bool) :
    Memory encode a tail n fixed (Function.update stk 11 counter) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa using h.assignment
  · simpa using h.alphabet
  · simpa using h.width
  · simpa using h.processed
  · intro j hj
    have hj11 : j ≠ 11 := by
      intro heq
      subst j
      exact (show (11 : Fin 48) ∉ scratchPorts by decide) hj
    simpa [hj11] using h.scratch j hj

/-- A compositional contract for the displayed, fixed step code. Its
premise is an actual instruction execution, never an atomic score oracle. -/
abbrev StepRefines {A : Type*} (encode : A → List Bool) (a : A) (tail : List A)
    (evaluate : ℕ → List A → ℕ) (scoreBuilder : Cmd 16 48) (budget total : ℕ)
    (environment : Fin 48 → List Bool) : Prop :=
  ∀ (n : ℕ) (fixed : List A) (d : Data),
    n + 1 + fixed.length = total →
    Memory encode a tail (n + 1) fixed d.stacks →
    (d.stacks 11).length = n →
    HighState environment d.stacks →
    ∃ t ≤ budget, ∃ e : Data,
      Eval (step scoreBuilder) t d e ∧
      Memory encode a tail n
        (NaturalAssignment.chooseMinNat (fun x => evaluate n (x :: fixed)) a tail :: fixed)
        e.stacks ∧
      (e.stacks 11).length = n ∧ HighState environment e.stacks

theorem loop_eval {A : Type*} (encode : A → List Bool) (a : A) (tail : List A)
    (evaluate : ℕ → List A → ℕ) (scoreBuilder : Cmd 16 48) (budget total : ℕ)
    (environment : Fin 48 → List Bool)
    (hstep : StepRefines encode a tail evaluate scoreBuilder budget total environment)
    (n : ℕ) (fixed : List A) (d : Data)
    (hsize : n + fixed.length = total)
    (hm : Memory encode a tail n fixed d.stacks) (hc : (d.stacks 11).length = n)
    (hcontext : HighState environment d.stacks) :
    ∃ t ≤ n * (budget + 3) + 1, ∃ e : Data,
      Eval (loop scoreBuilder) t (peeked d) e ∧
      Memory encode a tail 0 (NaturalAssignment.assignNat a tail evaluate n fixed) e.stacks ∧
      e.stacks 11 = [] ∧ HighState environment e.stacks := by
  induction n generalizing fixed d with
  | zero =>
      have hz : d.stacks 11 = [] := List.length_eq_zero_iff.mp hc
      refine ⟨1, by simp, peeked d, ?_, hm, hz, hcontext⟩
      exact Eval.while_false (by simp [ hz, readRegs_present])
  | succ n ih =>
      have hnon : d.stacks 11 ≠ [] := by
        intro hz
        simp [hz] at hc
      have hg : (peeked d).regs 10 = true := by
        cases hs : d.stacks 11 with
        | nil => exact (hnon hs).elim
        | cons b bs => simp [ hs, readRegs_present]
      have hdmem : Memory encode a tail (n + 1) fixed (dropped (peeked d)).stacks :=
        memory_counter_update hm _
      have hdlen : ((dropped (peeked d)).stacks 11).length = n := by
        simp [ List.length_tail, hc]
      obtain ⟨k, hk, middle, ht, hmiddle, hmlen, hmcontext⟩ :=
        hstep n fixed (dropped (peeked d)) hsize hdmem hdlen (highState_counter_update hcontext _)
      obtain ⟨m, hmb, e, he, hem, hec, hecontext⟩ :=
        ih _ middle (by simpa [List.length_cons, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hsize) hmiddle hmlen hmcontext
      refine ⟨(1 + (k + 1)) + m + 1, ?_, e, ?_, hem, hec, hecontext⟩
      · nlinarith
      · exact Eval.while_true hg
          (Eval.seq (drop_eval (peeked d)) (Eval.seq ht (peek_eval middle))) he

/-- Every step is supplied by the actual composed instruction table. The
complete fixed loop produces the natural-choice assignment in packed form. -/
theorem program_runsIn {A : Type*} (encode : A → List Bool) (a : A) (tail : List A)
    (evaluate : ℕ → List A → ℕ) (scoreBuilder : Cmd 16 48) (budget total : ℕ)
    (environment : Fin 48 → List Bool)
    (hstep : StepRefines encode a tail evaluate scoreBuilder budget total environment)
    (n : ℕ) (fixed : List A) (d : Data)
    (hsize : n + fixed.length = total)
    (hm : Memory encode a tail n fixed d.stacks) (hc : (d.stacks 11).length = n)
    (hcontext : HighState environment d.stacks) :
    ∃ e : Data, RunsIn (program scoreBuilder) (n * (budget + 3) + 3)
      (d.withPC (some (program scoreBuilder).entry)) (e.withPC none) ∧
      e.stacks 8 =
        ((NaturalAssignment.assignNat a tail evaluate n fixed).reverse.map encode).flatten := by
  obtain ⟨t, ht, e, he, hem, _⟩ :=
    loop_eval encode a tail evaluate scoreBuilder budget total environment hstep
      n fixed d hsize hm hc hcontext
  refine ⟨e, ⟨(1 + t) + 1, by omega, ?_⟩, ?_⟩
  · exact compiled_halt_trace (Eval.seq (peek_eval d) he) 8 8
  · simpa using hem.assignment

end SubexponentialSAT.Subexp.SequentialProgram

end OAI.Algorithms
