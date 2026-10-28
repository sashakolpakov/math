import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticProducerControl
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchPreparation

namespace OAI.Algorithms

/-! # Framed arithmetic calls inside the quartic record scans -/

namespace SubexponentialSAT.SubexpQuarticCallback

open BitProgram StructuredCalls
open SubexpLiftRing SubexpQuarticRing SubexpQuarticMachine
open SubexpQuarticProducerControl
open Subexp.BlockSearchPreparation (restrictState lifted_call)

def bankPort (i : Fin 14) : Fin 35 := Fin.castAdd 21 i
def workPort (i : Fin 8) : Fin 35 := coreStacks (SubexpQuarticMachine.workPort 14 i)

def Represents (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (d : Data) (bank : Fin 14 → Word (baseWidth p μ)) : Prop :=
  (∀ i, d.stacks (bankPort i) = (bank i).val) ∧
  (∀ i, d.stacks (workPort i) = scalarWork [] [] M.bits i) ∧ d.stacks 22 = []

theorem coreRegisters_injective : Function.Injective coreRegisters := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 14 => k.val) h)

theorem coreStacks_injective : Function.Injective coreStacks := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 35 => k.val) h)

@[simp] theorem coreStack_bank (i : Fin 14) :
    coreStacks (SubexpQuarticMachine.bankPort i) = bankPort i := rfl

@[simp] theorem coreStack_temp : coreStacks (tempPort 14) = 22 := rfl

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

theorem restrict_eq (d : Data) (bank : Fin 14 → Word (baseWidth p μ))
    (hd : Represents p μ M d bank) :
    restrictState coreRegisters coreStacks d =
      restingState (d.regs ∘ coreRegisters) bank M.bits := by
  apply SubexpScanPrimitives.state_ext
  · rfl
  · apply SubexpQuarticMachine.store_ext
    · intro i
      simpa only [restrictState, Function.comp_apply, coreStack_bank,
        restingState_bank] using hd.1 i
    · intro i
      simpa only [restrictState, Function.comp_apply, restingState, store_work,
        workPort] using hd.2.1 i
    · simpa only [restrictState, Function.comp_apply, coreStack_temp,
        restingState, store_temp] using hd.2.2

theorem embed_represents (d : Data) (regs : Fin 8 → Bool)
    (bank : Fin 14 → Word (baseWidth p μ)) :
    Represents p μ M
      (embedState coreRegisters coreStacks d (restingState regs bank M.bits)) bank := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simpa only [coreStack_bank, restingState_bank] using
      embedState_stack coreRegisters coreStacks d (restingState regs bank M.bits)
        coreStacks_injective (SubexpQuarticMachine.bankPort i)
  · intro i
    simpa only [workPort, restingState, store_work] using
      embedState_stack coreRegisters coreStacks d (restingState regs bank M.bits)
        coreStacks_injective (SubexpQuarticMachine.workPort 14 i)
  · simpa only [coreStack_temp, restingState, store_temp] using
      embedState_stack coreRegisters coreStacks d (restingState regs bank M.bits)
        coreStacks_injective (tempPort 14)

theorem embed_register_frame (d : Data) (e : State 8 23) (j : Fin 14)
    (hj : 8 ≤ j.val) :
    (embedState coreRegisters coreStacks d e).regs j = d.regs j := by
  apply StructuredCalls.embedState_register_frame
  rintro ⟨i, hi⟩
  have he := congrArg Fin.val hi
  change i.val = j.val at he
  omega

theorem embed_stack_frame (d : Data) (e : State 8 23) (j : Fin 35)
    (hj : 23 ≤ j.val) :
    (embedState coreRegisters coreStacks d e).stacks j = d.stacks j := by
  apply StructuredCalls.embedState_stack_frame
  rintro ⟨i, hi⟩
  have he := congrArg Fin.val hi
  change i.val = j.val at he
  omega

theorem linear_call (d : Data) (bank : Fin 14 → Word (baseWidth p μ))
    (hd : Represents p μ M d bank) (hminus : wordValue p μ (bank 6) = -1) :
    ∃ n next,
      n ≤ 50000 * (baseWidth p μ + 1)^2 + 1 ∧ Eval linearTest n d next ∧
      Represents p μ M next (scriptEval p μ M SubexpQuarticSharedTest.linearScript bank) ∧
      next.regs 2 = QuarticSearch.linearPass (p^μ)
        (fun i => wordValue p μ (![bank 0, bank 1, bank 2, bank 3] i))
        (wordValue p μ (bank 4)) ∧
      (∀ i : Fin 7, next.stacks (bankPort (Fin.castAdd 7 i)) =
        d.stacks (bankPort (Fin.castAdd 7 i))) ∧
      (∀ j : Fin 14, 8 ≤ j.val → next.regs j = d.regs j) ∧
      (∀ j : Fin 35, 23 ≤ j.val → next.stacks j = d.stacks j) := by
  obtain ⟨regs, hr, hf⟩ := SubexpQuarticSharedTest.linear_run p μ M
    (d.regs ∘ coreRegisters) bank hminus
  rw [← restrict_eq p μ M d bank hd] at hr
  let e := restingState regs (scriptEval p μ M SubexpQuarticSharedTest.linearScript bank) M.bits
  obtain ⟨n, hn, he⟩ := lifted_call SubexpQuarticSharedTest.linearProgram
    coreRegisters coreStacks coreRegisters_injective coreStacks_injective d e _ hr
  let next := embedState coreRegisters coreStacks d e
  have hnext : Represents p μ M next
      (scriptEval p μ M SubexpQuarticSharedTest.linearScript bank) :=
    embed_represents p μ M d regs _
  refine ⟨n, next, hn, he, hnext, ?_, ?_, ?_, ?_⟩
  · have h := embedState_register coreRegisters coreStacks d e coreRegisters_injective 2
    exact h.trans hf
  · intro i
    rw [hnext.1, SubexpQuarticSharedTest.linearScript_preserves, hd.1]
  · exact embed_register_frame d e
  · exact embed_stack_frame d e

theorem quadratic_call (d : Data) (bank : Fin 14 → Word (baseWidth p μ))
    (hd : Represents p μ M d bank) (hminus : wordValue p μ (bank 6) = -1) :
    ∃ n next,
      n ≤ 75000 * (baseWidth p μ + 1)^2 + 1 ∧ Eval quadraticTest n d next ∧
      Represents p μ M next (scriptEval p μ M SubexpQuarticDivisorMachine.quadraticScript bank) ∧
      next.regs 2 = QuarticSearch.quadraticPass (p^μ)
        (fun i => wordValue p μ (![bank 0, bank 1, bank 2, bank 3] i))
        (fun i => wordValue p μ (![bank 4, bank 5] i)) ∧
      (∀ i : Fin 7, next.stacks (bankPort (Fin.castAdd 7 i)) =
        d.stacks (bankPort (Fin.castAdd 7 i))) ∧
      (∀ j : Fin 14, 8 ≤ j.val → next.regs j = d.regs j) ∧
      (∀ j : Fin 35, 23 ≤ j.val → next.stacks j = d.stacks j) := by
  obtain ⟨regs, hr, hf⟩ := SubexpQuarticSharedTest.quadratic_run p μ M
    (d.regs ∘ coreRegisters) bank hminus
  rw [← restrict_eq p μ M d bank hd] at hr
  let e := restingState regs
    (scriptEval p μ M SubexpQuarticDivisorMachine.quadraticScript bank) M.bits
  obtain ⟨n, hn, he⟩ := lifted_call SubexpQuarticTestMachine.quadraticProgram
    coreRegisters coreStacks coreRegisters_injective coreStacks_injective d e _ hr
  let next := embedState coreRegisters coreStacks d e
  have hnext : Represents p μ M next
      (scriptEval p μ M SubexpQuarticDivisorMachine.quadraticScript bank) :=
    embed_represents p μ M d regs _
  refine ⟨n, next, hn, he, hnext, ?_, ?_, ?_, ?_⟩
  · have h := embedState_register coreRegisters coreStacks d e coreRegisters_injective 2
    exact h.trans hf
  · intro i
    rw [hnext.1, SubexpQuarticDivisorMachine.quadraticScript_preserves, hd.1]
  · exact embed_register_frame d e
  · exact embed_stack_frame d e

def wordAssignments (words : List (Fin 14 × Word (baseWidth p μ))) :
    List (Fin 35 × List Bool) := words.map (fun item => (bankPort item.1, item.2.val))

omit [Fact (Nat.Prime p)] in
theorem assignment_small (words : List (Fin 14 × Word (baseWidth p μ)))
    (item : Fin 35 × List Bool) (h : item ∈ wordAssignments p μ words) :
    item.1.val < 14 := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
  exact a.1.isLt

theorem bankPort_ne_large (i : Fin 14) (j : Fin 35) (hj : 14 ≤ j.val) :
    bankPort i ≠ j := by
  intro h
  have he := congrArg Fin.val h
  change i.val = j.val at he
  omega

theorem workPort_range (i : Fin 8) : 14 ≤ (workPort i).val ∧ (workPort i).val < 22 := by
  change 14 ≤ 14 + i.val ∧ 14 + i.val < 22
  omega

theorem loader_distinct (i : Fin 14) : Function.Injective
    (![31, 32, 22, 30, bankPort i] : Fin 5 → Fin 35) := by
  intro a b h
  have hi := i.isLt
  fin_cases a <;> fin_cases b <;> first
  | rfl
  | have hv := congrArg (fun j : Fin 35 => j.val) h
    norm_num [bankPort] at hv <;> omega

omit [Fact (Nat.Prime p)] in
theorem assignment_not_large (words : List (Fin 14 × Word (baseWidth p μ)))
    (j : Fin 35) (hj : 14 ≤ j.val) :
    j ∉ (wordAssignments p μ words).map Prod.fst := by
  intro h
  obtain ⟨item, hitem, he⟩ := List.mem_map.mp h
  have hs := assignment_small p μ words item hitem
  rw [he] at hs
  omega

/-- The common parser-payload loader leaves a represented scalar bank, while
framing all persistent enumerations and the enclosing iterator registers. -/
theorem load_call (d : Data) (bank : Fin 14 → Word (baseWidth p μ))
    (hd : Represents p μ M d bank)
    (words : List (Fin 14 × Word (baseWidth p μ)))
    (hnodup : (words.map Prod.fst).Nodup)
    (hinput : d.stacks 24 = (SubexpQuarticRecordLoad.payload (wordAssignments p μ words)).reverse)
    (hsource : d.stacks 30 = []) (hcounter : d.stacks 32 = [])
    (hwidth : (d.stacks 31).length = baseWidth p μ) :
    ∃ next nextBank,
      Eval (SubexpQuarticRecordLoad.readRecord 31 32 22 30 24 0 1
        ((wordAssignments p μ words).map Prod.fst))
        (words.length * (19 * baseWidth p μ + 14) + 3) d next ∧
      Represents p μ M next nextBank ∧ next.stacks 24 = [] ∧ next.stacks 30 = [] ∧
      (∀ item ∈ words, next.stacks (bankPort item.1) = item.2.val) ∧
      (∀ i : Fin 14, i ∉ words.map Prod.fst →
        next.stacks (bankPort i) = d.stacks (bankPort i)) ∧
      (∀ j : Fin 35, 14 ≤ j.val → j ≠ 24 → j ≠ 30 → next.stacks j = d.stacks j) ∧
      (∀ j : Fin 14, j ≠ 0 → j ≠ 1 → next.regs j = d.regs j) := by
  let assignments := wordAssignments p μ words
  let d₁ := SubexpScanPrimitives.afterTransfer d 24 30 0 1
  let next := SubexpQuarticRecordLoad.loaded 30 0 1 [] d₁ assignments
  have hassignmentWidth : ∀ item ∈ assignments, item.2.length = baseWidth p μ := by
    intro item hitem
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hitem
    exact a.2.property
  have hdistinct : ∀ item ∈ assignments, Function.Injective
      (![31, 32, 22, 30, item.1] : Fin 5 → Fin 35) := by
    intro item hitem
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hitem
    exact loader_distinct a.1
  have hnodup' : (assignments.map Prod.fst).Nodup := by
    have hinj : Function.Injective bankPort :=
      fun i j h => Fin.ext (congrArg (fun k : Fin 35 => k.val) h)
    simpa only [assignments, wordAssignments, List.map_map, Function.comp_def] using
      hnodup.map hinj
  have hframe₁ : ∀ j : Fin 35, j ≠ 24 → j ≠ 30 → d₁.stacks j = d.stacks j := by
    intro j h24 h30
    simp [d₁, SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks, h24, h30]
  have hbankWidth : ∀ i : Fin 14, (d₁.stacks (bankPort i)).length = baseWidth p μ := by
    intro i
    rw [hframe₁ _ (bankPort_ne_large i 24 (by decide)) (bankPort_ne_large i 30 (by decide)), hd.1]
    exact (bank i).property
  have hnextWidth : ∀ i : Fin 14, (next.stacks (bankPort i)).length = baseWidth p μ := by
    intro i
    exact SubexpQuarticRecordLoad.loaded_stack_length 30 0 1 [] d₁ assignments
      (baseWidth p μ) (bankPort i) (bankPort_ne_large i 30 (by decide))
      (hbankWidth i) hassignmentWidth
  let nextBank : Fin 14 → Word (baseWidth p μ) := fun i => ⟨next.stacks (bankPort i), hnextWidth i⟩
  have hframe : ∀ j : Fin 35, 14 ≤ j.val → j ≠ 24 → j ≠ 30 →
      next.stacks j = d.stacks j := by
    intro j hj h24 h30
    exact (SubexpQuarticRecordLoad.loaded_stack_frame 30 0 1 [] d₁ assignments j h30
      (assignment_not_large p μ words j hj)).trans (hframe₁ j h24 h30)
  have hrep : Represents p μ M next nextBank := by
    refine ⟨fun _ => rfl, ?_, ?_⟩
    · intro i
      have hi := workPort_range i
      have h24 : workPort i ≠ 24 := by intro h; have := congrArg Fin.val h; omega
      have h30 : workPort i ≠ 30 := by intro h; have := congrArg Fin.val h; omega
      exact (hframe _ hi.1 h24 h30).trans (hd.2.1 i)
    · exact (hframe 22 (by decide) (by decide) (by decide)).trans hd.2.2
  have hrun := SubexpQuarticRecordLoad.readRecord_eval 31 32 22 30 24 0 1
    (by decide) (by decide) (by decide) (by decide) (by decide)
    assignments hdistinct hnodup' (assignment_not_large p μ words 24 (by decide))
    d (baseWidth p μ) hsource hinput hcounter hd.2.2 hwidth
    (by
      intro item hitem
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hitem
      exact ⟨a.2.property, by rw [hd.1]; exact (bank a.1).property⟩)
    (by decide) (by decide) (by decide)
  refine ⟨next, nextBank, ?_, hrep, ?_, ?_, ?_, ?_, hframe, ?_⟩
  · simpa only [next, d₁, assignments, wordAssignments, List.length_map] using hrun
  · have h24 : d₁.stacks 24 = [] := by
      simp [d₁, SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks]
    exact (SubexpQuarticRecordLoad.loaded_stack_frame 30 0 1 [] d₁ assignments 24 (by decide)
      (assignment_not_large p μ words 24 (by decide))).trans h24
  · apply SubexpQuarticRecordLoad.loaded_stack_source 30 0 1 [] d₁ assignments
      (assignment_not_large p μ words 30 (by decide))
    simp [d₁, SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks,
      hinput, hsource, assignments]
  · intro item hitem
    exact SubexpQuarticRecordLoad.loaded_stack_member 30 0 1 [] d₁ assignments
      hnodup' (assignment_not_large p μ words 30 (by decide))
      (bankPort item.1, item.2.val) (List.mem_map.mpr ⟨item, hitem, rfl⟩)
  · intro i hi
    have hn : bankPort i ∉ assignments.map Prod.fst := by
      intro h
      obtain ⟨a, ha, he⟩ := List.mem_map.mp h
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      have hbi : b.1 = i := Fin.ext (congrArg (fun k : Fin 35 => k.val) he)
      exact hi (List.mem_map.mpr ⟨b, hb, hbi⟩)
    exact (SubexpQuarticRecordLoad.loaded_stack_frame 30 0 1 [] d₁ assignments
      (bankPort i) (bankPort_ne_large i 30 (by decide)) hn).trans
      (hframe₁ _ (bankPort_ne_large i 24 (by decide)) (bankPort_ne_large i 30 (by decide)))
  · intro j h0 h1
    exact (SubexpQuarticRecordLoad.loaded_register_frame 30 0 1 [] d₁ assignments j h0 h1).trans
      (StackRoutines.readRegs_frame d.regs 0 1 j none h0 h1)

def finishResult (d : Data) : Data :=
  (StructuredProgram.Atom.set (9 : Fin 14) true).eval
    ((StructuredProgram.Atom.set (8 : Fin 14) false).eval
      ((StructuredProgram.Atom.copy (10 : Fin 14) 2).eval d))

theorem finish_eval (d : Data) : Eval finishInner 3 d (finishResult d) := by
  let a := (StructuredProgram.Atom.copy (10 : Fin 14) 2).eval d
  let b := (StructuredProgram.Atom.set (8 : Fin 14) false).eval a
  have he := (Eval.base (StructuredProgram.Eval.atom (.copy (10 : Fin 14) 2) d)).seq
    ((Eval.base (StructuredProgram.Eval.atom (.set (8 : Fin 14) false) a)).seq
      (Eval.base (StructuredProgram.Eval.atom (.set (9 : Fin 14) true) b)))
  exact he

@[simp] theorem finish_stacks (d : Data) : (finishResult d).stacks = d.stacks := rfl

theorem finish_flags (d : Data) :
    (finishResult d).regs 8 = false ∧ (finishResult d).regs 9 = true ∧
      (finishResult d).regs 10 = d.regs 2 := by
  simp [finishResult, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr]

theorem finish_register_frame (d : Data) (j : Fin 14) (hj : 11 ≤ j.val) :
    (finishResult d).regs j = d.regs j := by
  have h8 : j ≠ 8 := by intro h; have := congrArg Fin.val h; omega
  have h9 : j ≠ 9 := by intro h; have := congrArg Fin.val h; omega
  have h10 : j ≠ 10 := by intro h; have := congrArg Fin.val h; omega
  simp [finishResult, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr, h8, h9, h10]

/-- One complete linear-divisor callback, including consuming the parser
payload and restoring the record iterator's control registers. -/
theorem linear_callback_eval (d : Data) (bank : Fin 14 → Word (baseWidth p μ))
    (hd : Represents p μ M d bank) (hminus : wordValue p μ (bank 6) = -1)
    (x : Word (baseWidth p μ)) (hinput : d.stacks 24 = x.val.reverse)
    (hsource : d.stacks 30 = []) (hcounter : d.stacks 32 = [])
    (hwidth : (d.stacks 31).length = baseWidth p μ) :
    ∃ n next nextBank,
      n ≤ 51000 * (baseWidth p μ + 1)^2 ∧ Eval linearCallback n d next ∧
      Represents p μ M next nextBank ∧
      next.regs 8 = false ∧ next.regs 9 = true ∧
      next.regs 10 = QuarticSearch.linearPass (p^μ)
        (fun i => wordValue p μ (![bank 0, bank 1, bank 2, bank 3] i))
        (wordValue p μ x) ∧
      next.stacks 24 = [] ∧ next.stacks 30 = [] ∧
      (∀ i : Fin 7, i ≠ 4 → next.stacks (bankPort (Fin.castAdd 7 i)) =
        d.stacks (bankPort (Fin.castAdd 7 i))) ∧
      (∀ j : Fin 35, 23 ≤ j.val → j ≠ 24 → j ≠ 30 → next.stacks j = d.stacks j) ∧
      (∀ j : Fin 14, 11 ≤ j.val → next.regs j = d.regs j) := by
  obtain ⟨a, b, hl, hb, ha24, ha30, hasgn, hunch, haf, har⟩ :=
    load_call p μ M d bank hd [(4, x)] (by simp)
      (by simpa [wordAssignments, SubexpQuarticRecordLoad.payload] using hinput)
      hsource hcounter hwidth
  have hvalue : ∀ i : Fin 14, i ≠ 4 → wordValue p μ (b i) = wordValue p μ (bank i) := by
    intro i hi
    unfold wordValue
    rw [← hb.1 i, hunch i (by simpa using hi), hd.1 i]
  have hx : wordValue p μ (b 4) = wordValue p μ x := by
    unfold wordValue
    rw [← hb.1 4, hasgn (4, x) (by simp)]
  have hbminus : wordValue p μ (b 6) = -1 := (hvalue 6 (by decide)).trans hminus
  obtain ⟨m, z, hm, hc, hz, hf, hzi, hzr, hzs⟩ := linear_call p μ M a b hb hbminus
  have hcvalues : (fun i => wordValue p μ (![b 0, b 1, b 2, b 3] i)) =
      (fun i => wordValue p μ (![bank 0, bank 1, bank 2, bank 3] i)) := by
    funext i
    fin_cases i <;> exact hvalue _ (by decide)
  rw [hcvalues, hx] at hf
  let next := finishResult z
  have hnext : Represents p μ M next
      (scriptEval p μ M SubexpQuarticSharedTest.linearScript b) := by
    simpa only [Represents, next, finish_stacks] using hz
  have hload : Eval (SubexpQuarticRecordLoad.readRecord 31 32 22 30 24 0 1 [4])
      (19 * baseWidth p μ + 17) d a := by
    simpa [wordAssignments, bankPort, Nat.add_assoc] using hl
  refine ⟨(19 * baseWidth p μ + 17) + (m + 3), next,
    scriptEval p μ M SubexpQuarticSharedTest.linearScript b, ?_,
    hload.seq (hc.seq (finish_eval z)), hnext,
    (finish_flags z).1, (finish_flags z).2.1, (finish_flags z).2.2.trans hf,
    ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith only [hm, Nat.zero_le (baseWidth p μ)]
  · exact (hzs 24 (by decide)).trans ha24
  · exact (hzs 30 (by decide)).trans ha30
  · intro i hi
    have hi' : (Fin.castAdd 7 i : Fin 14) ≠ 4 := by
      intro h
      apply hi
      exact Fin.ext (congrArg (fun k : Fin 14 => k.val) h)
    exact (hzi i).trans (hunch (Fin.castAdd 7 i) (by simpa using hi'))
  · intro j hj h24 h30
    exact (hzs j hj).trans (haf j (by omega) h24 h30)
  · intro j hj
    have h0 : j ≠ 0 := by intro h; have := congrArg Fin.val h; omega
    have h1 : j ≠ 1 := by intro h; have := congrArg Fin.val h; omega
    exact (finish_register_frame z j hj).trans ((hzr j (by omega)).trans (har j h0 h1))

/-- The quadratic callback shares the same bank and iterator boundary as the
linear callback, loading its two divisor coefficients on words four and five. -/
theorem quadratic_callback_eval (d : Data) (bank : Fin 14 → Word (baseWidth p μ))
    (hd : Represents p μ M d bank) (hminus : wordValue p μ (bank 6) = -1)
    (x₀ x₁ : Word (baseWidth p μ))
    (hinput : d.stacks 24 = (x₀.val ++ x₁.val).reverse)
    (hsource : d.stacks 30 = []) (hcounter : d.stacks 32 = [])
    (hwidth : (d.stacks 31).length = baseWidth p μ) :
    ∃ n next nextBank,
      n ≤ 76000 * (baseWidth p μ + 1)^2 ∧ Eval quadraticCallback n d next ∧
      Represents p μ M next nextBank ∧
      next.regs 8 = false ∧ next.regs 9 = true ∧
      next.regs 10 = QuarticSearch.quadraticPass (p^μ)
        (fun i => wordValue p μ (![bank 0, bank 1, bank 2, bank 3] i))
        ![wordValue p μ x₀, wordValue p μ x₁] ∧
      next.stacks 24 = [] ∧ next.stacks 30 = [] ∧
      (∀ i : Fin 7, i ≠ 4 → i ≠ 5 → next.stacks (bankPort (Fin.castAdd 7 i)) =
        d.stacks (bankPort (Fin.castAdd 7 i))) ∧
      (∀ j : Fin 35, 23 ≤ j.val → j ≠ 24 → j ≠ 30 → next.stacks j = d.stacks j) ∧
      (∀ j : Fin 14, 11 ≤ j.val → next.regs j = d.regs j) := by
  obtain ⟨a, b, hl, hb, ha24, ha30, hasgn, hunch, haf, har⟩ :=
    load_call p μ M d bank hd [(4, x₀), (5, x₁)] (by simp)
      (by simpa [wordAssignments, SubexpQuarticRecordLoad.payload] using hinput)
      hsource hcounter hwidth
  have hvalue : ∀ i : Fin 14, i ≠ 4 → i ≠ 5 →
      wordValue p μ (b i) = wordValue p μ (bank i) := by
    intro i h4 h5
    unfold wordValue
    rw [← hb.1 i, hunch i (by simp [h4, h5]), hd.1 i]
  have hx₀ : wordValue p μ (b 4) = wordValue p μ x₀ := by
    unfold wordValue
    rw [← hb.1 4, hasgn (4, x₀) (by simp)]
  have hx₁ : wordValue p μ (b 5) = wordValue p μ x₁ := by
    unfold wordValue
    rw [← hb.1 5, hasgn (5, x₁) (by simp)]
  have hbminus : wordValue p μ (b 6) = -1 :=
    (hvalue 6 (by decide) (by decide)).trans hminus
  obtain ⟨m, z, hm, hc, hz, hf, hzi, hzr, hzs⟩ := quadratic_call p μ M a b hb hbminus
  have hcvalues : (fun i => wordValue p μ (![b 0, b 1, b 2, b 3] i)) =
      (fun i => wordValue p μ (![bank 0, bank 1, bank 2, bank 3] i)) := by
    funext i
    fin_cases i <;> exact hvalue _ (by decide) (by decide)
  have hxvalues : (fun i => wordValue p μ (![b 4, b 5] i)) =
      ![wordValue p μ x₀, wordValue p μ x₁] := by
    funext i
    fin_cases i
    · exact hx₀
    · exact hx₁
  rw [hcvalues, hxvalues] at hf
  let next := finishResult z
  have hnext : Represents p μ M next
      (scriptEval p μ M SubexpQuarticDivisorMachine.quadraticScript b) := by
    simpa only [Represents, next, finish_stacks] using hz
  have hload : Eval (SubexpQuarticRecordLoad.readRecord 31 32 22 30 24 0 1 [4, 5])
      (38 * baseWidth p μ + 31) d a := by
    convert hl using 1
    all_goals norm_num [wordAssignments, bankPort]
    all_goals ring
  refine ⟨(38 * baseWidth p μ + 31) + (m + 3), next,
    scriptEval p μ M SubexpQuarticDivisorMachine.quadraticScript b, ?_,
    hload.seq (hc.seq (finish_eval z)), hnext,
    (finish_flags z).1, (finish_flags z).2.1, (finish_flags z).2.2.trans hf,
    ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith only [hm, Nat.zero_le (baseWidth p μ)]
  · exact (hzs 24 (by decide)).trans ha24
  · exact (hzs 30 (by decide)).trans ha30
  · intro i h4 h5
    have h4' : (Fin.castAdd 7 i : Fin 14) ≠ 4 := by
      intro h
      exact h4 (Fin.ext (congrArg (fun k : Fin 14 => k.val) h))
    have h5' : (Fin.castAdd 7 i : Fin 14) ≠ 5 := by
      intro h
      exact h5 (Fin.ext (congrArg (fun k : Fin 14 => k.val) h))
    exact (hzi i).trans (hunch (Fin.castAdd 7 i) (by simp [h4', h5']))
  · intro j hj h24 h30
    exact (hzs j hj).trans (haf j (by omega) h24 h30)
  · intro j hj
    have h0 : j ≠ 0 := by intro h; have := congrArg Fin.val h; omega
    have h1 : j ≠ 1 := by intro h; have := congrArg Fin.val h; omega
    exact (finish_register_frame z j hj).trans ((hzr j (by omega)).trans (har j h0 h1))

end SubexponentialSAT.SubexpQuarticCallback

end OAI.Algorithms
