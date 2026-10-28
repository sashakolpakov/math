import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNFSubset

namespace OAI.Algorithms

/-!
# Preserving encoded clause relations

Two invocations of the concrete subset tester compute equivalence and strict
inclusion. The original encoded clauses occupy stacks 8 and 9 throughout;
stacks 0 through 7 are empty workspace at both boundaries. Registers 10 and
11 return equivalence and strict inclusion, respectively.
-/

namespace SubexponentialSAT.ExecClauseRelationsProgram

open BitProgram StructuredCalls

abbrev Data := State 12 10

def regPort (i : Fin 10) : Fin 12 := Fin.castAdd 2 i
def stackPort (i : Fin 8) : Fin 10 := Fin.castAdd 2 i
def original (i : Fin 2) : Fin 10 := Fin.natAdd 8 i

def restrict (d : Data) : State 10 8 := ⟨d.regs ∘ regPort, d.stacks ∘ stackPort⟩

theorem regPort_injective : Function.Injective regPort := Fin.castAdd_injective 10 2
theorem stackPort_injective : Function.Injective stackPort := Fin.castAdd_injective 8 2

private theorem embed_restrict (d : Data) :
    embedState regPort stackPort d (restrict d) = d := by
  cases d with
  | mk regs stk =>
    unfold embedState restrict
    congr 1
    · funext i
      by_cases h : ∃ j, regPort j = i
      · obtain ⟨j, rfl⟩ := h
        exact regPort_injective.extend_apply _ _ _
      · exact Function.extend_apply' _ _ _ h
    · funext i
      by_cases h : ∃ j, stackPort j = i
      · obtain ⟨j, rfl⟩ := h
        exact stackPort_injective.extend_apply _ _ _
      · exact Function.extend_apply' _ _ _ h

def clean (d : Data) : Prop := ∀ i : Fin 8, d.stacks (stackPort i) = []

def subsetProgram := ProgramLinking.liftProgram ExecCNFSubset.subsetProgram regPort stackPort

/-- The subset routine has an actual trace. Its lifted call preserves the two
original clauses and the caller's two saved Boolean flags. -/
theorem subset_eval (source target : List (List Bool)) (d : Data)
    (hs : d.stacks 0 = Encoding.encodeList id source) (ho : d.stacks 1 = [])
    (hv : ExecCNFSubset.invariant target (restrict d)) :
    ∃ n ≤ 64 * ((Encoding.encodeList id target).length + 1) *
        (Encoding.encodeList id source).length + 3, ∃ e : Data,
      Eval (.call subsetProgram) n d e ∧
      ExecCNFSubset.invariant target (restrict e) ∧
      e.regs 9 = ExecCNF.subset source target ∧
      e.stacks 1 = [ExecCNF.subset source target] ∧
      (e.stacks 0).length ≤ (Encoding.encodeList id source).length ∧
      (∀ i : Fin 2, e.stacks (original i) = d.stacks (original i)) ∧
      e.regs 10 = d.regs 10 ∧ e.regs 11 = d.regs 11 := by
  obtain ⟨n, hn, b, he, hb, hr, hout, hlen⟩ :=
    ExecCNFSubset.subset_call source target (restrict d) hs ho hv
  have ht : Trace ExecCNFSubset.subsetProgram n
      ((restrict d).withPC (some ExecCNFSubset.subsetProgram.entry)) (b.withPC none) := by
    cases he with
    | call _ h => exact h
  have heval := eval_call_lifted ExecCNFSubset.subsetProgram regPort stackPort d
    regPort_injective stackPort_injective ht
  rw [embed_restrict] at heval
  let e := embedState regPort stackPort d b
  have hstack (i : Fin 8) : e.stacks (stackPort i) = b.stacks i :=
    embedState_stack _ _ _ _ stackPort_injective i
  have hreg (i : Fin 10) : e.regs (regPort i) = b.regs i :=
    embedState_register _ _ _ _ regPort_injective i
  have hre : restrict e = b := by
    cases b
    unfold restrict
    congr 1
    · funext i; exact hreg i
    · funext i; exact hstack i
  refine ⟨n, hn, e, heval, hre.symm ▸ hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hreg 9).trans hr
  · exact (hstack 1).trans hout
  · exact (congrArg List.length (hstack 0)).trans_le hlen
  · intro i
    apply embedState_stack_frame
    fin_cases i <;> decide
  · exact embedState_register_frame _ _ _ _ _ (by decide)
  · exact embedState_register_frame _ _ _ _ _ (by decide)

def copied (src dst : Fin 10) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩

abbrev copy (src dst : Fin 10) : Cmd 12 10 :=
  .call (StackRoutines.copyProgram src dst 7 0 1)

theorem copy_eval (src dst : Fin 10) (d : Data)
    (hsd : src ≠ dst) (hst : src ≠ 7) (htd : (7 : Fin 10) ≠ dst)
    (htmp : d.stacks 7 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (copied src dst d) := by
  have h := StackRoutines.copyProgram_trace src dst 7 (0 : Fin 12) 1
    hsd hst htd (by decide) d.regs d.stacks htmp
  have hh := StackRoutines.halt_after_trace _ h 7 rfl rfl
  apply Eval.call
  simpa [copied, StackRoutines.copyResult, StructuredProgram.State.withPC,
    StackRoutines.copyProgram, Nat.add_assoc] using hh

def cleared (port : Fin 10) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks port d.stacks⟩

abbrev clear (port : Fin 10) : Cmd 12 10 := .call (StackRoutines.clearProgram port 0 1)

theorem clear_eval (port : Fin 10) (d : Data) :
    Eval (clear port) (2 * (d.stacks port).length + 3) d (cleared port d) := by
  have h := StackRoutines.clearProgram_trace port (0 : Fin 12) 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 2 rfl rfl
  apply Eval.call
  simpa [cleared, StackRoutines.clearResult, StructuredProgram.State.withPC,
    StackRoutines.clearProgram, Nat.add_assoc] using hh

abbrev compare (i j : Fin 2) : Cmd 12 10 :=
  .seq (copy (original i) 0) (.seq (copy (original j) 2)
    (.seq (.call subsetProgram) (.seq (clear 0) (.seq (clear 1) (clear 2)))))

def compareBound (source target : List (List Bool)) : ℕ :=
  80 * ((Encoding.encodeList id source).length + 1) *
    ((Encoding.encodeList id target).length + 1)

/-- A complete directional comparison restores all workspace, so the same
fixed routine can be invoked with the clause ports interchanged. -/
theorem compare_eval (source target : List (List Bool)) (i j : Fin 2) (d : Data)
    (hs : d.stacks (original i) = Encoding.encodeList id source)
    (ht : d.stacks (original j) = Encoding.encodeList id target) (hc : clean d) :
    ∃ n ≤ compareBound source target, ∃ e : Data,
      Eval (compare i j) n d e ∧ clean e ∧
      e.regs 9 = ExecCNF.subset source target ∧
      (∀ k : Fin 2, e.stacks (original k) = d.stacks (original k)) ∧
      e.regs 10 = d.regs 10 ∧ e.regs 11 = d.regs 11 := by
  have hi0 : original i ≠ 0 := by fin_cases i <;> decide
  have hi7 : original i ≠ 7 := by fin_cases i <;> decide
  have hj2 : original j ≠ 2 := by fin_cases j <;> decide
  have hj7 : original j ≠ 7 := by fin_cases j <;> decide
  have hj0 : original j ≠ 0 := by fin_cases j <;> decide
  let a := copied (original i) 0 d
  let b := copied (original j) 2 a
  have hc0 : d.stacks 0 = [] := hc 0
  have hc1 : d.stacks 1 = [] := hc 1
  have hc2 : d.stacks 2 = [] := hc 2
  have hc7 : d.stacks 7 = [] := hc 7
  have ha7 : a.stacks 7 = [] := by simpa [a, copied, StackRoutines.copyStacks] using hc7
  have haj : a.stacks (original j) = Encoding.encodeList id target := by
    simpa [a, copied, StackRoutines.copyStacks, hj0] using ht
  have hb0 : b.stacks 0 = Encoding.encodeList id source := by
    simp [b, a, copied, StackRoutines.copyStacks, hs, hc0]
  have hb1 : b.stacks 1 = [] := by
    simpa [b, a, copied, StackRoutines.copyStacks] using hc1
  have hbv : ExecCNFSubset.invariant target (restrict b) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [restrict, stackPort, b, a, copied, StackRoutines.copyStacks, hj0, ht, hc2]
    · simpa [restrict, stackPort, b, a, copied, StackRoutines.copyStacks] using hc 3
    · simpa [restrict, stackPort, b, a, copied, StackRoutines.copyStacks] using hc 4
    · simpa [restrict, stackPort, b, a, copied, StackRoutines.copyStacks] using hc 5
    · simpa [restrict, stackPort, b, a, copied, StackRoutines.copyStacks] using hc 6
    · simpa [restrict, stackPort, b, a, copied, StackRoutines.copyStacks] using hc 7
  obtain ⟨m, hm, e, he, hv, hr, hout, hlen, hframe, h10, h11⟩ :=
    subset_eval source target b hb0 hb1 hbv
  let result := cleared 2 (cleared 1 (cleared 0 e))
  let count := (7 * (d.stacks (original i)).length + 5) +
    ((7 * (a.stacks (original j)).length + 5) +
      (m + ((2 * (e.stacks 0).length + 3) +
        ((2 * (e.stacks 1).length + 3) + (2 * (e.stacks 2).length + 3)))))
  have he2 : e.stacks 2 = Encoding.encodeList id target := hv.1
  refine ⟨count, ?_, result, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [count, compareBound]
    rw [hs, haj, hout, he2]
    simp only [List.length_cons, List.length_nil]
    nlinarith
  · apply Eval.seq (copy_eval _ _ d hi0 hi7 (by decide) hc7)
    apply Eval.seq (copy_eval _ _ a hj2 hj7 (by decide) ha7)
    apply Eval.seq he
    apply Eval.seq (clear_eval 0 e)
    apply Eval.seq (clear_eval 1 (cleared 0 e))
    simpa [result, cleared, StackRoutines.clearStacks] using
      clear_eval 2 (cleared 1 (cleared 0 e))
  · intro k
    fin_cases k
    · simp [result, cleared, StackRoutines.clearStacks, stackPort]
    · simp [result, cleared, StackRoutines.clearStacks, stackPort]
    · simp [result, cleared, StackRoutines.clearStacks, stackPort]
    · simpa [result, cleared, StackRoutines.clearStacks, restrict, stackPort] using hv.2.1
    · simpa [result, cleared, StackRoutines.clearStacks, restrict, stackPort] using hv.2.2.1
    · simpa [result, cleared, StackRoutines.clearStacks, restrict, stackPort] using hv.2.2.2.1
    · simpa [result, cleared, StackRoutines.clearStacks, restrict, stackPort] using hv.2.2.2.2.1
    · simpa [result, cleared, StackRoutines.clearStacks, restrict, stackPort] using hv.2.2.2.2.2
  · simpa [result, cleared, readRegs] using hr
  · intro k
    have hk0 : original k ≠ 0 := by fin_cases k <;> decide
    have hk1 : original k ≠ 1 := by fin_cases k <;> decide
    have hk2 : original k ≠ 2 := by fin_cases k <;> decide
    simpa [result, cleared, StackRoutines.clearStacks, b, a, copied,
      StackRoutines.copyStacks, hk0, hk1, hk2] using hframe k
  · simpa [result, cleared, readRegs, b, a, copied] using h10
  · simpa [result, cleared, readRegs, b, a, copied] using h11

def saved (d : Data) : Data :=
  ⟨Function.update d.regs 11 (d.regs 9), d.stacks⟩

abbrev save : Cmd 12 10 := RecordPrograms.atom (.copy 11 9)

theorem save_eval (d : Data) : Eval save 1 d (saved d) :=
  .base (.atom _ _)

abbrev combine : Cmd 12 10 :=
  .seq (RecordPrograms.atom (.band 10 11 9))
    (.seq (RecordPrograms.atom (.bnot 9 9)) (RecordPrograms.atom (.band 11 11 9)))

def combined (d : Data) : Data :=
  (StructuredProgram.Atom.band 11 11 9).eval
    ((StructuredProgram.Atom.bnot 9 9).eval ((StructuredProgram.Atom.band 10 11 9).eval d))

theorem combine_eval (d : Data) : Eval combine 3 d (combined d) :=
  .seq (.base (.atom _ _)) (.seq (.base (.atom _ _)) (.base (.atom _ _)))

@[simp] theorem combined_stacks (d : Data) : (combined d).stacks = d.stacks := rfl

@[simp] theorem combined_equivalent (d : Data) :
    (combined d).regs 10 = (d.regs 11 && d.regs 9) := by
  simp [combined, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]

@[simp] theorem combined_strict (d : Data) :
    (combined d).regs 11 = (d.regs 11 && !d.regs 9) := by
  simp [combined, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]

@[simp] theorem combined_reverse (d : Data) : (combined d).regs 9 = !d.regs 9 := by
  simp [combined, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]

abbrev command : Cmd 12 10 :=
  .seq (compare 0 1) (.seq save (.seq (compare 1 0) combine))

/-- One finite instruction table serves every pair of encoded clauses. -/
def program := compiled command 8 0

def bound (source target : List (List Bool)) : ℕ :=
  160 * ((Encoding.encodeList id source).length + 1) *
    ((Encoding.encodeList id target).length + 1) + 5

/-- Every copy, subset test, stack cleanup, and Boolean instruction contributes
to this measured polynomial bound. -/
theorem command_eval (source target : List (List Bool)) (d : Data)
    (hs : d.stacks 8 = Encoding.encodeList id source)
    (ht : d.stacks 9 = Encoding.encodeList id target) (hc : clean d) :
    ∃ n, n + 1 ≤ bound source target ∧ ∃ e : Data,
      Eval command n d e ∧ clean e ∧
      e.regs 10 = ExecCNF.equivalent source target ∧
      e.regs 11 = ExecCNF.strictSubset source target ∧
      (∀ i : Fin 2, e.stacks (original i) = d.stacks (original i)) := by
  obtain ⟨n, hn, e, he, hclean, hforward, hframe, h10, h11⟩ :=
    compare_eval source target 0 1 d hs ht hc
  have hs' : (saved e).stacks (original 1) = Encoding.encodeList id target :=
    (hframe 1).trans ht
  have ht' : (saved e).stacks (original 0) = Encoding.encodeList id source :=
    (hframe 0).trans hs
  obtain ⟨m, hm, f, hf, hclean', hbackward, hframe', h10', h11'⟩ :=
    compare_eval target source 1 0 (saved e) hs' ht' hclean
  have hremember : f.regs 11 = ExecCNF.subset source target := by
    simpa [saved, hforward] using h11'
  refine ⟨n + (1 + (m + 3)), ?_, combined f,
    Eval.seq he (Eval.seq (save_eval e) (Eval.seq hf (combine_eval f))), ?_, ?_, ?_, ?_⟩
  · have hle : n + (1 + (m + 3)) + 1 ≤
        compareBound source target + compareBound target source + 5 := by omega
    calc
      n + (1 + (m + 3)) + 1 ≤
          compareBound source target + compareBound target source + 5 := hle
      _ ≤ bound source target := by
        dsimp [bound, compareBound]
        ring_nf
        omega
  · exact hclean'
  · simp [hremember, hbackward, ExecCNF.equivalent]
  · simp [hremember, hbackward, ExecCNF.strictSubset]
  · intro i
    exact (hframe' i).trans (hframe i)

theorem program_runsIn (source target : List (List Bool)) (d : Data)
    (hs : d.stacks 8 = Encoding.encodeList id source)
    (ht : d.stacks 9 = Encoding.encodeList id target) (hc : clean d) :
    ∃ e : Data, RunsIn program (bound source target)
      (d.withPC (some program.entry)) (e.withPC none) ∧ clean e ∧
      e.regs 10 = ExecCNF.equivalent source target ∧
      e.regs 11 = ExecCNF.strictSubset source target ∧
      (∀ i : Fin 2, e.stacks (original i) = d.stacks (original i)) := by
  obtain ⟨n, hn, e, he, hclean, heq, hstrict, hframe⟩ := command_eval source target d hs ht hc
  exact ⟨e, ⟨n + 1, hn, compiled_halt_trace he 8 0⟩, hclean, heq, hstrict, hframe⟩

/-- The same execution also exposes the reverse-inclusion failure bit, used
to reject a proposed core that is not contained in a candidate clause. -/
theorem command_eval_all (source target : List (List Bool)) (d : Data)
    (hs : d.stacks 8 = Encoding.encodeList id source)
    (ht : d.stacks 9 = Encoding.encodeList id target) (hc : clean d) :
    ∃ n, n + 1 ≤ bound source target ∧ ∃ e : Data,
      Eval command n d e ∧ clean e ∧
      e.regs 10 = ExecCNF.equivalent source target ∧
      e.regs 11 = ExecCNF.strictSubset source target ∧
      (∀ i : Fin 2, e.stacks (original i) = d.stacks (original i)) ∧
      e.regs 9 = !(ExecCNF.subset target source) := by
  obtain ⟨n, hn, e, he, hclean, hforward, hframe, h10, h11⟩ :=
    compare_eval source target 0 1 d hs ht hc
  have hs' : (saved e).stacks (original 1) = Encoding.encodeList id target :=
    (hframe 1).trans ht
  have ht' : (saved e).stacks (original 0) = Encoding.encodeList id source :=
    (hframe 0).trans hs
  obtain ⟨m, hm, f, hf, hclean', hbackward, hframe', h10', h11'⟩ :=
    compare_eval target source 1 0 (saved e) hs' ht' hclean
  have hremember : f.regs 11 = ExecCNF.subset source target := by
    simpa [saved, hforward] using h11'
  refine ⟨n + (1 + (m + 3)), ?_, combined f,
    Eval.seq he (Eval.seq (save_eval e) (Eval.seq hf (combine_eval f))), ?_, ?_, ?_, ?_, ?_⟩
  · have hle : n + (1 + (m + 3)) + 1 ≤
        compareBound source target + compareBound target source + 5 := by omega
    calc
      n + (1 + (m + 3)) + 1 ≤
          compareBound source target + compareBound target source + 5 := hle
      _ ≤ bound source target := by
        dsimp [bound, compareBound]
        ring_nf
        omega
  · exact hclean'
  · simp [hremember, hbackward, ExecCNF.equivalent]
  · simp [hremember, hbackward, ExecCNF.strictSubset]
  · intro i
    exact (hframe' i).trans (hframe i)
  · simp [hbackward]

theorem program_runsIn_all (source target : List (List Bool)) (d : Data)
    (hs : d.stacks 8 = Encoding.encodeList id source)
    (ht : d.stacks 9 = Encoding.encodeList id target) (hc : clean d) :
    ∃ e : Data, RunsIn program (bound source target)
      (d.withPC (some program.entry)) (e.withPC none) ∧ clean e ∧
      e.regs 10 = ExecCNF.equivalent source target ∧
      e.regs 11 = ExecCNF.strictSubset source target ∧
      (∀ i : Fin 2, e.stacks (original i) = d.stacks (original i)) ∧
      e.regs 9 = !(ExecCNF.subset target source) := by
  obtain ⟨n, hn, e, he, hclean, heq, hstrict, hframe, hreverse⟩ :=
    command_eval_all source target d hs ht hc
  exact ⟨e, ⟨n + 1, hn, compiled_halt_trace he 8 0⟩, hclean, heq, hstrict, hframe, hreverse⟩

/-- Extensional clause semantics for the actual computed result flags. -/
theorem program_relations (source target : List (List Bool)) (d : Data)
    (hs : d.stacks 8 = Encoding.encodeList id source)
    (ht : d.stacks 9 = Encoding.encodeList id target) (hc : clean d) :
    ∃ e : Data, RunsIn program (bound source target)
      (d.withPC (some program.entry)) (e.withPC none) ∧ clean e ∧
      (e.regs 10 = true ↔ ExecCNF.clauseSet source = ExecCNF.clauseSet target) ∧
      (e.regs 11 = true ↔ ExecCNF.clauseSet source ⊂ ExecCNF.clauseSet target) ∧
      (∀ i : Fin 2, e.stacks (original i) = d.stacks (original i)) := by
  obtain ⟨e, he, hclean, heq, hstrict, hframe⟩ := program_runsIn source target d hs ht hc
  exact ⟨e, he, hclean, heq ▸ ExecCNF.equivalent_true source target,
    hstrict ▸ ExecCNF.strictSubset_true source target, hframe⟩

theorem primitive_execution (source target : List (List Bool)) (d : Data)
    (hs : d.stacks 8 = Encoding.encodeList id source)
    (ht : d.stacks 9 = Encoding.encodeList id target) (hc : clean d) :
    ∃ e : Data, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * bound source target)
      (primitiveCfg program (d.withPC (some program.entry)))
      (primitiveCfg program (e.withPC none)) ∧ clean e ∧
      e.regs 10 = ExecCNF.equivalent source target ∧
      e.regs 11 = ExecCNF.strictSubset source target ∧
      (∀ i : Fin 2, e.stacks (original i) = d.stacks (original i)) := by
  obtain ⟨e, he, hclean, heq, hstrict, hframe⟩ := program_runsIn source target d hs ht hc
  exact ⟨e, BitProgram.primitive_execution program he, hclean, heq, hstrict, hframe⟩

theorem encodeList_id_map {α : Type*} (enc : α → List Bool) (xs : List α) :
    Encoding.encodeList id (xs.map enc) = Encoding.encodeList enc xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Encoding.encodeList, ih]

theorem contains_map_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (x : α) (xs : List α) :
    ExecCNF.contains (f x) (xs.map f) = ExecCNF.contains x xs := by
  apply Bool.eq_iff_iff.mpr
  simp only [ExecCNF.contains_true, List.mem_map]
  constructor
  · rintro ⟨a, ha, heq⟩
    exact hf heq ▸ ha
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem subset_map_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (source target : List α) :
    ExecCNF.subset (source.map f) (target.map f) = ExecCNF.subset source target := by
  induction source with
  | nil => rfl
  | cons x xs ih => simp [ExecCNF.subset, contains_map_injective f hf, ih]

theorem equivalent_map_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (source target : List α) :
    ExecCNF.equivalent (source.map f) (target.map f) = ExecCNF.equivalent source target := by
  simp [ExecCNF.equivalent, subset_map_injective f hf]

theorem strictSubset_map_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (source target : List α) :
    ExecCNF.strictSubset (source.map f) (target.map f) = ExecCNF.strictSubset source target := by
  simp [ExecCNF.strictSubset, subset_map_injective f hf]

def natBound (source target : List ℕ) : ℕ :=
  160 * ((Encoding.encodeList Encoding.encodeNat source).length + 1) *
    ((Encoding.encodeList Encoding.encodeNat target).length + 1) + 5

/-- Direct interface for the canonical unary literal-list representation.
The program is unchanged; injectivity connects its bitwise tests to literals. -/
theorem nat_command_eval (source target : List ℕ) (d : Data)
    (hs : d.stacks 8 = Encoding.encodeList Encoding.encodeNat source)
    (ht : d.stacks 9 = Encoding.encodeList Encoding.encodeNat target) (hc : clean d) :
    ∃ n, n + 1 ≤ natBound source target ∧ ∃ e : Data,
      Eval command n d e ∧ clean e ∧
      e.regs 10 = ExecCNF.equivalent source target ∧
      e.regs 11 = ExecCNF.strictSubset source target ∧
      (∀ i : Fin 2, e.stacks (original i) = d.stacks (original i)) := by
  have hs' : d.stacks 8 = Encoding.encodeList id (source.map Encoding.encodeNat) := by
    simpa only [encodeList_id_map] using hs
  have ht' : d.stacks 9 = Encoding.encodeList id (target.map Encoding.encodeNat) := by
    simpa only [encodeList_id_map] using ht
  simpa only [bound, natBound, encodeList_id_map,
    equivalent_map_injective Encoding.encodeNat Encoding.encodeNat_injective,
    strictSubset_map_injective Encoding.encodeNat Encoding.encodeNat_injective] using
    command_eval (source.map Encoding.encodeNat) (target.map Encoding.encodeNat) d hs' ht' hc

theorem nat_program_runsIn (source target : List ℕ) (d : Data)
    (hs : d.stacks 8 = Encoding.encodeList Encoding.encodeNat source)
    (ht : d.stacks 9 = Encoding.encodeList Encoding.encodeNat target) (hc : clean d) :
    ∃ e : Data, RunsIn program (natBound source target)
      (d.withPC (some program.entry)) (e.withPC none) ∧ clean e ∧
      e.regs 10 = ExecCNF.equivalent source target ∧
      e.regs 11 = ExecCNF.strictSubset source target ∧
      (∀ i : Fin 2, e.stacks (original i) = d.stacks (original i)) := by
  obtain ⟨n, hn, e, he, hclean, heq, hstrict, hframe⟩ :=
    nat_command_eval source target d hs ht hc
  exact ⟨e, ⟨n + 1, hn, compiled_halt_trace he 8 0⟩, hclean, heq, hstrict, hframe⟩

end SubexponentialSAT.ExecClauseRelationsProgram

end OAI.Algorithms
