import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgramPairs
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentPairFrontend

namespace OAI.Algorithms

/-! Paid generation and installation of raw pairs from a linear plan stream. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram.Install
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

abbrev Data := State 16 48
def registers : Fin 10 → Fin 16 := Fin.castAdd 6
def ports : Fin 9 → Fin 48 := ![0,20,21,22,23,24,25,26,27]
def bank : List (Fin 48) := [20,21,22,23,24,25,26,27]

theorem registers_injective : Function.Injective registers := Fin.castAdd_injective 10 6
theorem ports_injective : Function.Injective ports := by decide

def Input (plans : List (List ℕ)) (d : Data) : Prop :=
  (∀ i, d.stacks (ports i) = (pairInput plans).stacks i) ∧
  d.stacks 7 = [] ∧ d.stacks 45 = []

abbrev generate : Cmd 16 48 :=
  .call (ProgramLinking.liftProgram TupleProgram.generateProgram registers ports)
abbrev command : Cmd 16 48 :=
  .seq generate (.seq AssignmentPairFrontend.move (SequentialProgram.clearList bank))
def program := compiled command 20 45
def budget (plans : List (List ℕ)) : ℕ :=
  100 * (TupleProgram.powerCost (planAlphabet plans) 2 [[]] + 9 +
    (ProgramEncoding.encodeRecords (planAlphabet plans)).length + 1)

theorem generate_eval (plans : List (List ℕ)) (d : Data) (hd : Input plans d) :
    ∃ t ≤ TupleProgram.powerCost (planAlphabet plans) 2 [[]] + 9,
      ∃ e : Data, Eval generate t d e ∧
      e.stacks 0 = PairScoreProgram.pairRecords (generatedRawPairs plans) ∧
      (∀ j, j ≠ 0 → j ∉ bank → e.stacks j = d.stacks j) := by
  let a : State 10 9 := ⟨d.regs ∘ registers, d.stacks ∘ ports⟩
  have ha : ∀ i, a.stacks i = (pairInput plans).stacks i := hd.1
  have hready : TupleProgram.outerInvariant (planAlphabet plans) [true,true]
      (a.regs 9) a := by
    simp only [TupleProgram.outerInvariant, ha]
    simp [pairInput]
  obtain ⟨b, hb, t, ht, htrace⟩ := TupleProgram.generateProgram_runsIn
    (planAlphabet plans) [true,true] (a.regs 9) a hready
    (by rw [ha]; simp [pairInput]) (by rw [ha]; simp [pairInput])
    (by rw [ha]; simp [pairInput])
  let e := embedState registers ports d b
  have hin : embedState registers ports d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ registers_injective ports_injective
    all_goals intros; rfl
  have he := eval_call_lifted TupleProgram.generateProgram registers ports d
    registers_injective ports_injective htrace
  rw [hin] at he
  refine ⟨t, ht, e, he, ?_, ?_⟩
  · exact (embedState_stack registers ports d b ports_injective 0).trans
      (hb.2.1.trans (generatedRawPairs_bytes plans))
  · intro j h0 hj
    apply embedState_stack_frame
    rintro ⟨i, hi⟩
    subst j
    fin_cases i <;> first | exact h0 rfl | exact hj (by decide)

/-- The input plan stream is consumed, output 45 holds its actual pair table,
and every stack outside the fixed work bank is preserved. -/
theorem command_eval (plans : List (List ℕ)) (d : Data) (hd : Input plans d) :
    ∃ t, t+1 ≤ budget plans ∧ ∃ e : Data,
      Eval command t d e ∧
      e.stacks 45 = PairScoreProgram.pairRecords (generatedRawPairs plans) ∧
      (∀ j, j = 0 ∨ j = 7 ∨ j ∈ bank → e.stacks j = []) ∧
      (∀ j, j ≠ 0 → j ≠ 7 → j ≠ 45 → j ∉ bank → e.stacks j = d.stacks j) := by
  obtain ⟨t, ht, b, hb, hout, hf⟩ := generate_eval plans d hd
  have h7 : b.stacks 7 = [] := (hf 7 (by decide) (by decide)).trans hd.2.1
  have h45 : b.stacks 45 = [] := (hf 45 (by decide) (by decide)).trans hd.2.2
  have hg (j : Fin 48) : (b.stacks j).length ≤ (d.stacks j).length + t + 1 := by
    have h := SequentialProgram.trace_stack_length_le (compiled_halt_trace hb 20 0) j
    simpa only [StructuredProgram.State.withPC, Nat.add_assoc] using h
  have h0 : d.stacks 0 = [] := by simpa [ports, pairInput] using hd.1 0
  have hlen : (b.stacks 0).length ≤ t+1 := by simpa [h0] using hg 0
  let L := (ProgramEncoding.encodeRecords (planAlphabet plans)).length
  have hstart (j : Fin 48) (hj : j ∈ bank) : (d.stacks j).length ≤ L+2 := by
    have h20 := hd.1 1
    have h21 := hd.1 2
    have h22 := hd.1 3
    have h23 := hd.1 4
    have h24 := hd.1 5
    have h25 := hd.1 6
    have h26 := hd.1 7
    have h27 := hd.1 8
    simp [ports, pairInput] at h20 h21 h22 h23 h24 h25 h26 h27
    simp only [bank, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [L]
  have hclean (j : Fin 48) (hj : j ∈ bank) :
      ((AssignmentPairFrontend.moved b).stacks j).length ≤ L+t+3 := by
    have hj0 : j ≠ 0 := by rintro rfl; exact (by decide : (0 : Fin 48) ∉ bank) hj
    have hj7 : j ≠ 7 := by rintro rfl; exact (by decide : (7 : Fin 48) ∉ bank) hj
    have hj45 : j ≠ 45 := by rintro rfl; exact (by decide : (45 : Fin 48) ∉ bank) hj
    simp only [AssignmentPairFrontend.moved, Function.update_of_ne hj45,
      Function.update_of_ne hj7, Function.update_of_ne hj0]
    have h := hg j
    have hi := hstart j hj
    omega
  obtain ⟨m, hm, e, he, hs⟩ := SequentialProgram.clearList_eval bank
    (AssignmentPairFrontend.moved b) (L+t+3) hclean
  have htrace := hb.seq ((AssignmentPairFrontend.move_eval b h7 h45).seq he)
  refine ⟨t+(6*(b.stacks 0).length+6+m), ?_, e, htrace, ?_, ?_, ?_⟩
  · change m ≤ 8*(2*(L+t+3)+3) at hm
    dsimp [budget, L] at *
    omega
  · rw [hs]
    simpa [bank, AssignmentPairFrontend.moved] using hout
  · intro j hj
    rw [hs]
    rcases hj with rfl | rfl | hj
    · simp [bank, AssignmentPairFrontend.moved]
    · simp [bank, AssignmentPairFrontend.moved]
    · simp [hj]
  · intro j h0j h7j h45j hj
    rw [hs]
    simp only [hj, ite_false, AssignmentPairFrontend.moved,
      Function.update_of_ne h45j, Function.update_of_ne h7j, Function.update_of_ne h0j]
    exact hf j h0j hj

theorem primitive_run (plans : List (List ℕ)) (d : Data) (hd : Input plans d) :
    ∃ e : Data, SubexponentialSAT.Computation.RunsIn (primitive program).step
      (primitiveOverhead program * budget plans)
      (primitiveCfg program (d.withPC (some program.entry)))
      (primitiveCfg program (e.withPC none)) ∧
      e.stacks 45 = PairScoreProgram.pairRecords (generatedRawPairs plans) ∧
      (∀ j, j = 0 ∨ j = 7 ∨ j ∈ bank → e.stacks j = []) ∧
      (∀ j, j ≠ 0 → j ≠ 7 → j ≠ 45 → j ∉ bank → e.stacks j = d.stacks j) := by
  obtain ⟨t, ht, e, he, hout, hz, hf⟩ := command_eval plans d hd
  have hr : RunsIn program (budget plans) (d.withPC (some program.entry))
      (e.withPC none) := ⟨t+1, ht, compiled_halt_trace he 20 45⟩
  exact ⟨e, primitive_execution program hr, hout, hz, hf⟩
end SubexponentialSAT.SqrtLog.PackingIncidenceProgram.Install

end OAI.Algorithms
