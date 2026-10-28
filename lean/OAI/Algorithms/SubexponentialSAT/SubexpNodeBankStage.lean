import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeBasisStage
import OAI.Algorithms.SubexponentialSAT.SubexpNodeBankMap

namespace OAI.Algorithms

/-!
# Place the actual matrix-to-bank mapper in the node workspace

The basis producer leaves its matrix bundle on201. Four physical copies
install the scalar words from the protected static bank, the fixed mapper
enumerates every matrix, and cleanup removes those four copies. The result
on204 has the same outer-then-color order as the matrix bundle.
-/

namespace SubexponentialSAT.SubexpNodeBankStage

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpNodeBasisStage (Data Move copies copied copyCost clears cleared clearCost)

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

def ports (i : Fin 64) : Fin 288 :=
  if h : i.val < 32 then ⟨138 + i.val, by omega⟩
  else ⟨169 + i.val, by omega⟩

theorem ports_injective : Function.Injective ports := by
  intro i j he
  apply Fin.ext
  have hv := congrArg Fin.val he
  by_cases hi : i.val < 32 <;> by_cases hj : j.val < 32
  all_goals simp [ports, hi, hj] at hv ; omega

@[simp] theorem ports_input : ports 32 = 201 := by decide
@[simp] theorem ports_output : ports 35 = 204 := by decide

theorem ports_range (i : Fin 64) : 138 ≤ (ports i).val ∧ (ports i).val < 233 := by
  unfold ports
  split_ifs <;> dsimp <;> omega

def moves : List Move := [(279,209), (277,210), (280,211), (264,212)]
def workspace : List (Fin 288) := [209,210,211,212]
abbrev prepare : Cmd 16 288 := copies moves
abbrev call : Cmd 16 288 :=
  .call (ProgramLinking.liftProgram SubexpNodeBankMap.program id ports)
abbrev command : Cmd 16 288 := .seq prepare (.seq call (clears workspace))
abbrev program : Program 16 288 (size command + 1) := compiled command 201 204

theorem prepare_eval (d : Data) (h0 : d.stacks 0 = []) :
    Eval prepare (copyCost moves d) d (copied moves d) := by
  apply SubexpNodeBasisStage.copies_eval moves d h0
  intro m hm
  simp only [moves, List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> decide

theorem cleared_frame (xs : List (Fin 288)) (d : Data) (i : Fin 288)
    (hi : i ∉ xs) : (cleared xs d).stacks i = d.stacks i := by
  induction xs generalizing d with
  | nil => rfl
  | cons x xs ih =>
      have hx : i ≠ x := List.ne_of_not_mem_cons hi
      rw [cleared, ih _ (List.not_mem_of_not_mem_cons hi)]
      simp [SubexpNodeBasisStage.clearOut, hx]

def frame (d : Data) : Fin 20 → List Bool :=
  fun i => d.stacks (ports (Fin.natAdd 44 i))

/-- This is the concrete parser input layout, not an execution assumption.
The matrix records are supplied by the preceding basis producer. -/
def Input {p rows : ℕ} [Fact p.Prime]
    (d : Data) (matrices : List (SubexpNodeBankMap.Matrix p rows)) : Prop :=
  projectState id ports (copied moves d) =
    SubexpNodeBankMap.input matrices (copied moves d).regs (frame d)

noncomputable def mapped {p rows : ℕ} [Fact p.Prime] (d : Data)
    (matrices : List (SubexpNodeBankMap.Matrix p rows)) (rf : Fin 16 → Bool) : Data :=
  embedState id ports (copied moves d) (SubexpNodeBankMap.result matrices rf (frame d))

noncomputable def finished {p rows : ℕ} [Fact p.Prime] (d : Data)
    (matrices : List (SubexpNodeBankMap.Matrix p rows)) (rf : Fin 16 → Bool) : Data :=
  cleared workspace (mapped d matrices rf)

theorem mapped_common {p rows : ℕ} [Fact p.Prime] (d : Data)
    (matrices : List (SubexpNodeBankMap.Matrix p rows)) (rf : Fin 16 → Bool) :
    (mapped d matrices rf).stacks 209 = Subexp.MatrixWordEncoding.modulus p ∧
    (mapped d matrices rf).stacks 210 = Subexp.MatrixWordEncoding.zero p ∧
    (mapped d matrices rf).stacks 211 =
      ProgramEncoding.encodeRecords (Subexp.MatrixImageEnumeration.tokens p) ∧
    (mapped d matrices rf).stacks 212 = List.replicate rows true := by
  have h (i : Fin 24) :=
    (embedState_stack id ports (copied moves d)
      (SubexpNodeBankMap.result matrices rf (frame d)) ports_injective
      (Fin.natAdd 40 i)).trans (SubexpNodeBankMap.result_common matrices rf (frame d) i)
  exact ⟨by simpa [mapped, ports, SubexpNodeBankMap.common] using h 0,
    by simpa [mapped, ports, SubexpNodeBankMap.common] using h 1,
    by simpa [mapped, ports, SubexpNodeBankMap.common] using h 2,
    by simpa [mapped, ports, SubexpNodeBankMap.common] using h 3⟩

def cleanupBound (p rows : ℕ) [Fact p.Prime] : ℕ :=
  2 * SubexpNodeBankMap.commonSize p rows + 12

theorem cleanup_cost {p rows : ℕ} [Fact p.Prime] (d : Data)
    (matrices : List (SubexpNodeBankMap.Matrix p rows)) (rf : Fin 16 → Bool) :
    clearCost workspace (mapped d matrices rf) = cleanupBound p rows := by
  obtain ⟨h0,h1,h2,h3⟩ := mapped_common d matrices rf
  simp [workspace, clearCost, SubexpNodeBasisStage.clearOut, h0, h1, h2, h3,
    cleanupBound, SubexpNodeBankMap.commonSize]
  omega

theorem finished_output {p rows : ℕ} [Fact p.Prime] (d : Data)
    (matrices : List (SubexpNodeBankMap.Matrix p rows)) (rf : Fin 16 → Bool) :
    (finished d matrices rf).stacks 204 =
      ProgramEncoding.encodeRecords (matrices.map SubexpNodeBankMap.bankList) := by
  rw [finished, cleared_frame workspace _ 204 (by decide)]
  simpa only [mapped, ports_output] using
    (embedState_stack id ports (copied moves d)
      (SubexpNodeBankMap.result matrices rf (frame d)) ports_injective 35).trans
      (SubexpNodeBankMap.result_output matrices rf (frame d))

theorem finished_source_empty {p rows : ℕ} [Fact p.Prime] (d : Data)
    (matrices : List (SubexpNodeBankMap.Matrix p rows)) (rf : Fin 16 → Bool) :
    (finished d matrices rf).stacks 201 = [] := by
  rw [finished, cleared_frame workspace _ 201 (by decide)]
  simpa [mapped, SubexpNodeBankMap.result, SubexpNodeBankMap.store] using
    embedState_stack id ports (copied moves d)
      (SubexpNodeBankMap.result matrices rf (frame d)) ports_injective 32

theorem finished_workspace_empty {p rows : ℕ} [Fact p.Prime] (d : Data)
    (matrices : List (SubexpNodeBankMap.Matrix p rows)) (rf : Fin 16 → Bool)
    (i : Fin 288) (hi : i ∈ workspace) :
    (finished d matrices rf).stacks i = [] := by
  simp only [workspace, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp [finished, workspace, cleared, SubexpNodeBasisStage.clearOut]

theorem finished_frame {p rows : ℕ} [Fact p.Prime] (d : Data)
    (matrices : List (SubexpNodeBankMap.Matrix p rows)) (rf : Fin 16 → Bool)
    (i : Fin 288) (hi : i.val < 138 ∨ 233 ≤ i.val) :
    (finished d matrices rf).stacks i = d.stacks i := by
  have hn (j : Fin 288) (hj : 138 ≤ j.val ∧ j.val < 233) : i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have hw : i ∉ workspace := by
    simp only [workspace, List.mem_cons, List.mem_nil_iff, or_false]
    exact fun h => by
      rcases h with h | h | h | h
      all_goals exact hn _ (by decide) h
  rw [finished, cleared_frame workspace _ i hw]
  unfold mapped
  rw [embedState_stack_frame id ports (copied moves d) _ i (by
    rintro ⟨j,hj⟩
    exact hn _ (ports_range j) hj.symm)]
  apply SubexpNodeBasisStage.copied_frame
  intro m hm
  simp only [moves, List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> exact hn _ (by decide)

def budget {p rows : ℕ} [Fact p.Prime] (d : Data)
    (matrices : List (SubexpNodeBankMap.Matrix p rows)) : ℕ :=
  copyCost moves d + (SubexpNodeBankMap.runtimeBound matrices + cleanupBound p rows)

/-- No arithmetic or enumeration callback is assumed: this invokes the
proved finite matrix-image mapper on the concrete prepared input layout. -/
theorem command_eval {p rows : ℕ} [Fact p.Prime] (d : Data)
    (matrices : List (SubexpNodeBankMap.Matrix p rows)) (h0 : d.stacks 0 = [])
    (hi : Input d matrices) :
    ∃ n ≤ budget d matrices, ∃ rf : Fin 16 → Bool,
      Eval command n d (finished d matrices rf) := by
  obtain ⟨rf,n,hn,ht⟩ := SubexpNodeBankMap.program_run matrices (copied moves d).regs (frame d)
  change projectState id ports (copied moves d) = _ at hi
  rw [← hi] at ht
  have he := eval_call_from_state SubexpNodeBankMap.program id ports (copied moves d)
    Function.injective_id ports_injective ht
  have hc := SubexpNodeBasisStage.clears_eval workspace (mapped d matrices rf)
  rw [cleanup_cost] at hc
  refine ⟨copyCost moves d + (n + cleanupBound p rows), ?_, rf,
    (prepare_eval d h0).seq (he.seq hc)⟩
  unfold budget
  omega

theorem program_runs {p rows : ℕ} [Fact p.Prime] (d : Data)
    (matrices : List (SubexpNodeBankMap.Matrix p rows)) (h0 : d.stacks 0 = [])
    (hi : Input d matrices) :
    ∃ rf : Fin 16 → Bool, RunsIn program (budget d matrices + 1)
      (d.withPC (some program.entry)) ((finished d matrices rf).withPC none) := by
  obtain ⟨n,hn,rf,he⟩ := command_eval d matrices h0 hi
  exact ⟨rf,n + 1,by omega,compiled_halt_trace he 201 204⟩

end SubexponentialSAT.SubexpNodeBankStage

end OAI.Algorithms
