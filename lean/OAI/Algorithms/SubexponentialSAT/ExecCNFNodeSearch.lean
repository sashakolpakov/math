import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecNodeSizeProgram
import OAI.Algorithms.SubexponentialSAT.ExecCNFWidthDriver

namespace OAI.Algorithms

/-!
# Deriving node parameters before the concrete minimum-width search

This composition computes the clause count and index-word width from the
preserved current formula, then runs the actual fixed-k width driver. The
numeric words are outputs of a finite program, rather than entry assumptions.
All ports outside the search workspace and those two words are framed.
-/

namespace SubexponentialSAT.ExecCNFNodeSearch

open BitProgram StructuredCalls
open ExecCNFWidthLoad (low)

abbrev Formula := CandidatePrepareProgram.Formula
abbrev Data := ExecCNFWidthLoad.Data
abbrev Code := ExecCNFWidthLoad.Code
abbrev localState {k : ℕ} (a : Data k) : StructuredProgram.State 32 32 :=
  ExecCNFWidthInvariant.localState a

/-- A fresh node has an encoded source and empty working storage. No count,
index-width value, or register value is assumed. -/
structure Fresh {k : ℕ} (F : Formula) (a : Data k) : Prop where
  source : a.stacks (low k 16) = CandidatePrepareProgram.formulaCode F
  clean : ExecCNFWidthInvariant.Clean a
  count : a.stacks (low k 19) = []
  width : a.stacks (low k 20) = []

def setup (k : ℕ) : Code k :=
  liftCommand (.call ExecNodeSizeProgram.ambientProgram) 16 19 id (low k)

noncomputable def prepared {k : ℕ} (a : Data k) (count width : List Bool) : Data k :=
  embedState id (low k) a (ExecNodeSizeProgram.result (localState a) count width)

def setupBound (F : Formula) : ℕ :=
  128 * ((CandidatePrepareProgram.formulaCode F).length + 1) ^ 2 + 1

theorem prepared_stack {k : ℕ} (a : Data k) (count width : List Bool) (i : Fin 32) :
    (prepared a count width).stacks (low k i) =
      (ExecNodeSizeProgram.result (localState a) count width).stacks i :=
  embedState_stack id (low k) a _ (ExecCNFWidthLoad.low_injective k) i

theorem prepared_frame {k : ℕ} (a : Data k) (count width : List Bool)
    (i : Fin (k + 34)) (h19 : i ≠ low k 19) (h20 : i ≠ low k 20) :
    (prepared a count width).stacks i = a.stacks i := by
  classical
  by_cases hi : ∃ j, low k j = i
  · obtain ⟨j, rfl⟩ := hi
    have hj19 : j ≠ 19 := fun h => h19 (congrArg (low k) h)
    have hj20 : j ≠ 20 := fun h => h20 (congrArg (low k) h)
    rw [prepared_stack]
    simp [ExecNodeSizeProgram.result, hj19, hj20, localState,
      ExecCNFWidthInvariant.localState, projectState]
  · exact embedState_stack_frame id (low k) a _ i hi

theorem prepared_count {k : ℕ} (a : Data k) (count width : List Bool) :
    (prepared a count width).stacks (low k 19) = count := by
  rw [prepared_stack]
  simp [ExecNodeSizeProgram.result]

theorem prepared_width {k : ℕ} (a : Data k) (count width : List Bool) :
    (prepared a count width).stacks (low k 20) = width := by
  rw [prepared_stack]
  simp [ExecNodeSizeProgram.result]

theorem prepared_ready {k : ℕ} (F : Formula) (a : Data k)
    (ha : Fresh F a) (count width : List Bool) :
    ExecCNFWidthInvariant.Ready F count (prepared a count width) := by
  refine ⟨?_, prepared_count a count width, ?_⟩
  · exact (prepared_frame a count width (low k 16)
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))).trans ha.source
  · intro i hi
    have hi19 : i ≠ 19 := by
      intro h
      subst i
      exact (show ¬ ExecCNFWidthInvariant.Scratch (19 : Fin 32) by decide) hi
    have hi20 : i ≠ 20 := by
      intro h
      subst i
      exact (show ¬ ExecCNFWidthInvariant.Scratch (20 : Fin 32) by decide) hi
    exact (prepared_frame a count width (low k i)
      ((ExecCNFWidthLoad.low_injective k).ne hi19)
      ((ExecCNFWidthLoad.low_injective k).ne hi20)).trans (ha.clean i hi)

/-- The setup call computes both words and establishes the driver's concrete
clean entry boundary. Its cost includes the return from the lifted call. -/
theorem setup_eval (k : ℕ) (F : Formula) (a : Data k) (ha : Fresh F a) :
    ∃ count width, CounterPrograms.value count = F.length ∧
      CounterPrograms.value width = DyadicWidth.width F.length ∧
      count.length ≤ F.length ∧ width.length ≤ F.length + 1 ∧
      ∃ n ≤ setupBound F, Eval (setup k) n a (prepared a count width) ∧
        ExecCNFWidthInvariant.Ready F count (prepared a count width) := by
  obtain ⟨count, width, hc, hw, hcl, hwl, n, hn, he⟩ :=
    ExecNodeSizeProgram.setup_encoded_eval CandidatePrepareProgram.clauseCode F
      (localState a) ha.source ha.count ha.width
      (ha.clean 0 (by decide)) (ha.clean 1 (by decide)) (ha.clean 2 (by decide))
  refine ⟨count, width, hc, hw, hcl, hwl, n + 1, ?_, ?_,
    prepared_ready F a ha count width⟩
  · exact Nat.add_le_add_right hn 1
  · exact eval_liftCommand_from_state _ _ _ id (low k) a
      Function.injective_id (ExecCNFWidthLoad.low_injective k) he

def command (k : ℕ) : Code k :=
  .seq (setup k) (.call (ExecCNFWidthDriver.program k))

def program (k : ℕ) := compiled (command k) (low k 16) (low k 21)

/-- Frame for the entire setup-and-search composition. The count and width
ports are included because this program actually constructs those words. -/
def Frame (k : ℕ) (a b : Data k) : Prop :=
  ∀ i, i ≠ low k 8 → i ≠ low k 13 → i ≠ low k 14 →
    i ≠ low k 15 → i ≠ low k 17 → i ≠ low k 19 →
    i ≠ low k 20 → i ≠ low k 21 → b.stacks i = a.stacks i

/-- This is an actual execution of the concrete setup and width-driver code.
The visit log identifies the exact driver run and retains its finite stage
executions for the independent search-cost and minimum-width proofs. -/
theorem command_eval (k : ℕ) (F : Formula) (a : Data k) (ha : Fresh F a) :
    ∃ count width, CounterPrograms.value count = F.length ∧
      CounterPrograms.value width = DyadicWidth.width F.length ∧
      count.length ≤ F.length ∧ width.length ≤ F.length + 1 ∧
      ∃ (ns nt : ℕ) (visited : List (ExecCNFWidthDriver.Width k)) (b : Data k),
        ns ≤ setupBound F ∧ Eval (command k) (ns + nt + 1) a b ∧
        ExecCNFWidthDriver.Visits k (List.finRange (k - 1)) visited nt
          (prepared a count width) b ∧
        visited <+: List.finRange (k - 1) ∧
        (b.stacks (low k 21) = [] → ExecCNFWidthInvariant.Ready F count b) ∧
        b.stacks (low k 16) = CandidatePrepareProgram.formulaCode F ∧
        b.stacks (low k 19) = count ∧ b.stacks (low k 20) = width ∧ Frame k a b := by
  obtain ⟨count, width, hc, hw, hcl, hwl, ns, hns, hsetup, hready⟩ :=
    setup_eval k F a ha
  obtain ⟨visited, nt, b, htrace, hvisit, hprefix, hb, hf⟩ :=
    ExecCNFWidthDriver.program_runs k F count (prepared a count width) hready
  refine ⟨count, width, hc, hw, hcl, hwl, ns, nt, visited, b, hns, ?_,
    hvisit, hprefix, hb, ?_, ?_, ?_, ?_⟩
  · have he := hsetup.seq (Eval.call _ htrace)
    simpa only [command, Nat.add_assoc] using he
  · exact (hf (low k 16)
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))).trans hready.1
  · exact (hf (low k 19)
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))).trans
        (prepared_count a count width)
  · exact (hf (low k 20)
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))).trans
        (prepared_width a count width)
  · intro i hi8 hi13 hi14 hi15 hi17 hi19 hi20 hi21
    exact (hf i hi8 hi13 hi14 hi15 hi17 hi21).trans
      (prepared_frame a count width i hi19 hi20)

theorem program_runs (k : ℕ) (F : Formula) (a : Data k) (ha : Fresh F a) :
    ∃ count width, CounterPrograms.value count = F.length ∧
      CounterPrograms.value width = DyadicWidth.width F.length ∧
      count.length ≤ (CandidatePrepareProgram.formulaCode F).length ∧
      width.length ≤ (CandidatePrepareProgram.formulaCode F).length ∧
      ∃ (ns nt : ℕ) (visited : List (ExecCNFWidthDriver.Width k)) (b : Data k),
        ns ≤ setupBound F ∧ Trace (program k) (ns + nt + 2)
          (a.withPC (some (program k).entry)) (b.withPC none) ∧
        ExecCNFWidthDriver.Visits k (List.finRange (k - 1)) visited nt
          (prepared a count width) b ∧
        visited <+: List.finRange (k - 1) ∧
        (b.stacks (low k 21) = [] → ExecCNFWidthInvariant.Ready F count b) ∧
        b.stacks (low k 16) = CandidatePrepareProgram.formulaCode F ∧
        b.stacks (low k 19) = count ∧ b.stacks (low k 20) = width ∧ Frame k a b := by
  obtain ⟨count, width, hc, hw, hcl, hwl, ns, nt, visited, b,
    hns, he, hv, hp, hr, h16, h19, h20, hf⟩ := command_eval k F a ha
  have hlen := Encoding.length_encodeList_lower CandidatePrepareProgram.clauseCode F
  change F.length + 1 ≤ (CandidatePrepareProgram.formulaCode F).length at hlen
  refine ⟨count, width, hc, hw, by omega, hwl.trans hlen,
    ns, nt, visited, b, hns, ?_, hv, hp, hr, h16, h19, h20, hf⟩
  simpa only [program, Nat.add_assoc] using compiled_halt_trace he (low k 16) (low k 21)

end SubexponentialSAT.ExecCNFNodeSearch

end OAI.Algorithms
