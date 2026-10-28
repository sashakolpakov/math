import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyBoundary
import OAI.Algorithms.SubexponentialSAT.ExecSparsifySearchWitness
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyChildSemantics
import OAI.Algorithms.SubexponentialSAT.ExecChildNormalizationInvariant
import OAI.Algorithms.SubexponentialSAT.SparsifyIntegrity

namespace OAI.Algorithms

/-!
# The branching observed in the concrete encoded search

The semantic branch function is extracted from a proved execution of the
fixed node-search program, on one canonical local input per formula.  The
actual machine still executes its own finite instruction table.  This
proof-only description lets the worklist tree retain the exact order chosen
by the index-and-mask search, without identifying it with an older selector.
-/

namespace SubexponentialSAT.ExecSparsifyObserved

open BitProgram StructuredCalls ExecCNF
open ExecSparsifyNode (Data)
open ExecSparsifyEncoding
open ExecSparsifySearchWitness (TypedOutcome TypedWitness program_typed natFormulaCode)
open ExecSparsifyCanonicalHead
open ExecCNFWidthLoad (low)

abbrev Formula (n : ℕ) := ExecCNF.Formula (SAT.Literal (Fin n))

def encode {n : ℕ} (F : Formula n) : List Bool :=
  CandidatePrepareProgram.formulaCode (words F)

@[simp] theorem encode_eq {n : ℕ} (F : Formula n) :
    encode F = natFormulaCode (codes F) := words_encoding F

/-- The inductive invariant concerns actual ordered lists. -/
def Ready (k : ℕ) {n : ℕ} (F : Formula n) : Prop :=
  (F.map clauseSet).Nodup ∧ (∀ C ∈ F, C.Nodup) ∧ ∀ C ∈ F, C.length ≤ k

noncomputable def localInput {n k : ℕ} (frame : Data k) (F : Formula n) :
    ExecCNFNodeSearch.Data k :=
  projectState id (ExecSparsifyProgram.searchPort k)
    (ExecSparsifyNode.headLoaded (encode F) (input encode frame F [] [] 0))

@[simp] theorem localInput_source {n k : ℕ} (frame : Data k) (F : Formula n) :
    (localInput frame F).stacks (low k 16) = encode F := by
  change (Function.update (input encode frame F [] [] 0).stacks
    (ExecSparsifyNode.port k 21) (encode F)) (ExecSparsifyNode.port k 21) = encode F
  exact Function.update_self _ _ _

/-- These are the actual persistent table words computed before traversal. -/
def BankValues {k : ℕ} (z : ℕ → ℕ) (frame : Data k) : Prop :=
  ∀ d : ExecCNFWidthDriver.Width k,
    BinaryArithmetic.toNat (frame.stacks (ExecSparsifyProgram.searchPort k
      (ExecCNFWidthLoad.bank k (ExecCNFWidthDriver.dimension d)
        (ExecCNFWidthDriver.dimension_le d)))) = z (ExecCNFWidthDriver.dimension d)

theorem localInput_fresh {n k : ℕ} (frame : Data k)
    (hf : ExecSparsifyBoundary.FrameReady frame) (F : Formula n) :
    ExecCNFNodeSearch.Fresh (words F) (localInput frame F) :=
  ExecSparsifyProgram.head_fresh (words F) (input encode frame F [] [] 0)
    (ExecSparsifyBoundary.input_clean encode frame hf F [] [] 0)

theorem localInput_bank {n k : ℕ} (frame : Data k) (z : ℕ → ℕ)
    (hb : BankValues z frame) (F : Formula n) :
    ExecCNFNodeSearchCorrectness.BankValues z (localInput frame F) := by
  intro d
  have hne : ExecSparsifyProgram.searchPort k
      (ExecCNFWidthLoad.bank k (ExecCNFWidthDriver.dimension d)
        (ExecCNFWidthDriver.dimension_le d)) ≠ ExecSparsifyNode.port k 21 := by
    intro h
    have hv := congrArg Fin.val h
    change 5 + (33 + ExecCNFWidthDriver.dimension d) = 21 at hv
    omega
  change BinaryArithmetic.toNat
    ((ExecSparsifyNode.headLoaded (encode F) (input encode frame F [] [] 0)).stacks
      (ExecSparsifyProgram.searchPort k (ExecCNFWidthLoad.bank k
        (ExecCNFWidthDriver.dimension d) (ExecCNFWidthDriver.dimension_le d)))) = _
  rw [ExecSparsifyNode.headLoaded_stack_frame _ _ _ hne,
    input_search_stack]
  exact hb d

/-- Every field describes one actual local run or its proved output. -/
structure Execution {n k : ℕ} (frame : Data k) (z : ℕ → ℕ) (F : Formula n) where
  steps : ℕ
  final : ExecCNFNodeSearch.Data k
  trace : Trace (ExecCNFNodeSearch.program k) steps
    ((localInput frame F).withPC (some (ExecCNFNodeSearch.program k).entry))
    (final.withPC none)
  source : final.stacks (low k 16) = natFormulaCode (codes F)
  frame_preserved : ExecCNFNodeSearch.Frame k (localInput frame F) final
  outcome : TypedOutcome F z final

theorem exists_execution {n k : ℕ} (frame : Data k) (z : ℕ → ℕ)
    (hf : ExecSparsifyBoundary.FrameReady frame) (hb : BankValues z frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j)
    (F : Formula n) (hF : Ready k F) : Nonempty (Execution frame z F) := by
  obtain ⟨t, b, ht, hs, hframe, ho⟩ := program_typed F z (localInput frame F)
    (localInput_fresh frame hf F) hF.1 hF.2.1 hF.2.2 hz (localInput_bank frame z hb F)
  exact ⟨⟨t, b, ht, hs, hframe, ho⟩⟩

noncomputable def observe {n k : ℕ} (frame : Data k) (z : ℕ → ℕ)
    (hf : ExecSparsifyBoundary.FrameReady frame) (hb : BankValues z frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j)
    (F : Formula n) (hF : Ready k F) : Execution frame z F :=
  Classical.choice (exists_execution frame z hf hb hz F hF)

noncomputable def witness {n k : ℕ} {frame : Data k} {z : ℕ → ℕ} {F : Formula n}
    (e : Execution frame z F) (hne : e.final.stacks (low k 21) ≠ []) :
    TypedWitness F z e.final :=
  Classical.choice ((e.outcome.resolve_left (fun h => hne h.1)).2)

def children {n k : ℕ} {z : ℕ → ℕ} {F : Formula n}
    {b : ExecCNFNodeSearch.Data k} (w : TypedWitness F z b) : Formula n × Formula n :=
  (ExecCoreChildProgram.result F w.selected w.core,
    ExecPetalChildProgram.result F w.selected w.core)

noncomputable def splitAt {n k : ℕ} {frame : Data k} {z : ℕ → ℕ} {F : Formula n}
    (e : Execution frame z F) : Option (Formula n × Formula n) :=
  if h : e.final.stacks (low k 21) = [] then none else some (children (witness e h))

theorem splitAt_decreases {n k : ℕ} {frame : Data k} {z : ℕ → ℕ} {F : Formula n}
    (e : Execution frame z F) (A B : Formula n) (h : splitAt e = some (A, B)) :
    SunflowerBranch.literalMass (formulaSet A) < SunflowerBranch.literalMass (formulaSet F) ∧
    SunflowerBranch.literalMass (formulaSet B) < SunflowerBranch.literalMass (formulaSet F) := by
  classical
  unfold splitAt at h
  split at h
  · contradiction
  · rename_i hn
    have he := Option.some.inj h
    cases he
    exact ExecSparsifyChildSemantics.children_mass_lt F (witness e hn).selected
      (witness e hn).core (witness e hn).choice (witness e hn).core_eq
      (witness e hn).selected_eq

theorem children_ready {n k : ℕ} {z : ℕ → ℕ} {F : Formula n}
    {b : ExecCNFNodeSearch.Data k} (hF : Ready k F) (w : TypedWitness F z b) :
    Ready k (children w).1 ∧ Ready k (children w).2 := by
  have ha := ExecChildNormalizationInvariant.core_normalized F w.selected w.core
    hF.2.1 w.core_sublist
  have hb := ExecChildNormalizationInvariant.petal_normalized F w.selected w.core
    hF.2.1 w.selected_subset
  have hwa := ExecChildNormalizationInvariant.core_width k F w.selected w.core
    hF.2.2 w.core_sublist
  have hwb := ExecChildNormalizationInvariant.petal_width k F w.selected w.core
    hF.2.2 w.selected_subset
  exact ⟨⟨ha.2, ha.1, hwa⟩, ⟨hb.2, hb.1, hwb⟩⟩

noncomputable def split {n k : ℕ} (frame : Data k) (z : ℕ → ℕ)
    (hf : ExecSparsifyBoundary.FrameReady frame) (hb : BankValues z frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j) (F : Formula n) :
    Option (Formula n × Formula n) := by
  classical
  exact if hF : Ready k F then splitAt (observe frame z hf hb hz F hF) else none

noncomputable def branching {n k : ℕ} (frame : Data k) (z : ℕ → ℕ)
    (hf : ExecSparsifyBoundary.FrameReady frame) (hb : BankValues z frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j) : ExecSparsifyWorklist.Branching (Formula n) where
  split := split frame z hf hb hz
  mass F := SunflowerBranch.literalMass (formulaSet F)
  decreases := by
    intro F A B h
    classical
    unfold split at h
    split at h
    · exact splitAt_decreases _ A B h
    · contradiction

theorem split_some_ready {n k : ℕ} (frame : Data k) (z : ℕ → ℕ)
    (hf : ExecSparsifyBoundary.FrameReady frame) (hb : BankValues z frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j)
    (F A B : Formula n) (h : split frame z hf hb hz F = some (A, B)) : Ready k F := by
  classical
  by_contra hn
  simp [split, hn] at h

theorem branching_closed {n k : ℕ} (frame : Data k) (z : ℕ → ℕ)
    (hf : ExecSparsifyBoundary.FrameReady frame) (hb : BankValues z frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j) :
    ExecSparsifyWorklist.SplitClosed (branching (n := n) frame z hf hb hz).split (Ready k) := by
  intro F A B hF hs
  classical
  change split frame z hf hb hz F = some (A, B) at hs
  simp only [split, dite_eq_left hF] at hs
  unfold splitAt at hs
  split at hs
  · contradiction
  · rename_i hn
    have he := Option.some.inj hs
    cases he
    exact children_ready hF _

theorem branching_choices {n k : ℕ} (frame : Data k) (z : ℕ → ℕ)
    (hf : ExecSparsifyBoundary.FrameReady frame) (hb : BankValues z frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j) :
    SparsifyIntegrity.RefinesChoicesOn (branching (n := n) frame z hf hb hz)
      formulaSet z k (Ready k) := by
  intro F hF A B hs
  classical
  change split frame z hf hb hz F = some (A, B) at hs
  simp only [split, dite_eq_left hF] at hs
  unfold splitAt at hs
  split at hs
  · contradiction
  · rename_i hn
    have he := Option.some.inj hs
    cases he
    let w := witness (observe frame z hf hb hz F hF) hn
    exact ⟨w.choice,
      ExecSparsifyChildSemantics.core_set F w.selected w.core w.choice w.core_eq w.selected_eq,
      ExecSparsifyChildSemantics.petal_set F w.selected w.core w.choice w.core_eq w.selected_eq⟩

theorem branching_terminal {n k : ℕ} (frame : Data k) (z : ℕ → ℕ)
    (hf : ExecSparsifyBoundary.FrameReady frame) (hb : BankValues z frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j) :
    SparsifyIntegrity.RefinesTerminalOn (branching (n := n) frame z hf hb hz)
      formulaSet z k (Ready k) := by
  intro F hF hs
  classical
  change split frame z hf hb hz F = none at hs
  simp only [split, dite_eq_left hF] at hs
  unfold splitAt at hs
  split at hs
  · rename_i he
    exact ((observe frame z hf hb hz F hF).outcome.resolve_right (fun h => h.1 he)).2
  · contradiction

end SubexponentialSAT.ExecSparsifyObserved

end OAI.Algorithms
