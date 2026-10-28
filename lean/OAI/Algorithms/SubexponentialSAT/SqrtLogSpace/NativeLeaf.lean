import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramStorage
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSBoundarySpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CopySpace
import OAI.Algorithms.SubexponentialSAT.SubexpPrimeProgram

/-! Actual adapters for the streamed counting leaf. Both initial code rows
and newly generated rows use the canonical modulus word's exact width. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeaf

open BitProgram StructuredCalls
open SqrtLog.LeafOuterProgram

def canonicalRowWidth : Cmd 40 896 := .seq (route (780, 768)) (route (780, 783))

def canonicalRowState (a : Data) : Data := routed (780, 783) (routed (780, 768) a)

def canonicalRowSteps (a : Data) : ℕ :=
  2 * (a.stacks 768).length + 2 * (a.stacks 783).length +
    14 * (a.stacks 780).length + 16

theorem canonicalRowWidth_eval (a : Data) (hs : a.stacks 767 = []) :
    Eval canonicalRowWidth (canonicalRowSteps a) a (canonicalRowState a) := by
  have h1 := route_eval (780, 768) (by unfold routeValid; decide) a hs
  have h2 := route_eval (780, 783) (by unfold routeValid; decide) (routed (780, 768) a)
    (by simpa [routed] using hs)
  convert h1.seq h2 using 1
  · rfl
  · simp [canonicalRowSteps, routeCost, routed]
    omega
  · rfl

theorem canonicalRowState_modulus (a : Data) :
    (canonicalRowState a).stacks 768 = a.stacks 780 := by
  simp [canonicalRowState, routed]

theorem canonicalRowState_width (a : Data) :
    (canonicalRowState a).stacks 783 = a.stacks 780 := by
  simp [canonicalRowState, routed]

theorem canonicalRowState_frame (a : Data) (i : Fin 896) (h768 : i ≠ 768)
    (h783 : i ≠ 783) : (canonicalRowState a).stacks i = a.stacks i := by
  simp [canonicalRowState, routed, h768, h783]

theorem canonicalRowState_bound (a : Data) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((canonicalRowState a).stacks i).length ≤ B := by
  intro i
  by_cases h768 : i = 768
  · subst i; simpa [canonicalRowState_modulus] using ha 780
  by_cases h783 : i = 783
  · subst i; simpa [canonicalRowState_width] using ha 780
  rw [canonicalRowState_frame a i h768 h783]
  exact ha i

def canonicalRowProgram := compiled canonicalRowWidth 784 788

theorem canonicalRowWidth_trace_space (a : Data) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) (hs : a.stacks 767 = []) :
    Trace canonicalRowProgram (canonicalRowSteps a + 1)
      (a.withPC (some canonicalRowProgram.entry)) ((canonicalRowState a).withPC none) ∧
      canonicalRowSteps a + 1 ≤ 18 * B + 17 ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ canonicalRowSteps a + 1 →
        Trace canonicalRowProgram prefixSteps (a.withPC (some canonicalRowProgram.entry))
          intermediate → ∀ i, (intermediate.stacks i).length ≤ 914 * B + 17 := by
  have ht : canonicalRowSteps a + 1 ≤ 18 * B + 17 := by
    have h1 := ha 768
    have h2 := ha 783
    have h3 := ha 780
    dsimp [canonicalRowSteps]
    omega
  refine ⟨compiled_halt_trace (canonicalRowWidth_eval a hs) 784 788, ht, ?_⟩
  intro prefixSteps intermediate hp htrace i
  have hstart : dataBits (a.withPC (some canonicalRowProgram.entry)) ≤ 896 * B :=
    StreamResources.dataBits_le_mul _ ha
  have h := StructuredSpace.local_stack_bound canonicalRowProgram
    (steps := 18 * B + 17) hstart prefixSteps intermediate (hp.trans ht) htrace i
  omega

/-- Each concrete route clears its destination before copying, so its
temporary and destination fit the original source-word envelope. -/
theorem route_space (p : Route) (hp : routeValid p) {steps B : ℕ} {a b : Data}
    (he : Eval (route p) steps a b) (hs : a.stacks 767 = [])
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace (compiled (route p) 784 788) prefixSteps
        (a.withPC (some (compiled (route p) 784 788).entry)) c →
      ∀ i, (c.stacks i).length ≤ B := by
  obtain ⟨hsd, hst, hdt⟩ := hp
  cases he with
  | @seq _ _ n m _ middle _ first second =>
      have hclear := BankRoutines.clear_call_eval p.2 (0 : Fin 40) 1 a.regs a.stacks
      have hmiddle := SubexpPrimeProgram.eval_result_unique first hclear 784 788
      subst hmiddle
      have hfirst : ∀ prefixSteps c, prefixSteps ≤ n →
          Trace (compiled (.call (StackRoutines.clearProgram p.2 0 1)) 784 788) prefixSteps
            (a.withPC (some (compiled (.call (StackRoutines.clearProgram p.2 0 1)) 784 788).entry)) c →
          ∀ i, (c.stacks i).length ≤ B := by
        cases first with
        | call routine ht =>
            apply StructuredSpace.call_stack_bound (StackRoutines.clearProgram p.2 0 1)
              (compiled (.call (StackRoutines.clearProgram p.2 0 1)) 784 788)
              (siteAddress (.call (StackRoutines.clearProgram p.2 0 1)))
              (exitAddress (.call (StackRoutines.clearProgram p.2 0 1)))
              (compiled_site (.call (StackRoutines.clearProgram p.2 0 1)) 784 788) ht
            intro prefixSteps c _ hc i
            exact (DisjointReuse.SparseDFSBoundarySpace.clearProgram_stack_length_le
              p.2 0 1 hc i).trans (ha i)
      have hbound := hfirst _ _ le_rfl (compiled_trace first 784 788)
      have hsecond : ∀ prefixSteps c, prefixSteps ≤ m →
          Trace (compiled (.call (StackRoutines.copyProgram p.1 p.2 767 0 1)) 784 788) prefixSteps
            ((⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks p.2 a.stacks⟩ : Data).withPC
              (some (compiled (.call (StackRoutines.copyProgram p.1 p.2 767 0 1)) 784 788).entry)) c →
          ∀ i, (c.stacks i).length ≤ B := by
        cases second with
        | call routine ht =>
            apply StructuredSpace.call_stack_bound (StackRoutines.copyProgram p.1 p.2 767 0 1)
              (compiled (.call (StackRoutines.copyProgram p.1 p.2 767 0 1)) 784 788)
              (siteAddress (.call (StackRoutines.copyProgram p.1 p.2 767 0 1)))
              (exitAddress (.call (StackRoutines.copyProgram p.1 p.2 767 0 1)))
              (compiled_site (.call (StackRoutines.copyProgram p.1 p.2 767 0 1)) 784 788) ht
            intro prefixSteps c _ hc
            apply CopySpace.copyProgram_no_growth p.1 p.2 767 0 1 hsd hst hdt.symm rfl
              (by simp [StackRoutines.clearStacks])
              (by simpa [StructuredProgram.State.withPC, StackRoutines.clearStacks, hdt.symm] using hs) hbound hc
      exact StructuredSpace.sequence_stack_bound first second 784 788 hfirst hsecond
        (compiled (route p) 784 788) (siteAddress (route p)) (exitAddress (route p))
        (compiled_site (route p) 784 788)

def countHandoff : Cmd 40 896 := route (323, 788)

def countHandoffState (a : Data) : Data := routed (323, 788) a

theorem countHandoff_eval (a : Data) (hs : a.stacks 767 = []) :
    Eval countHandoff (2 * (a.stacks 788).length + 7 * (a.stacks 323).length + 8)
      a (countHandoffState a) :=
  route_eval (323, 788) (by unfold routeValid; decide) a hs

theorem countHandoff_count (a : Data) :
    (countHandoffState a).stacks 788 = a.stacks 323 := by
  simp [countHandoffState, routed]

theorem countHandoff_frame (a : Data) (i : Fin 896) (hi : i ≠ 788) :
    (countHandoffState a).stacks i = a.stacks i := by
  simp [countHandoffState, routed, hi]

theorem countHandoff_space (a : Data) (B : ℕ) (hs : a.stacks 767 = [])
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ prefixSteps c,
      prefixSteps ≤ 2 * (a.stacks 788).length + 7 * (a.stacks 323).length + 8 →
      Trace (compiled countHandoff 784 788) prefixSteps
        (a.withPC (some (compiled countHandoff 784 788).entry)) c →
      ∀ i, (c.stacks i).length ≤ B :=
  route_space (323, 788) (by unfold routeValid; decide) (countHandoff_eval a hs) hs ha

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeaf

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls

/-- Clearing a port never enlarges any retained word, including before return. -/
theorem clearOutput_space (port : Fin 1220) {steps bound : ℕ}
    {a b : State 80 1220} (he : Eval (clearOutput port) steps a b)
    (ha : ∀ i, (a.stacks i).length ≤ bound) :
    ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace (compiled (clearOutput port) 256 256) prefixSteps
        (a.withPC (some (compiled (clearOutput port) 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
  cases he with
  | call p ht =>
      apply StructuredSpace.call_stack_bound (StackRoutines.clearProgram port 72 73)
        (compiled (clearOutput port) 256 256) (siteAddress (clearOutput port))
        (exitAddress (clearOutput port)) (compiled_site (clearOutput port) 256 256) ht
      intro prefixSteps c _ hc i
      exact (DisjointReuse.SparseDFSBoundarySpace.clearProgram_stack_length_le
        port 72 73 hc i).trans (ha i)

/-- The fixed bank cleanup preserves the incoming per-stack bound. -/
theorem clearSequence_space (ports : List (Fin 1220)) {steps bound : ℕ}
    {a b : State 80 1220} (he : Eval (clearSequence ports) steps a b)
    (ha : ∀ i, (a.stacks i).length ≤ bound) :
    ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace (compiled (clearSequence ports) 256 256) prefixSteps
        (a.withPC (some (compiled (clearSequence ports) 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
  induction ports generalizing steps a b with
  | nil =>
      cases he with
      | base h =>
          cases h with
          | skip =>
              intro prefixSteps c hp hc
              have hz : prefixSteps = 0 := by omega
              subst prefixSteps
              cases hc
              exact ha
  | cons port rest ih =>
      cases he with
      | seq first second =>
          have hfirst := clearOutput_space port first ha
          have hmiddle := hfirst _ _ le_rfl (compiled_trace first 256 256)
          exact StructuredSpace.sequence_stack_bound first second 256 256 hfirst
            (ih second hmiddle) (compiled (clearSequence (port :: rest)) 256 256)
            (siteAddress (clearSequence (port :: rest)))
            (exitAddress (clearSequence (port :: rest)))
            (compiled_site (clearSequence (port :: rest)) 256 256)

theorem resetRegisters_space (ports : List (Fin 80)) {steps bound : ℕ}
    {a b : State 80 1220} (he : Eval (resetRegisters ports) steps a b)
    (ha : ∀ i, (a.stacks i).length ≤ bound) :
    ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace (compiled (resetRegisters ports) 256 256) prefixSteps
        (a.withPC (some (compiled (resetRegisters ports) 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
  induction ports generalizing steps a b with
  | nil =>
      cases he with
      | base h =>
          cases h with
          | skip =>
              intro prefixSteps c hp hc
              have hz : prefixSteps = 0 := by omega
              subst prefixSteps
              cases hc
              exact ha
  | cons port rest ih =>
      cases he with
      | seq first second =>
          have hfirst : ∀ prefixSteps c, prefixSteps ≤ 1 →
              Trace (compiled (.base (.atom (.set port false))) 256 256) prefixSteps
                (a.withPC (some (compiled (.base (.atom (.set port false))) 256 256).entry)) c →
              ∀ i, (c.stacks i).length ≤ bound := by
            intro prefixSteps c hp hc
            have hcases : prefixSteps = 0 ∨ prefixSteps = 1 := by omega
            rcases hcases with rfl | rfl
            · cases hc
              exact ha
            · rw [trace_same_length_unique hc
                (compiled_trace (Eval.base (.atom (.set port false) a)) 256 256)]
              exact ha
          cases first with
          | base h =>
              cases h with
              | atom =>
                  exact StructuredSpace.sequence_stack_bound
                    (Eval.base (.atom (.set port false) a)) second 256 256 hfirst
                    (ih second ha) (compiled (resetRegisters (port :: rest)) 256 256)
                    (siteAddress (resetRegisters (port :: rest)))
                    (exitAddress (resetRegisters (port :: rest)))
                    (compiled_site (resetRegisters (port :: rest)) 256 256)

/-- The copy table preserves its source and never needs a word longer than
that source when its destination and scratch are initially empty. -/
theorem copyWord_space (src dst scratch : Fin 1220) {steps bound : ℕ}
    {a b : State 80 1220} (he : Eval (copyWord src dst scratch) steps a b)
    (hsd : src ≠ dst) (hst : src ≠ scratch) (htd : scratch ≠ dst)
    (hdst : a.stacks dst = []) (htmp : a.stacks scratch = [])
    (ha : ∀ i, (a.stacks i).length ≤ bound) :
    ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace (compiled (copyWord src dst scratch) 256 256) prefixSteps
        (a.withPC (some (compiled (copyWord src dst scratch) 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
  cases he with
  | call p ht =>
      apply StructuredSpace.call_stack_bound (StackRoutines.copyProgram src dst scratch 72 73)
        (compiled (copyWord src dst scratch) 256 256) (siteAddress (copyWord src dst scratch))
        (exitAddress (copyWord src dst scratch))
        (compiled_site (copyWord src dst scratch) 256 256) ht
      intro prefixSteps c _ hc
      exact CopySpace.copyProgram_no_growth src dst scratch 72 73 hsd hst htd
        rfl hdst htmp ha hc

/-- Clearing, resetting and copying the three actual leaf inputs retain the
same per-stack envelope, even when the ambient numeric words are padded. -/
theorem loadLeaf_space {steps B : ℕ} {a b : State 80 1220}
    (heval : Eval loadLeaf steps a b) (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace (compiled loadLeaf 256 256) prefixSteps
        (a.withPC (some (compiled loadLeaf 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ B := by
  obtain ⟨t, e, _, he, hempty, _, hb⟩ := clearLeaf_eval a B ha
  let d0 := clearOutputState 1219 (resetLeafState e)
  let d1 := copiedWord 265 1104 d0
  let d2 := copiedWord 267 1105 d1
  have h1104 : e.stacks 1104 = [] := hempty 784
  have h1105 : e.stacks 1105 = [] := hempty 785
  have h1106 : e.stacks 1106 = [] := hempty 786
  have hclear : DisjointReuse.DFSVisit.BoundedEval clearLeaf t a e B :=
    ⟨he, clearSequence_space leafPorts he ha⟩
  have hreset : DisjointReuse.DFSVisit.BoundedEval resetLeafRegisters 40 e (resetLeafState e) B :=
    ⟨resetLeafRegisters_eval e,
      resetRegisters_space leafRegisterPorts (resetLeafRegisters_eval e) hb⟩
  have h0e := clearOutput_eval 1219 (resetLeafState e)
  have h0 : DisjointReuse.DFSVisit.BoundedEval (clearOutput 1219)
      (2 * ((resetLeafState e).stacks 1219).length + 3) (resetLeafState e) d0 B :=
    ⟨h0e, clearOutput_space 1219 h0e hb⟩
  have htmp0 : d0.stacks 1219 = [] := by simp [d0, clearOutputState]
  have hdst1 : d0.stacks 1104 = [] := by
    simp [d0, clearOutputState, resetLeafState, resetRegisterState, h1104]
  have h1e := copyWord_eval 265 1104 1219 d0 (by decide) (by decide) (by decide) htmp0
  have h1 : DisjointReuse.DFSVisit.BoundedEval (copyWord 265 1104 1219)
      (7 * (d0.stacks 265).length + 5) d0 d1 B :=
    ⟨h1e, copyWord_space 265 1104 1219 h1e (by decide) (by decide) (by decide)
      hdst1 htmp0 h0.final_bound⟩
  have htmp1 : d1.stacks 1219 = [] := by
    simp [d1, copiedWord, StackRoutines.copyStacks, htmp0]
  have hdst2 : d1.stacks 1105 = [] := by
    simp [d1, d0, copiedWord, clearOutputState, StackRoutines.copyStacks,
      resetLeafState, resetRegisterState, h1105]
  have h2e := copyWord_eval 267 1105 1219 d1 (by decide) (by decide) (by decide) htmp1
  have h2 : DisjointReuse.DFSVisit.BoundedEval (copyWord 267 1105 1219)
      (7 * (d1.stacks 267).length + 5) d1 d2 B :=
    ⟨h2e, copyWord_space 267 1105 1219 h2e (by decide) (by decide) (by decide)
      hdst2 htmp1 h1.final_bound⟩
  have htmp2 : d2.stacks 1219 = [] := by
    simp [d2, copiedWord, StackRoutines.copyStacks, htmp1]
  have hdst3 : d2.stacks 1106 = [] := by
    simp [d2, d1, d0, copiedWord, clearOutputState, StackRoutines.copyStacks,
      resetLeafState, resetRegisterState, h1106]
  have h3e := copyWord_eval 264 1106 1219 d2 (by decide) (by decide) (by decide) htmp2
  have h3 : DisjointReuse.DFSVisit.BoundedEval (copyWord 264 1106 1219)
      (7 * (d2.stacks 264).length + 5) d2 (copiedWord 264 1106 d2) B :=
    ⟨h3e, copyWord_space 264 1106 1219 h3e (by decide) (by decide) (by decide)
      hdst3 htmp2 h2.final_bound⟩
  have whole := hclear.seq (hreset.seq (h0.seq (h1.seq (h2.seq h3))))
  have ht := SubexpPrimeProgram.eval_steps_unique whole.eval heval 256 256
  simpa only [loadLeaf, ht] using whole.space

/-- Exporting the full count word and clearing the leaf bank also preserves
the incoming envelope at every prefix. -/
theorem exportLeaf_space {steps B : ℕ} {a b : State 80 1220}
    (heval : Eval exportLeaf steps a b) (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace (compiled exportLeaf 256 256) prefixSteps
        (a.withPC (some (compiled exportLeaf 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ B := by
  let d0 := clearOutputState 263 a
  let d1 := clearOutputState 1219 d0
  let d2 := copiedWord 1108 263 d1
  have h0e := clearOutput_eval 263 a
  have h0 : DisjointReuse.DFSVisit.BoundedEval (clearOutput 263)
      (2 * (a.stacks 263).length + 3) a d0 B :=
    ⟨h0e, clearOutput_space 263 h0e ha⟩
  have h1e := clearOutput_eval 1219 d0
  have h1 : DisjointReuse.DFSVisit.BoundedEval (clearOutput 1219)
      (2 * (d0.stacks 1219).length + 3) d0 d1 B :=
    ⟨h1e, clearOutput_space 1219 h1e h0.final_bound⟩
  have htmp : d1.stacks 1219 = [] := by simp [d1, clearOutputState]
  have hdst : d1.stacks 263 = [] := by simp [d1, d0, clearOutputState]
  have h2e := copyWord_eval 1108 263 1219 d1 (by decide) (by decide) (by decide) htmp
  have h2 : DisjointReuse.DFSVisit.BoundedEval (copyWord 1108 263 1219)
      (7 * (d1.stacks 1108).length + 5) d1 d2 B :=
    ⟨h2e, copyWord_space 1108 263 1219 h2e (by decide) (by decide) (by decide)
      hdst htmp h1.final_bound⟩
  obtain ⟨t, e, _, he, _, _, _⟩ := clearLeaf_eval d2 B h2.final_bound
  have h3 : DisjointReuse.DFSVisit.BoundedEval clearLeaf t d2 e B :=
    ⟨he, clearSequence_space leafPorts he h2.final_bound⟩
  have whole := h0.seq (h1.seq (h2.seq h3))
  have ht := SubexpPrimeProgram.eval_steps_unique whole.eval heval 256 256
  simpa only [exportLeaf, ht] using whole.space

/-- The loaded leaf is small independently of the suspended DFS envelope.
The two parameter word caps come from concrete pre-DFS production. -/
theorem loadLeaf_input_bound {n k parameterBound B : ℕ} (threshold : List Bool)
    (F : DisjointReuse.RawCNF n) (a : State 80 1220)
    (hv : DisjointReuse.SparseDFSRefinement.Valid k F)
    (hr : DisjointReuse.DFSVisit.LeafReady k threshold parameterBound F a)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∃ steps b, steps ≤ 1815 * B + 2746 ∧
      DisjointReuse.DFSVisit.BoundedEval loadLeaf steps a b B ∧
      b.stacks 1104 = DisjointReuse.SparseCountProgram.encodeBody F ∧
      BinaryArithmetic.toNat (b.stacks 1105) = n ∧
      BinaryArithmetic.toNat (b.stacks 1106) =
        4 * BinaryArithmetic.toNat threshold ^ (k - 1) ∧
      (∀ j : Fin 896, (b.stacks (ABI.leafStacks j)).length ≤
        DisjointReuse.SparseCountProgram.formulaBound n k + (n + 1) + parameterBound) ∧
      (∀ j : Fin 896, j ≠ 784 → j ≠ 785 → j ≠ 786 →
        b.stacks (ABI.leafStacks j) = []) ∧
      (∀ j, b.regs (ABI.leafRegisters j) = false) ∧
      (∀ i, (¬ ∃ j, ABI.leafStacks j = i) → i ≠ 1219 → b.stacks i = a.stacks i) := by
  obtain ⟨steps, b, ht, he, hformula, hn, hB, _, hempty, hframe, _, hregs⟩ :=
    loadLeaf_eval a B ha
  have hbody := DisjointReuse.SparseCountProgram.encodeBody_length_le F k hv.literal_nodup
    hv.clause_nodup (DisjointReuse.formulaSet_width_le F hv.width)
  have empty (j : Fin 896) (h4 : j ≠ 784) (h5 : j ≠ 785) (h6 : j ≠ 786) :
      b.stacks (ABI.leafStacks j) = [] := by
    apply hempty j
    · exact fun h => h4 (ABI.leafStacks.injective h)
    · exact fun h => h5 (ABI.leafStacks.injective h)
    · exact fun h => h6 (ABI.leafStacks.injective h)
  refine ⟨steps, b, ht, ⟨he, loadLeaf_space he ha⟩,
    hformula.trans hr.current, ?_, ?_, ?_, empty, hregs, hframe⟩
  · rw [hn]; exact hr.ambient
  · rw [hB]; exact hr.dimension
  · intro j
    by_cases h4 : j = 784
    · subst j
      change (b.stacks 1104).length ≤ _
      rw [hformula, hr.current]
      omega
    by_cases h5 : j = 785
    · subst j
      change (b.stacks 1105).length ≤ _
      rw [hn]
      have h := hr.dimension_length
      omega
    by_cases h6 : j = 786
    · subst j
      change (b.stacks 1106).length ≤ _
      rw [hB]
      have h := hr.occurrence_length
      omega
    rw [empty j h4 h5 h6]
    exact Nat.zero_le _

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
