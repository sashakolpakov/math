import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNFWidthSearchSaved
import OAI.Algorithms.SubexponentialSAT.ExecCNFWidthInvariant
import OAI.Algorithms.SubexponentialSAT.ExecSunflowerCallbackBounds

namespace OAI.Algorithms

/-!
# Fixed-k minimum-width search control

The list of widths is compiled statically. Every width guard is before its
loader, so a successful search retains the matching width and threshold words
as well as its materialized core and family.
-/

namespace SubexponentialSAT.ExecCNFWidthDriver

open BitProgram StructuredCalls

abbrev Data := ExecCNFWidthLoad.Data
abbrev Code := ExecCNFWidthLoad.Code
abbrev low := ExecCNFWidthLoad.low
abbrev Width (k : ℕ) := Fin (k - 1)

def dimension {k : ℕ} (d : Width k) : ℕ := d.val + 2

theorem dimension_le {k : ℕ} (d : Width k) : dimension d ≤ k := by
  have := d.isLt
  unfold dimension
  omega

def searchCall (k : ℕ) : Code k :=
  liftCommand (ExecCNFWidthSearch.command k) 16 21 id (low k)

def stage (k : ℕ) (d : Width k) : Code k :=
  .seq (ExecCNFWidthLoad.command k (dimension d) (dimension_le d)) (searchCall k)

def peek (k : ℕ) : Code k := .base (.atom (.peek (low k 21) 0 1))

def peeked {k : ℕ} (a : Data k) : Data k :=
  (StructuredProgram.Atom.peek (low k 21) 0 1).eval a

@[simp] theorem peeked_stacks {k : ℕ} (a : Data k) : (peeked a).stacks = a.stacks := rfl

@[simp] theorem peeked_flag {k : ℕ} (a : Data k) :
    (peeked a).regs 1 = (a.stacks (low k 21)).head?.isSome := by
  exact readRegs_present a.regs 0 1 _

def scan (k : ℕ) : List (Width k) → Code k
  | [] => .base .skip
  | d :: ds => .seq (peek k) (.ite 1 (.base .skip) (.seq (stage k d) (scan k ds)))

def command (k : ℕ) : Code k := scan k (List.finRange (k - 1))

def program (k : ℕ) := compiled (command k) (low k 16) (low k 21)

/-- A saved witness stops before any later width or threshold is loaded. -/
theorem scan_stops {k : ℕ} (d : Width k) (ds : List (Width k)) (a : Data k)
    (h : a.stacks (low k 21) ≠ []) :
    Eval (scan k (d :: ds)) 2 a (peeked a) := by
  have hp : (peeked a).regs 1 = true := by
    rw [peeked_flag]
    cases he : a.stacks (low k 21) <;> simp_all
  exact Eval.seq (.base (.atom _ _)) (Eval.ite_true hp (.base (.skip _)))

/-- This log records only executions of the concrete stage command above.
The unprocessed suffix is retained when a witness stops the scan. -/
inductive Visits (k : ℕ) : List (Width k) → List (Width k) → ℕ → Data k → Data k → Prop
  | done (a : Data k) : Visits k [] [] 0 a a
  | stopped {d ds a} (h : a.stacks (low k 21) ≠ []) :
      Visits k (d :: ds) [] 2 a (peeked a)
  | step {d ds visited a b c ns nt}
      (h : a.stacks (low k 21) = [])
      (hs : Eval (stage k d) ns (peeked a) b)
      (ht : Visits k ds visited nt b c) :
      Visits k (d :: ds) (d :: visited) (ns + nt + 2) a c

theorem Visits.eval {k : ℕ} {ds visited : List (Width k)} {n : ℕ} {a b : Data k}
    (h : Visits k ds visited n a b) : Eval (scan k ds) n a b := by
  induction h with
  | done => exact .base (.skip _)
  | stopped h => exact scan_stops _ _ _ h
  | @step d ds visited a b c ns nt hz hs ht ih =>
    have hp : (peeked a).regs 1 = false := by simp [hz]
    have he := Eval.seq (show Eval (peek k) 1 a (peeked a) from .base (.atom _ _))
      (Eval.ite_false (yes := .base .skip) hp (Eval.seq hs ih))
    have hn : 1 + (ns + nt + 1) = ns + nt + 2 := by omega
    simpa only [scan, hn] using he

theorem Visits.visited_prefix {k : ℕ} {ds visited : List (Width k)} {n : ℕ} {a b : Data k}
    (h : Visits k ds visited n a b) : visited <+: ds := by
  induction h with
  | done => exact List.prefix_rfl
  | stopped => exact List.nil_prefix
  | step _ _ _ ih => exact List.cons_prefix_cons.mpr ⟨rfl, ih⟩

/-- If a witness was already present, the whole remaining scan preserves all
stacks, including the matched width, threshold, core, and selected family. -/
theorem Visits.stopped_stacks {k : ℕ} {ds visited : List (Width k)} {n : ℕ} {a b : Data k}
    (h : Visits k ds visited n a b) (hw : a.stacks (low k 21) ≠ []) :
    b.stacks = a.stacks := by
  cases h with
  | done => rfl
  | stopped => rfl
  | step hzero _ _ => exact False.elim (hw hzero)

theorem widths_range (k : ℕ) :
    (List.finRange (k - 1)).map dimension = List.range' 2 (k - 1) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [dimension, Nat.add_comm]

abbrev Formula := ExecSunflowerCallback.Formula
abbrev Ready {k : ℕ} (F : Formula) (limit : List Bool) (a : Data k) : Prop :=
  ExecCNFWidthInvariant.Ready F limit a
abbrev localState {k : ℕ} (a : Data k) : State 32 32 :=
  ExecCNFWidthInvariant.localState a

def callbackBudget (F : Formula) (limit width rows : List Bool) (k r w : ℕ) : ℕ :=
  3000000 * (ExecSunflowerCallbackBounds.aggregate F k r w limit width rows) ^ 8

theorem callbackBudget_spec (F : Formula) (limit width rows : List Bool) (k r w : ℕ) :
    ExecCNFWidthSearch.BodyBudget F limit width rows k r w
      (callbackBudget F limit width rows k r w) := by
  intro mask indices hm hi
  exact ExecSunflowerCallbackBounds.bound_le_aggregate F mask limit width rows indices k r w hm hi

def stageBound (k : ℕ) (d : Width k) (F : Formula) (limit : List Bool) (a : Data k) : ℕ :=
  let rows := a.stacks (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d))
  let width := a.stacks (low k 20)
  let r := CounterPrograms.value rows
  let w := CounterPrograms.value width
  ExecCNFWidthLoad.bound k (dimension d) (dimension_le d) a +
    ExecCNFWidthSearch.bound k r w (callbackBudget F limit (dimension d).bits rows k r w)
      (ExecCNFTupleInitialize.bound k rows width) + 1

def StageFrame (k : ℕ) (a b : Data k) : Prop :=
  ∀ i, i ≠ low k 8 → i ≠ low k 13 → i ≠ low k 14 →
    i ≠ low k 15 → i ≠ low k 17 → i ≠ low k 21 → b.stacks i = a.stacks i

/-- The complete stage invokes the real loader and real per-width search.
Its callback budget is the proved list-size polynomial, with no callback-cost
premise remaining. -/
theorem stage_eval (k : ℕ) (d : Width k) (F : Formula) (limit : List Bool)
    (a : Data k) (ha : Ready F limit a) :
    ∃ (n : ℕ) (e : Data k), Eval (stage k d) n a e ∧ n ≤ stageBound k d F limit a ∧
      e.stacks (low k 14) = (dimension d).bits ∧
      e.stacks (low k 15) = a.stacks (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d)) ∧
      e.stacks (low k 17) = [] ∧ e.stacks (low k 18) = [] ∧
      ExecSunflowerCallback.Saved F limit (dimension d).bits
        (a.stacks (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d))) (localState e) ∧
      StageFrame k a e ∧ (e.stacks (low k 21) = [] → Ready F limit e) ∧
      (e.stacks (low k 21) = [] → ∀ (mask : List Bool) (indices : List (List Bool)), mask.length = k →
        indices.map List.length = List.replicate
          (CounterPrograms.value (a.stacks (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d))))
          (CounterPrograms.value (a.stacks (low k 20))) →
        ExecSunflowerCallback.accepted F mask limit (dimension d).bits
          (a.stacks (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d))) indices = false) := by
  obtain ⟨b, hload, hb, hb14, hb15, hinit, hs, h21, hloadFrame⟩ :=
    ExecCNFWidthInvariant.load_ready k (dimension d) (dimension_le d) F limit a ha
  have hb20 : b.stacks (low k 20) = a.stacks (low k 20) :=
    hloadFrame (low k 20) ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
  let c := localState b
  let B := callbackBudget F limit (dimension d).bits (c.stacks 15) k
    (CounterPrograms.value (c.stacks 15)) (CounterPrograms.value (c.stacks 20))
  have hcI : ExecCNFWidthSearch.Invariant F limit (dimension d).bits (c.stacks 15) c := by
    have hh := ExecCNFWidthInvariant.callback_inputs F limit b hb
    have hh' := hh h21
    intro _
    rcases hh' with ⟨h16, h19, hwork, hspace, h14, h15⟩
    exact ⟨h16, h19, hwork, hspace, by simpa only [c, hb14] using h14, rfl⟩
  obtain ⟨n, f, hsearch, hn, hfI, hf17, hf18, hfSaved, hfFrame, hfAbsent⟩ :=
    ExecCNFWidthSearch.command_eval_saved F limit (dimension d).bits k B c hcI hinit hs h21
      (callbackBudget_spec F limit (dimension d).bits _ k _ _)
  let e := embedState id (low k) b f
  have hcall : Eval (searchCall k) (n + 1) b e :=
    eval_liftCommand_from_state (ExecCNFWidthSearch.command k) 16 21 id (low k) b
      Function.injective_id (ExecCNFWidthLoad.low_injective k) hsearch
  have hePort (i : Fin 32) : e.stacks (low k i) = f.stacks i :=
    embedState_stack id (low k) b f (ExecCNFWidthLoad.low_injective k) i
  have heLocal : localState e = f :=
    projectState_embed id (low k) b f Function.injective_id (ExecCNFWidthLoad.low_injective k)
  have heFrame := ExecCNFWidthInvariant.embed_search_frame b f hfFrame
  have hf14 : f.stacks 14 = (dimension d).bits :=
    (hfFrame 14 (by decide) (by decide) (by decide) (by decide)).trans hb14
  have hf15 : f.stacks 15 = a.stacks (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d)) :=
    (hfFrame 15 (by decide) (by decide) (by decide) (by decide)).trans hb15
  refine ⟨ExecCNFWidthLoad.bound k (dimension d) (dimension_le d) a + (n + 1), e,
    Eval.seq hload hcall, ?_, (hePort 14).trans hf14, (hePort 15).trans hf15,
    (hePort 17).trans hf17, (hePort 18).trans hf18, ?_, ?_, ?_, ?_⟩
  · dsimp [stageBound]
    have hnr : n ≤ ExecCNFWidthSearch.bound k
        (CounterPrograms.value (a.stacks (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d))))
        (CounterPrograms.value (a.stacks (low k 20)))
        (callbackBudget F limit (dimension d).bits
          (a.stacks (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d))) k
          (CounterPrograms.value (a.stacks (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d))))
          (CounterPrograms.value (a.stacks (low k 20))))
        (ExecCNFTupleInitialize.bound k
          (a.stacks (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d))) (a.stacks (low k 20))) := by
      simpa only [B, c, localState, ExecCNFWidthInvariant.localState, projectState,
        Function.comp_apply, hb15, hb20] using hn
    omega
  · rw [heLocal]
    simpa only [c, localState, ExecCNFWidthInvariant.localState, projectState,
      Function.comp_apply, hb15] using hfSaved
  · intro i hi8 hi13 hi14 hi15 hi17 hi21
    exact (heFrame i hi8 hi13 hi17 hi21).trans (hloadFrame i hi14 hi15)
  · intro he21
    have hf21 : f.stacks 21 = [] := (hePort 21).symm.trans he21
    have hclean := hfI hf21
    apply ExecCNFWidthInvariant.ready_after_unsuccessful_search F limit b e hb
      ((hePort 8).trans hclean.2.2.1.2.1)
      ((hePort 13).trans hclean.2.2.1.2.2.1)
      ((hePort 17).trans hf17) he21
    intro i hi8 hi13 hi17 hi21
    exact (hePort i).trans (hfFrame i hi8 hi13 hi17 hi21)
  · intro he21 mask indices hm hi
    have hf21 : f.stacks 21 = [] := (hePort 21).symm.trans he21
    have hres := hfAbsent hf21 mask indices hm (by
      simpa only [c, localState, ExecCNFWidthInvariant.localState, projectState,
        Function.comp_apply, hb15, hb20] using hi)
    simpa only [c, localState, ExecCNFWidthInvariant.localState, projectState,
      Function.comp_apply, hb15, hb20] using hres

/-- Every static width list has an actual finite execution. The only entry
condition is the concrete clean boundary when no witness has yet been saved. -/
theorem scan_exists (k : ℕ) (ds : List (Width k)) (F : Formula) (limit : List Bool)
    (a : Data k) (ha : a.stacks (low k 21) = [] → Ready F limit a) :
    ∃ (visited : List (Width k)) (n : ℕ) (b : Data k), Visits k ds visited n a b ∧
      (b.stacks (low k 21) = [] → Ready F limit b) ∧ StageFrame k a b := by
  induction ds generalizing a with
  | nil => exact ⟨[], 0, a, .done a, ha, fun _ _ _ _ _ _ _ => rfl⟩
  | cons d ds ih =>
    by_cases hw : a.stacks (low k 21) = []
    · have hpa : Ready F limit (peeked a) :=
        ExecCNFWidthInvariant.ready_of_stacks_eq F limit a (peeked a) (ha hw) rfl
      obtain ⟨ns, b, hstage, _, _, _, _, _, _, hframe, hb, _⟩ :=
        stage_eval k d F limit (peeked a) hpa
      obtain ⟨visited, nt, c, htail, hc, htailFrame⟩ := ih b hb
      refine ⟨d :: visited, ns + nt + 2, c, .step hw hstage htail, hc, ?_⟩
      intro i hi8 hi13 hi14 hi15 hi17 hi21
      exact (htailFrame i hi8 hi13 hi14 hi15 hi17 hi21).trans
        (hframe i hi8 hi13 hi14 hi15 hi17 hi21)
    · exact ⟨[], 2, peeked a, .stopped hw,
        fun h => False.elim (hw h), fun _ _ _ _ _ _ _ => rfl⟩

theorem program_runs (k : ℕ) (F : Formula) (limit : List Bool)
    (a : Data k) (ha : Ready F limit a) :
    ∃ (visited : List (Width k)) (n : ℕ) (b : Data k), Trace (program k) (n + 1)
      (a.withPC (some (program k).entry)) (b.withPC none) ∧
      Visits k (List.finRange (k - 1)) visited n a b ∧
      visited <+: List.finRange (k - 1) ∧
      (b.stacks (low k 21) = [] → Ready F limit b) ∧ StageFrame k a b := by
  obtain ⟨visited, n, b, hlog, hb, hf⟩ :=
    scan_exists k (List.finRange (k - 1)) F limit a (fun _ => ha)
  exact ⟨visited, n, b, compiled_halt_trace hlog.eval (low k 16) (low k 21),
    hlog, hlog.visited_prefix, hb, hf⟩

end SubexponentialSAT.ExecCNFWidthDriver

end OAI.Algorithms
