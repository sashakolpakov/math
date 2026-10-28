import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLeafSemantics

namespace OAI.Algorithms

/-!
# Conditional assembly of the actual sparse-leaf callback

`ReconstructionStages` records actual executions and the denotation of the
single quartet returned by reconstruction at zero. This file does not produce
those stages. In particular, their layout/source provenance and true-moment
identities remain obligations of the concrete producers. Given that boundary,
the real finalizer supplies the SAT answer and restores its work storage.
-/

namespace SubexponentialSAT.SubexpLeafContract

open StructuredCalls SubexpMainProgram SubexpLayoutSpec SubexpLeafSemantics

abbrev dimension (n ell : ℕ) := Fintype.card (Fin (ChunkPartition.count n ell))
abbrev wordWidth (n ell p : ℕ) := SubexpLiftRing.baseWidth p (dimension n ell + 1)

variable {er es n ell p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]

theorem packed_bounded_of_sparse {occ : ℕ} (G : Leaf n)
    (sparse : Sparse k occ G) (hell : 0 < ell) (hcap : 2 ^ ell ≤ p)
    (hk : 1 ≤ k)
    (hne : ¬ SubexpEmptyClauseGuard.HasEmpty (ExecQuantitativeSparsify.encodeRawFormula G)) :
    (SubexpLEFactorSystem.packed hell hcap (ExecCNF.formulaSet G)).toPattern.Bounded
      k (1 + ell * occ) :=
  SubexpLEFactorSystem.packed_bounded hell hcap (ExecCNF.formulaSet G)
    hk sparse.width sparse.occurrences (nonempty_clauses G hne)

/-- The finite semantic enumeration has exactly the physical unary-first
and observed-clause order. No finite-set sorting is substituted here. -/
theorem sparse_scope_stream {occ : ℕ} (G : Leaf n) (sparse : Sparse k occ G)
    (hell : 0 < ell) :
    (SubexpLeafData.factors (D := ChunkPartition.count n ell) G sparse.clause_sets_nodup).values.map
        (SubexpLeafData.scopes G sparse.clause_sets_nodup (ChunkPartition.indexEquiv n ell hell)) =
      (List.finRange (ChunkPartition.count n ell)).map (fun j => [j]) ++
        G.map (SubexpLeafData.clauseScope (ChunkPartition.indexEquiv n ell hell)) :=
  SubexpLeafData.scope_stream G sparse.clause_sets_nodup (ChunkPartition.indexEquiv n ell hell)

/-- The denotation field concerns exactly the physically returned singleton
H(0) quartet. It must be proved from the real source/moment/CRT chain; it is
not a premise asserting that an arbitrary natural count is correct. -/
structure ReconstructionStages (phases : Phases er es) (G : Leaf n)
    (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) {c : Parameters p k Δ r tau}
    (layout : Layout (E := SubexpActualRing.E p)
      (SubexpLEFactorSystem.packed hell hcap (ExecCNF.formulaSet G)).toPattern c)
    (start : MainState er es) where
  afterLayout : MainState er es
  afterMoments : MainState er es
  afterCRT : MainState er es
  layoutSteps : ℕ
  momentSteps : ℕ
  crtSteps : ℕ
  layoutTrace : Eval phases.layout.invoke layoutSteps (transferredData start) afterLayout
  momentTrace : Eval phases.moments.invoke momentSteps afterLayout afterMoments
  crtTrace : Eval phases.crt.invoke crtSteps afterMoments afterCRT
  modulus : SubexpPreparedQuartic.Modulus p (dimension n ell + 1)
  output : SubexpFlatCount.Code (wordWidth n ell p)
  decodeRegs : Fin 8 → Bool
  width : List Bool
  width_length : width.length = wordWidth n ell p
  decodeReady : (SubexpMainDecode.procedure er es).project afterCRT =
    SubexpFlatCount.start decodeRegs modulus.bits width (SubexpFlatCount.flatPolynomial [output])
  reconstructed : SubexpHornerMachine.decode p (dimension n ell + 1)
    (QuarticSearch.liftedCoefficients p (dimension n ell + 1)) output =
      SubexpCRTAtZero.selectedValue
        (SubexpLEFactorSystem.packed hell hcap (ExecCNF.formulaSet G)) layout
  source_frame : afterCRT.stacks (persistent es 7) =
    (transferredData start).stacks (persistent es 7)
  payload_frame : afterCRT.stacks (persistent es 8) =
    (transferredData start).stacks (persistent es 8)
  leaf_frame : afterCRT.stacks (persistent es 9) =
    (transferredData start).stacks (persistent es 9)

namespace ReconstructionStages

variable {phases : Phases er es} {G : Leaf n} {hell : 0 < ell} {hcap : 2 ^ ell ≤ p}
  {c : Parameters p k Δ r tau}
  {layout : Layout (E := SubexpActualRing.E p)
    (SubexpLEFactorSystem.packed hell hcap (ExecCNF.formulaSet G)).toPattern c}
  {start : MainState er es}

def prefixSteps (stages : ReconstructionStages phases G hell hcap layout start) : ℕ :=
  stages.layoutSteps + (stages.momentSteps + stages.crtSteps)

theorem prefixTrace (stages : ReconstructionStages phases G hell hcap layout start) :
    Eval (.seq phases.layout.invoke (.seq phases.moments.invoke phases.crt.invoke))
      stages.prefixSteps (transferredData start) stages.afterCRT :=
  stages.layoutTrace.seq (stages.momentTrace.seq stages.crtTrace)

noncomputable def finalState
    (stages : ReconstructionStages phases G hell hcap layout start)
    (count : ℕ) (hcount : count ≤ workStacks es) (rf : Fin 8 → Bool) : MainState er es :=
  SubexpMainReady.result count hcount stages.afterCRT rf stages.modulus.bits
    stages.width stages.output.c0.val

end ReconstructionStages

/-- Includes transfer, actual prefix, selected-workspace cleanup, final
register reset, and the physical leaf/answer epilogue. -/
def leafBound (er count width prefixLimit : ℕ) (bits : List Bool) : ℕ :=
  3 * (prefixLimit + SubexpH0CountDecision.budget width) +
    5 * bits.length + 4 * width + 3 * count + workRegs er + 18

theorem finish_run (phases : Phases er es) (count : ℕ) (hcount : count ≤ workStacks es)
    (hdecode : phases.decode = SubexpMainReady.procedure er es count hcount)
    (G : Leaf n) (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (hn : 0 < n)
    {c : Parameters p k Δ r tau}
    (layout : Layout (E := SubexpActualRing.E p)
      (SubexpLEFactorSystem.packed hell hcap (ExecCNF.formulaSet G)).toPattern c)
    (base : MainState er es) (tail : List Bool)
    (stages : ReconstructionStages phases G hell hcap layout
      (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G)))
    (storage : SubexpMainReady.StorageReady count base)
    (emptyLeaf : base.stacks (persistent es 9) = []) :
    ∃ (rf : Fin 8 → Bool)
      (run : LeafRun phases (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))),
      run.afterDecode = stages.finalState count hcount rf ∧
      run.steps ≤ leafBound er count (wordWidth n ell p) stages.prefixSteps
        (ExecQuantitativeSparsify.encodeRawFormula G) ∧
      SubexpMainReady.StorageReady count (finishedData run.afterDecode) ∧
      run.afterDecode.stacks (persistent es 7) = tail ∧
      run.afterDecode.stacks (persistent es 8) = [] ∧
      (run.afterDecode.stacks (persistent es 10)).head? =
        some (test n (ExecQuantitativeSparsify.encodeRawFormula G)) := by
  obtain ⟨steps, rf, hb, he, _, _, hframe⟩ := SubexpLeafSemantics.finalize_execution
    G hell hcap layout count hcount stages.modulus stages.output hn stages.reconstructed
    stages.afterCRT stages.decodeRegs stages.width stages.width_length stages.decodeReady
  change steps ≤ 3 * SubexpH0CountDecision.budget (wordWidth n ell p) +
    2 * WorkspaceCleanupProgram.Main.selectedBits count hcount stages.afterCRT +
    3 * count + workRegs er + 4 at hb
  let run : LeafRun phases (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G)) := {
    afterLayout := stages.afterLayout
    afterMoments := stages.afterMoments
    afterCRT := stages.afterCRT
    afterDecode := stages.finalState count hcount rf
    layoutSteps := stages.layoutSteps
    momentSteps := stages.momentSteps
    crtSteps := stages.crtSteps
    decodeSteps := steps
    layoutTrace := stages.layoutTrace
    momentTrace := stages.momentTrace
    crtTrace := stages.crtTrace
    decodeTrace := by
      simpa only [hdecode, ReconstructionStages.finalState] using he }
  have hin := transfer_leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G) emptyLeaf
  have hsource : stages.afterCRT.stacks (persistent es 7) = tail :=
    stages.source_frame.trans hin.2.2
  have hpayload : stages.afterCRT.stacks (persistent es 8) = [] :=
    stages.payload_frame.trans hin.2.1
  have hleaf : stages.afterCRT.stacks (persistent es 9) =
      ExecQuantitativeSparsify.encodeRawFormula G := stages.leaf_frame.trans hin.1
  have hready := SubexpMainReady.transferred_ready count hcount
    (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))
    (SubexpMainReady.leafInput_ready count hcount base tail
      (ExecQuantitativeSparsify.encodeRawFormula G) storage)
  have hbits := SubexpMainReady.selectedBits_after_eval count hcount stages.prefixTrace
  rw [SubexpMainReady.selectedBits_eq_zero count hcount _ hready, zero_add] at hbits
  have hfinish := SubexpMainReady.finishCost_result_le count hcount [stages.output]
    stages.afterCRT rf stages.modulus.bits stages.width
  change finishCost (stages.finalState count hcount rf) ≤
    2 * (stages.afterCRT.stacks (persistent es 9)).length +
      2 * (stages.modulus.bits.length + wordWidth n ell p) + 9 at hfinish
  rw [hleaf] at hfinish
  have hmodulus : stages.modulus.bits.length ≤ wordWidth n ell p + 1 :=
    stages.modulus.length_le
  have htransfer : transferCost (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G)) =
      3 * (ExecQuantitativeSparsify.encodeRawFormula G).length + 3 := by
    simp [transferCost, leafInput, RecordPrograms.state, ports]
  have hanswer : SubexpDecodeProgram.answer stages.modulus.bits stages.output.c0.val =
      test n (ExecQuantitativeSparsify.encodeRawFormula G) := by
    apply Bool.eq_iff_iff.mpr
    exact (SubexpLeafSemantics.answer_iff G hell hcap layout stages.modulus stages.output
      hn stages.reconstructed).trans (test_encodeRawFormula_iff G).symm
  refine ⟨rf, run, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [LeafRun.steps, run, leafBound]
    rw [htransfer]
    dsimp only [ReconstructionStages.prefixSteps] at hbits ⊢
    omega
  · exact SubexpMainReady.finished_ready count hcount stages.afterCRT rf
      stages.modulus.bits stages.width stages.output.c0.val
  · exact (hframe 7 (by decide)).trans hsource
  · exact (hframe 8 (by decide)).trans hpayload
  · simp only [run, ReconstructionStages.finalState, SubexpMainReady.result_answer, hanswer]

/-- This is an explicitly conditional producer interface. The three actual
phase traces, singleton denotation, prefix bound, and restoration of any
additional caller invariant must all be established by concrete producers. -/
def StageProvider (phases : Phases er es) (count : ℕ) (hcount : count ≤ workStacks es)
    (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (valid : Leaf n → Prop)
    (invariant : MainState er es → Prop) (prefixLimit : List Bool → ℕ) : Prop :=
  ∀ (G : Leaf n), valid G → [] ∉ G → ∀ (tail : List Bool) (base : MainState er es),
    invariant base → ∃ (c : Parameters p k Δ r tau),
      ∃ layout : Layout (E := SubexpActualRing.E p)
        (SubexpLEFactorSystem.packed hell hcap (ExecCNF.formulaSet G)).toPattern c,
      ∃ stages : ReconstructionStages phases G hell hcap layout
        (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G)),
        stages.prefixSteps ≤ prefixLimit (ExecQuantitativeSparsify.encodeRawFormula G) ∧
        ∀ rf : Fin 8 → Bool, invariant (finishedData (stages.finalState count hcount rf))

theorem nonempty_leafContract (phases : Phases er es) (count : ℕ)
    (hcount : count ≤ workStacks es)
    (hdecode : phases.decode = SubexpMainReady.procedure er es count hcount)
    (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (hn : 0 < n)
    (valid : Leaf n → Prop) (invariant : MainState er es → Prop)
    (prefixLimit : List Bool → ℕ)
    (ready : ∀ base, invariant base → SubexpMainReady.StorageReady count base ∧
      base.stacks (persistent es 9) = [] ∧ base.stacks (persistent es 10) = [])
    (provider : StageProvider (k := k) (Δ := Δ) (r := r) (tau := tau)
      phases count hcount hell hcap valid invariant prefixLimit) :
    LeafContract phases (test n)
      (fun bits => leafBound er count (wordWidth n ell p) (prefixLimit bits) bits)
      invariant (fun bits => validPayload n valid bits ∧ ¬ SubexpEmptyClauseGuard.HasEmpty bits) := by
  rintro bits tail base ⟨⟨G, hG, rfl⟩, hno⟩ hi
  have hnoempty : [] ∉ G := fun h => hno ((SubexpEmptyClauseGuard.hasEmpty_raw_iff G).mpr h)
  obtain ⟨c, layout, stages, hpref, hinv⟩ := provider G hG hnoempty tail base hi
  obtain ⟨hstorage, hleaf, _⟩ := ready base hi
  obtain ⟨rf, run, hrun, hcost, _, hsource, hpayload, hanswer⟩ :=
    finish_run phases count hcount hdecode G hell hcap hn layout base tail stages hstorage hleaf
  refine ⟨run, ?_, ?_, hsource, hpayload, hanswer⟩
  · change run.steps ≤ leafBound er count (wordWidth n ell p)
      (prefixLimit (ExecQuantitativeSparsify.encodeRawFormula G))
      (ExecQuantitativeSparsify.encodeRawFormula G)
    unfold leafBound at hcost ⊢
    omega
  · rw [hrun]
    exact hinv rf

/-- The real empty-clause guard covers the remaining valid payloads. The
reference byte test is used only to name its proved output bit. -/
theorem guarded_callback_contract (phases : Phases er es) (count : ℕ)
    (hcount : count ≤ workStacks es) (hguard : 9 ≤ count)
    (hdecode : phases.decode = SubexpMainReady.procedure er es count hcount)
    (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (hn : 0 < n)
    (valid : Leaf n → Prop) (invariant : MainState er es → Prop)
    (prefixLimit : List Bool → ℕ)
    (ready : ∀ base, invariant base → SubexpMainReady.StorageReady count base ∧
      base.stacks (persistent es 9) = [] ∧ base.stacks (persistent es 10) = [])
    (provider : StageProvider (k := k) (Δ := Δ) (r := r) (tau := tau)
      phases count hcount hell hcap valid invariant prefixLimit) :
    RecordPrograms.CallbackContractOn (ports er es) (SubexpEmptyClauseGuard.leafCallback phases)
      (test n) (fun bits => leafBound er count (wordWidth n ell p) (prefixLimit bits) bits +
        200 * (bits.length + 1)) invariant (validPayload n valid) := by
  apply SubexpEmptyClauseGuard.callback_contract
    (test n) (fun bits => leafBound er count (wordWidth n ell p) (prefixLimit bits) bits)
    invariant (validPayload n valid)
  · intro bits hv
    exact validPayload_encoded hv
  · intro base hi
    obtain ⟨hs, h9, h10⟩ := ready base hi
    refine ⟨⟨hs.1, ?_⟩, h9, h10⟩
    intro i hi
    exact hs.2 i (hi.trans_le hguard)
  · intro bits hv he
    exact empty_answer hv he
  · exact nonempty_leafContract phases count hcount hdecode hell hcap hn
      valid invariant prefixLimit ready provider

theorem records_any_test (leaves : List (Leaf n)) :
    (leaves.map ExecQuantitativeSparsify.encodeRawFormula).any (test n) = true ↔
      ∃ G ∈ leaves, SAT.Satisfiable (ExecCNF.formulaSet G) := by
  simp only [List.any_eq_true, List.mem_map]
  constructor
  · rintro ⟨bits, ⟨G, hG, rfl⟩, htest⟩
    exact ⟨G, hG, (test_encodeRawFormula_iff G).mp htest⟩
  · rintro ⟨G, hG, hs⟩
    exact ⟨_, ⟨G, hG, rfl⟩, (test_encodeRawFormula_iff G).mpr hs⟩

end SubexponentialSAT.SubexpLeafContract

end OAI.Algorithms
