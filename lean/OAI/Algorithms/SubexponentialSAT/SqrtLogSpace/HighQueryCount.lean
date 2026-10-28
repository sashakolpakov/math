import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryPreparedSource
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryRankCount
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryTraversal
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect

/-! The persistent physical boundary for the actual high-assignment loop.
The ring, source and parked layout words are produced once for this query and
retained across each rank. No execution or evaluator is part of this invariant. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount

open OAI BitProgram StructuredCalls SqrtLog LeafProgram
open HighQueryAdapter

abbrev Data := State 40 896

/-- The node index, coefficient stream and decoded current-high assignment
are regenerated at each rank; the remaining prepared words are unchanged. -/
def preparedPorts : List (Fin 896) :=
  QueryNodeEvaluation.framePorts.filter
    (fun i => i≠307 ∧ i≠863 ∧ i≠702 ∧ i≠703)

theorem preparedPorts_ranges (i : Fin 896) (hi : i∈preparedPorts) :
    i.val<744 ∧ i≠330 ∧ i≠323 ∧ i≠702 ∧ i≠703 := by
  simp only [preparedPorts,List.mem_filter,decide_eq_true_eq] at hi
  obtain ⟨hp,h307,h863,h702,h703⟩ := hi
  have hr : i.val<744 := by
    simp only [QueryNodeEvaluation.framePorts,List.mem_cons,List.not_mem_nil,or_false,
      Fin.ext_iff,Fin.coe_ofNat_eq_mod] at hp
    have hn : i.val≠863 := fun hv => h863 (Fin.ext hv)
    omega
  refine ⟨hr,?_,?_,h702,h703⟩
  · intro h; subst i; simp [QueryNodeEvaluation.framePorts] at hp
  · intro h; subst i; simp [QueryNodeEvaluation.framePorts] at hp

/-- The actual parked layout lies entirely in the repeated high-loop frame. -/
theorem parked_mem (i : Fin 14) :
    NativeLayoutLoad.stackMap (LayoutMasters.high i)∈preparedPorts := by
  fin_cases i <;> decide

/-- All arithmetic words consumed by the concrete node constructor are static
between high assignments. -/
theorem arithmetic_mem (i : Fin 768) (hi : i∈QueryReadyConstruction.arithmeticPorts) :
    i.castAdd 128∈preparedPorts := by
  simp only [QueryReadyConstruction.arithmeticPorts,List.mem_cons,
    List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

/-- The source-local cache cap stays fixed across all high assignments;
transient caller storage is not fed into the next node's source cap. -/
theorem prepared_input_caps {initial a : Data} {A : ℕ}
    (hframe : ∀ i∈preparedPorts,a.stacks i=initial.stacks i)
    (hcache : ∀ i∈QueryNodeEvaluation.cacheInputPorts,(initial.stacks i).length≤A)
    (hparked : ∀ i : Fin 14,
      (initial.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high i))).length≤A) :
    (∀ i∈QueryNodeEvaluation.cacheInputPorts,(a.stacks i).length≤A) ∧
    (∀ i : Fin 14,(a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high i))).length≤A) := by
  constructor
  · intro i hi
    have hm : i∈preparedPorts := by
      simp only [QueryNodeEvaluation.cacheInputPorts,List.mem_cons,
        List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals decide
    rw [hframe i hm]
    exact hcache i hi
  · intro i
    rw [hframe _ (parked_mem i)]
    exact hparked i

/-- The actual seed does not alter any prepared ring, source or layout word. -/
theorem initialized_prepared (a : Data) (rf : Fin 2 → Bool)
    (i : Fin 896) (hi : i∈preparedPorts) :
    (HighCountSeed.initialized a rf).stacks i=a.stacks i := by
  obtain ⟨hlo,h330,h323,_,_⟩ := preparedPorts_ranges i hi
  apply HighCountSeed.initialized_frame
  simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,
    Fin.coe_ofNat_eq_mod] at h330 h323 ⊢
  omega

/-- Refreshing the reusable lower counter retains the same prepared words. -/
theorem copied_prepared (a : Data) (i : Fin 896) (hi : i∈preparedPorts) :
    (copiedHighCounter a).stacks i=a.stacks i := by
  obtain ⟨hlo,h330,_,_,_⟩ := preparedPorts_ranges i hi
  exact copiedHighCounter_frame a i h330 (by
    intro h; have hv:=congrArg Fin.val h; simp at hv; omega)

/-- The genuine odometer changes only its counter and scratch words. -/
theorem advance_prepared (a : Data) (words : List (List Bool))
    (i : Fin 896) (hi : i∈preparedPorts) :
    (ExecCNFTupleEnumeration.advanceResult highPorts.counter a words).stacks i=a.stacks i := by
  have hlo := (preparedPorts_ranges i hi).1
  exact (ExecCNFTupleEnumeration.advanceResult_outside highPorts.counter a words i
    (by intro h; have hv:=congrArg Fin.val h; change i.val=789 at hv; omega)
    (by intro h; have hv:=congrArg Fin.val h; change i.val=790 at hv; omega)).symm

/-- Actual native count addition leaves every prepared input word intact. -/
theorem mass_prepared (a : Data) (rf : Fin 8 → Bool) (acc : List Bool)
    (i : Fin 896) (hi : i∈preparedPorts) :
    (Mass.state highPorts.mass a rf acc []).stacks i=a.stacks i := by
  obtain ⟨hlo,_,h323,_,_⟩ := preparedPorts_ranges i hi
  apply LeafBranchProgram.mass_frame highPorts a rf acc [] i
  intro j
  fin_cases j
  · intro h; have hv:=congrArg Fin.val h; change 788=i.val at hv; omega
  · exact Ne.symm h323
  · intro h; have hv:=congrArg Fin.val h; change 791=i.val at hv; omega

/-- The same static words survive the actual native addition trace. -/
theorem mass_eval_prepared {a b : Data} {steps : ℕ}
    (he : Eval (Mass.invoke highPorts.mass) steps a b) (hs : a.stacks 791=[])
    (i : Fin 896) (hi : i∈preparedPorts) : b.stacks i=a.stacks i := by
  obtain ⟨ticks,_,rf,ht⟩ := Mass.invoke_eval highPorts.mass a
    (fun j => a.regs (highPorts.mass.register j)) (a.stacks 788) (a.stacks 323)
  have hself : Mass.state highPorts.mass a (fun j => a.regs (highPorts.mass.register j))
      (a.stacks 788) (a.stacks 323)=a := LeafBranchProgram.mass_self highPorts a hs
  rw [hself] at ht
  have hb := Eval.final_unique 788 he ht
  rw [hb]
  exact mass_prepared a rf _ i hi

/-- This is the physical frame join around a concrete fixed-stream run.
The stream's actual word equalities are retained through the real adder. -/
theorem branch_prepared_of_stream {a middle b : Data} {querySteps branchSteps : ℕ}
    (he : Eval QueryStreamProgram.command querySteps (copiedHighCounter a) middle)
    (hb : Eval HighQueryProgram.branch branchSteps a b)
    (hs : a.stacks 791=[])
    (hf : ∀ i∈preparedPorts,middle.stacks i=(copiedHighCounter a).stacks i) :
    ∀ i∈preparedPorts,b.stacks i=a.stacks i := by
  change Eval (.seq HighQueryProgram.conditioned (Mass.invoke highPorts.mass)) branchSteps a b at hb
  cases hb with
  | seq hc hm =>
    have hout := Eval.final_unique 789 hc (HighQueryProgram.conditioned_eval a middle querySteps he)
    subst_vars
    have htmp : (⟨Function.update middle.regs 21 true,middle.stacks⟩ : Data).stacks 791=[] :=
      (HighQueryLoop.conditioned_durable_frame he 791 (by simp)).trans hs
    intro i hi
    exact (mass_eval_prepared hm htmp i hi).trans ((hf i hi).trans (copied_prepared a i hi))

/-- A pure physical word frame is stable under the real high odometer.
Its logical assertion contains no code, successful layout or query oracle. -/
theorem prepared_frame_stable (initial : Data) :
    CounterForPrograms.FrameStable highPorts.counter
      (fun _ a => ∀ i∈preparedPorts,a.stacks i=initial.stacks i) := by
  intro _ a b hframe ha i hi
  have hlo := (preparedPorts_ranges i hi).1
  rw [←hframe i
    (by intro h; have hv:=congrArg Fin.val h; change i.val=789 at hv; omega)
    (by intro h; have hv:=congrArg Fin.val h; change i.val=790 at hv; omega)]
  exact ha i hi

/-- Kept caller words are disjoint from the concrete high controller's
reusable counter and mass-adder words. This includes the parked blank767. -/
theorem kept_disjoint (i : Fin 896) (hi : HashMarkedReturn.kept i=true) :
    i≠323 ∧ i≠330 ∧ i≠788 ∧ i≠789 ∧ i≠790 ∧ i≠791 ∧ i≠792 := by
  simp only [HashMarkedReturn.kept,decide_eq_true_eq,Fin.ext_iff,
    Fin.coe_ofNat_eq_mod] at hi ⊢
  omega

/-- The complete caller frame can be carried by the same pure loop invariant. -/
theorem kept_frame_stable (initial : Data) :
    CounterForPrograms.FrameStable highPorts.counter
      (fun _ a => ∀ i,HashMarkedReturn.kept i=true → a.stacks i=initial.stacks i) := by
  intro _ a b hframe ha i hi
  have hd := kept_disjoint i hi
  rw [←hframe i hd.2.2.2.1 hd.2.2.2.2.1]
  exact ha i hi

/-- Actual native addition preserves the full caller frame, not only the
arithmetic words required by the next conditioned query. -/
theorem mass_eval_kept {a b : Data} {steps : ℕ}
    (he : Eval (Mass.invoke highPorts.mass) steps a b) (hs : a.stacks 791=[])
    (i : Fin 896) (hi : HashMarkedReturn.kept i=true) : b.stacks i=a.stacks i := by
  obtain ⟨ticks,_,rf,ht⟩ := Mass.invoke_eval highPorts.mass a
    (fun j => a.regs (highPorts.mass.register j)) (a.stacks 788) (a.stacks 323)
  have hself : Mass.state highPorts.mass a (fun j => a.regs (highPorts.mass.register j))
      (a.stacks 788) (a.stacks 323)=a := LeafBranchProgram.mass_self highPorts a hs
  rw [hself] at ht
  rw [Eval.final_unique 788 he ht]
  have hd := kept_disjoint i hi
  apply LeafBranchProgram.mass_frame highPorts a rf _ [] i
  intro j
  fin_cases j
  · exact Ne.symm hd.2.2.1
  · exact Ne.symm hd.1
  · exact Ne.symm hd.2.2.2.2.2.1

/-- The real copy, fixed query, guard restoration and native adder retain the
same caller words as the actual stream; no global space cap proves this frame. -/
theorem branch_kept_of_stream {a middle b : Data} {querySteps branchSteps : ℕ}
    (he : Eval QueryStreamProgram.command querySteps (copiedHighCounter a) middle)
    (hb : Eval HighQueryProgram.branch branchSteps a b)
    (hs : a.stacks 791=[])
    (hf : ∀ i,HashMarkedReturn.kept i=true →
      middle.stacks i=(copiedHighCounter a).stacks i) :
    ∀ i,HashMarkedReturn.kept i=true → b.stacks i=a.stacks i := by
  change Eval (.seq HighQueryProgram.conditioned (Mass.invoke highPorts.mass)) branchSteps a b at hb
  cases hb with
  | seq hc hm =>
    have hout := Eval.final_unique 789 hc (HighQueryProgram.conditioned_eval a middle querySteps he)
    subst_vars
    have htmp : (⟨Function.update middle.regs 21 true,middle.stacks⟩ : Data).stacks 791=[] :=
      (HighQueryLoop.conditioned_durable_frame he 791 (by simp)).trans hs
    intro i hi
    have hd := kept_disjoint i hi
    exact (mass_eval_kept hm htmp i hi).trans
      ((hf i hi).trans (copiedHighCounter_frame a i hd.2.1 hd.2.2.2.2.2.2))

/-- The concrete prepared-and-seeded run starts at the empty count and the
single zero tuple, even when there are no high coordinates. -/
theorem prepared_seed_entry {q k hg front padding S B cost}
    (run : HighQuerySetup.PreparedRun q k hg front padding S B cost) :
    let a := HighCountSeed.initialized (HighMarkedFrontend.result front run.output) run.seedRegs
    a.stacks 789=Encoding.encodeList id (List.replicate (HighMarkedFrontend.highSet q).card [false]) ∧
    a.stacks 790=[] ∧ a.stacks 323=[] ∧ a.stacks 791=[] ∧
    BinaryArithmetic.toNat (a.stacks 788)=0 ∧ (a.stacks 788).length=0 ∧
    a.regs 21=true ∧
    (∀ i∈preparedPorts,a.stacks i=(HighMarkedFrontend.result front run.output).stacks i) := by
  let a := HighCountSeed.initialized (HighMarkedFrontend.result front run.output) run.seedRegs
  have hf : ∀ i∈preparedPorts,a.stacks i=(HighMarkedFrontend.result front run.output).stacks i :=
    initialized_prepared (HighMarkedFrontend.result front run.output) run.seedRegs
  have hz : a.stacks 788=[] := run.cleared 788 (by decide)
  have hv : BinaryArithmetic.toNat (a.stacks 788)=0 := congrArg BinaryArithmetic.toNat hz
  have hl : (a.stacks 788).length=0 := congrArg List.length hz
  exact ⟨run.counter,run.cleared 790 (by decide),run.cleared 323 (by decide),
    run.cleared 791 (by decide),hv,hl,run.high_guard,hf⟩

/-- The complete high-loop invariant combines only literal word equalities.
Both frames survive the actual odometer and the paid initial guard. -/
theorem complete_frame_stable (initial : Data) :
    CounterForPrograms.FrameStable highPorts.counter (fun _ a =>
      (∀ i∈preparedPorts,a.stacks i=initial.stacks i) ∧
      (∀ i,HashMarkedReturn.kept i=true → a.stacks i=initial.stacks i)) := by
  intro rank a b hf ha
  exact ⟨prepared_frame_stable initial rank a b hf ha.1,
    kept_frame_stable initial rank a b hf ha.2⟩

/-- The high counter and exact accumulator fit the compact boundary from
an independent ambient source cap. No prefix allowance enters this bound. -/
theorem compact_width {n A : ℕ} (H : Finset (Fin n)) (hn : n≤A) :
    4*H.card+1≤QueryHeadBudgets.compact A ∧ n+1≤QueryHeadBudgets.compact A := by
  have hh : H.card≤n := by simpa using Finset.card_le_univ H
  have hs := QueryHeadBudgets.original_le_scalar A
  change 4*H.card+1≤HeadSumBudgets.compactCap (QueryHeadBudgets.scalarCap A) ∧
    n+1≤HeadSumBudgets.compactCap (QueryHeadBudgets.scalarCap A)
  unfold HeadSumBudgets.compactCap
  omega

section PreparedInputs

open LeafParametersProgram

variable {q : LeafQueryFrontend.Query} {k : ℕ} {hg : Guard (q.input k)}
    {front : Data} {padding : Fin 8 → ℕ} {S B cost : ℕ}
    (run : HighQuerySetup.PreparedRun q k hg front padding S B cost)

local notation "seeded" => HighCountSeed.initialized
  (HighMarkedFrontend.result front run.output) run.seedRegs
local notation "model" => Execute.guardedModel (q.input k) padding

/-- Every rank reads the layout physically produced by this same preparation. -/
theorem prepared_parked (a : Data)
    (hf : ∀ i∈preparedPorts,a.stacks i=(seeded).stacks i) (j : Fin 14) :
    a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j)) =
      (PackingCallerProgram.result (HighMarkedFrontend.project front)
        (Query.packingProblem q k hg) run.first run.rest).stacks (LayoutMasters.high j) :=
  (hf _ (parked_mem j)).trans (HighQueryPreparedSource.parked run j)

/-- The arithmetic witness is the actual preparation output, with unchanged
physical cache words at each repeated branch boundary. -/
theorem prepared_arithmetic (a : Data)
    (hf : ∀ i∈preparedPorts,a.stacks i=(seeded).stacks i)
    (i : Fin 768) (hi : i∈QueryReadyConstruction.arithmeticPorts) :
    a.stacks (i.castAdd 128)=run.output.stacks i :=
  (hf _ (arithmetic_mem i hi)).trans (HighQueryPreparedSource.arithmetic_words run i hi)

/-- Both node serializations remain the ones emitted by the same ring run. -/
theorem prepared_nodes (a : Data)
    (hf : ∀ i∈preparedPorts,a.stacks i=(seeded).stacks i) :
    a.stacks 300=Encoding.encodeList id
      (RingNodeMetadata.nodeBits ((model).val 33) ((model).val 34) ((model).val 21)) ∧
    a.stacks 256=
      (RingNodeMetadata.nodeBits ((model).val 33) ((model).val 34) ((model).val 21)).flatten :=
  ⟨(hf 300 (by decide)).trans (HighQueryPreparedSource.nodes run).1,
    (hf 256 (by decide)).trans (HighQueryPreparedSource.nodes run).2⟩

/-- A repeated branch retains this query's own computed high set. -/
theorem prepared_mask (a : Data)
    (hf : ∀ i∈preparedPorts,a.stacks i=(seeded).stacks i) :
    a.stacks 338=HighIncidenceProgram.descendingHighMask (HighMarkedFrontend.highSet q) :=
  (hf 338 (by decide)).trans (HighQueryPreparedSource.mask run)

/-- Literal source and current-marker inputs at every rank follow from the
same frontend execution and original readiness, rather than a supplied source. -/
theorem prepared_sources (a : Data)
    (hf : ∀ i∈preparedPorts,a.stacks i=(seeded).stacks i)
    (base : Query.Data) (w : Bank.Words)
    (hfront : Query.FrontState q k base (HighMarkedFrontend.project front) padding w)
    (hr : q.Ready base) :
    a.stacks 700=Encoding.encodeList id q.clauses ∧
    a.stacks 701=HashScopeProgram.RawTable.inputBits q.width.length q.rows ∧
    a.stacks 704=List.replicate q.rows.length true ∧
    a.stacks 705=q.index ∧ a.stacks 706=[q.mark.isSome] ∧
    a.stacks 707=q.modulus ∧ a.stacks 708=q.width ∧ a.stacks 709=q.ambient := by
  obtain ⟨h700,h701,h704,h705,h706,h707,h708,h709⟩ :=
    HighQueryPreparedSource.sources run base w hfront hr
  exact ⟨(hf 700 (by decide)).trans h700,(hf 701 (by decide)).trans h701,
    (hf 704 (by decide)).trans h704,(hf 705 (by decide)).trans h705,
    (hf 706 (by decide)).trans h706,(hf 707 (by decide)).trans h707,
    (hf 708 (by decide)).trans h708,(hf 709 (by decide)).trans h709⟩

end PreparedInputs

section ActualRun

open LeafParametersProgram PreparedSource PreparedBranchCount LeafBranchProgram
open HashGreedyProgram.NativeRound

variable {q : LeafQueryFrontend.Query} {k : ℕ} {hg : Guard (q.input k)}
    {front : Data} {padding : Fin 8 → ℕ} {S B cost : ℕ}
    (prepared : HighQuerySetup.PreparedRun q k hg front padding S B cost)

local notation "seeded" => HighCountSeed.initialized
  (HighMarkedFrontend.result front prepared.output) prepared.seedRegs
local notation "model" => Execute.guardedModel (q.input k) padding
local notation "H" => HighMarkedFrontend.highSet q
local notation "n" => BinaryArithmetic.toNat q.ambient

/-- Actual complete enumeration of the fresh high set. Every rank invokes the
fixed streamed query, and the same run accumulates the full source count.
The input word and scalar caps are physical preparation bounds; no evaluator,
layout service, branch execution, or repeated-loop bound is assumed. -/
theorem run (RB RC RD RI RE : ℕ) (hv : q.Valid)
    (frontBase : Query.Data) (bw : Bank.Words)
    (hfront : Query.FrontState q k frontBase (HighMarkedFrontend.project front) padding bw)
    (hready : q.Ready frontBase) (hindex : q.index=Encoding.encodeNat (markIndex q))
    (source : List (List (SAT.Literal (Fin n))))
    (hsource : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (hwidth : ∀ clause∈source,clause.length≤k)
    (A T : ℕ) (hwords : ∀ i,((seeded).stacks i).length≤A)
    (hvalues : ∀ i,(model).val i≤A) (hAT : A≤T) (hqsize : 3^((model).val 34)≤T) :
    let hashes := (castRows (congrArg List.length hsource) q.rows).map
      (fun terms => terms.map (fun term =>
        (term.2,HashInputProgram.Expansion.originalClause source term.1)))
    let resources := ProducedQueryResources.ofPacking q k RB RC RD RI RE hg
      prepared.first prepared.rest
    let work := CostAssembly.assembledWork k (ProducedQueryResources.ambient q) resources
    let F := QueryHeadBudgets.compact A
    let C := QueryStreamCorrect.budget n ((model).val 33) ((model).val 34)
      ((model).val 21) ((model).val 42) A T work+11*F+16*(n+2)+15
    let D := max (max F (QueryStreamCorrect.space n ((model).val 33) ((model).val 34)
      ((model).val 42) A T)) (20*(n+2))
    ∃ steps final, Eval HighQueryProgram.highLoop steps seeded final ∧
      steps+1≤2^(H).card*(C+28*(H).card+12)+3 ∧
      BinaryArithmetic.toNat (final.stacks 788)=
        fullCount hashes q.mark.isSome (source[markIndex q]?.getD []) ∧
      (final.stacks 788).length≤n+1 ∧ final.stacks 323=[] ∧ final.stacks 791=[] ∧
      final.stacks 789=Encoding.encodeList id (List.replicate (H).card [false]) ∧
      final.stacks 790=[] ∧ final.regs 21=false ∧
      (∀ i,HashMarkedReturn.kept i=true → final.stacks i=(seeded).stacks i) ∧
      (∀ i,(final.stacks i).length≤F) ∧
      Trace (compiled HighQueryProgram.highLoop 789 788) (steps+1)
        ((seeded).withPC (some (compiled HighQueryProgram.highLoop 789 788).entry))
        (final.withPC none) ∧
      StageSpace HighQueryProgram.highLoop (steps+1) seeded (max D (40*((H).card+1))) := by
  classical
  dsimp only
  let node : Fin (Query.packingProblem q k hg).Q :=
    ⟨0,(Query.packingProblem q k hg).hQ⟩
  let native := LeafHeadSetupProgram.Native.queryInputsAddressed q k hg
    prepared.first prepared.rest node
  let hashes := (castRows (congrArg List.length hsource) q.rows).map
    (fun terms => terms.map (fun term =>
      (term.2,HashInputProgram.Expansion.originalClause source term.1)))
  let work := CostAssembly.assembledWork k (ProducedQueryResources.ambient q)
    (ProducedQueryResources.ofPacking q k RB RC RD RI RE hg prepared.first prepared.rest)
  let F := QueryHeadBudgets.compact A
  let K := QueryStreamCorrect.space n ((model).val 33) ((model).val 34)
    ((model).val 42) A T
  let C := QueryStreamCorrect.budget n ((model).val 33) ((model).val 34)
    ((model).val 21) ((model).val 42) A T work+11*F+16*(n+2)+15
  let D := max (max F K) (20*(n+2))
  let I := fun a : Data =>
    (∀ i∈preparedPorts,a.stacks i=(seeded).stacks i) ∧
    (∀ i,HashMarkedReturn.kept i=true → a.stacks i=(seeded).stacks i)
  have hn : n≤A := by
    have hh := hwords 338
    rw [HighQueryPreparedSource.mask prepared] at hh
    simpa [HighIncidenceProgram.descendingHighMask,
      OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.coordinates] using hh
  have cap := compact_width H hn
  have hQ : (model).val 21=native.Q := numeric_Q q k padding
  have hfield : native.Q<3^((model).val 34) := numeric_field q k padding hg
  have hR : (prepared.packed.stacks 740).length=native.R :=
    HighQueryPreparedSource.packed_radius prepared frontBase bw hfront node
  have hJ : 0<(model).val 42 := QueryTargetMetadata.numeric_order_pos q k padding hg
  have branch : ∀ rank,rank<2^(H).card → ∀ words (a : Data),
      words.map List.length=List.replicate (H).card 1 → I a →
      a.stacks 789=Encoding.encodeList id words → a.stacks 790=[] → a.stacks 791=[] →
      a.regs 21=true → CounterPrograms.value words.flatten=rank →
      BinaryArithmetic.toNat (a.stacks 788)=rankSum
        (rankValue H hashes q.mark.isSome (source[markIndex q]?.getD [])) 0 rank →
      (a.stacks 788).length≤n+1 → (∀ i,(a.stacks i).length≤F) →
      ∃ steps b,Eval HighQueryProgram.branch steps a b ∧ steps≤C ∧ I b ∧
        BinaryArithmetic.toNat (b.stacks 788)=rankSum
          (rankValue H hashes q.mark.isSome (source[markIndex q]?.getD [])) 0 (rank+1) ∧
        (b.stacks 788).length≤n+1 ∧ b.stacks 323=[] ∧ b.stacks 791=[] ∧
        b.stacks 789=a.stacks 789 ∧ b.stacks 790=a.stacks 790 ∧
        (∀ i,(b.stacks i).length≤F) ∧ StageSpace HighQueryProgram.branch steps a D := by
    intro rank hr words a shape invariant hc _hs ht _guard hvRank hacc hlen hb
    let copied := copiedHighCounter a
    have frame : ∀ i∈preparedPorts,copied.stacks i=(seeded).stacks i :=
      fun i hi => (copied_prepared a i hi).trans (invariant.1 i hi)
    have caps := prepared_input_caps frame (fun i _ => hwords i) (fun i => hwords _)
    obtain ⟨s700,s701,s704,s705,s706,s707,s708,s709⟩ :=
      prepared_sources prepared copied frame frontBase bw hfront hready
    have sources : Query.Sources q
        (projectState (id : Fin 40 → Fin 40) QueryAssembler.Nodes.lowPort copied) :=
      ⟨s700,s701,s707,s708,s709⟩
    have rings : ∀ i∈QueryReconstruction.ringPorts,
        copied.stacks (i.castAdd 576)=prepared.ringState.stacks (i.castAdd 320) := by
      intro i hi
      apply Eq.trans (frame _ ?_) (HighQueryPreparedSource.ring_word prepared i)
      simp only [QueryReconstruction.ringPorts,List.mem_cons,
        List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    obtain ⟨cacheWords,hcache,qs,middle,qe,_qt,qcount,_qblank,qbound,qframe,qkept,qtime,qspace⟩ :=
      QueryStreamCorrect.run q k RB RC RD RI RE hg hv prepared.first prepared.rest node
        model padding rfl (Query.ring_precision_pos (q.input k) padding hg)
        (Query.ring_degree_pos (q.input k) padding hg) prepared.modulus prepared.cache
        prepared.half prepared.ringState prepared.packed prepared.output
        prepared.arithmetic_output hfield hQ hR hJ source hsource A T copied
        frontBase (HighMarkedFrontend.project front) bw hfront
        (prepared_parked prepared copied frame) caps.2 caps.1 hvalues sources
        (by rw [frame 700 (by decide)]; exact hwords 700)
        (by rw [frame 701 (by decide)]; exact hwords 701)
        (by rw [frame 708 (by decide)]; exact hwords 708)
        (prepared_nodes prepared copied frame).1 (prepared_mask prepared copied frame)
        (prepared_arithmetic prepared copied frame) prepared.degree s704
        (s705.trans hindex) s706 words shape ⟨rank,hr⟩ hvRank
        ((copiedHighCounter_word a).trans hc) rings
        ((frame 256 (by decide)).trans (HighQueryPreparedSource.ring_word prepared 256))
        hwidth (copiedHighCounter_bound a F hb) hAT hqsize
        (by rw [frame 194 (by decide)]; exact (hwords 194).trans hAT)
        (by rw [frame 202 (by decide)]; exact (hwords 202).trans hAT) cap.2
    have exactCount : middle.stacks 323=countWord
        (rankValue H hashes q.mark.isSome (source[markIndex q]?.getD []) rank) := by
      have value := HighQueryRankCount.native_rank_count native model
        (Query.ring_precision_pos (q.input k) padding hg)
        (Query.ring_degree_pos (q.input k) padding hg) cacheWords hcache
        prepared.modulus prepared.cache prepared.half prepared.ringState
        prepared.arithmetic_output.produced hfield q hv ((model).val 42) hJ
        source hsource H ⟨rank,hr⟩
      exact qcount.trans (congrArg DisjointReuse.binaryNat value)
    have qp : StageSpace QueryStreamProgram.command qs copied K :=
      ⟨fun t z hle he i => qspace.bound t z (by omega) he i⟩
    obtain ⟨steps,b,he,hcost,hvalue,hwidth',hzero,hscratch,hcounter,hcounterScratch,
        _hguard,hbound,hprefix⟩ :=
      HighQueryLoop.branch_step_resources H hashes q.mark.isSome (source[markIndex q]?.getD [])
        rank hr a middle qs F F F K qe qp hacc hlen exactCount ht hb
        (hb 330) (hb 792) (hb 789) cap.2 (fun i _ _ _ => qbound i)
    have pf : ∀ i∈preparedPorts,middle.stacks i=copied.stacks i := by
      intro i hi
      have hm := List.mem_filter.mp hi
      have hn := of_decide_eq_true hm.2
      apply qframe i
      · exact List.mem_filter.mpr ⟨hm.1,by simpa using And.intro hn.1 hn.2.1⟩
      · exact hn.2.2.1
      · exact hn.2.2.2
    refine ⟨steps,b,he,?_,?_,hvalue,hwidth',hzero,hscratch,hcounter,hcounterScratch,hbound,?_⟩
    · have qt : qs≤QueryStreamCorrect.budget n ((model).val 33) ((model).val 34)
          ((model).val 21) ((model).val 42) A T work := (Nat.le_succ qs).trans qtime
      exact hcost.trans (Nat.add_le_add_right
        (Nat.add_le_add_right (Nat.add_le_add_right qt _) _) _)
    · exact ⟨fun i hi => (branch_prepared_of_stream qe he ht pf i hi).trans (invariant.1 i hi),
        fun i hi => (branch_kept_of_stream qe he ht qkept i hi).trans (invariant.2 i hi)⟩
    · exact ⟨fun t z hle ht i => hprefix.bound t z (by omega) ht i⟩
  obtain ⟨hc,hs,_ho,ht,hacc,hlen,_hg,_frame⟩ := prepared_seed_entry prepared
  obtain ⟨steps,final,he,htime,hi,hvalue,hwidth',hzero,hscratch,hcounter,hcounterScratch,
      hguard,hbound,htrace,hprefix⟩ :=
    HighQueryTraversal.high_loop_run H hashes q.mark.isSome (source[markIndex q]?.getD [])
      I F C D (complete_frame_stable seeded) cap.1
      ((Nat.le_max_left F K).trans (Nat.le_max_left _ _)) branch seeded
      ⟨fun _ _ => rfl,fun _ _ => rfl⟩ hc hs ht hacc (by omega)
      (QueryHeadBudgets.incoming_bound seeded A hwords)
  exact ⟨steps,final,he,htime,hvalue,hwidth',hzero,hscratch,hcounter,hcounterScratch,
    hguard,hi.2,hbound,htrace,hprefix⟩

end ActualRun

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount
