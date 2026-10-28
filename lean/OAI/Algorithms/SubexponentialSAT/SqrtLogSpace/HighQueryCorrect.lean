import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount

/-! Actual whole-query composition after the high iterator. The two joins
below consume the fixed iterator's measured execution, preserve the same
prepared witnesses, and execute the existing complete return and cleanup.
The public marked and accepted theorems instantiate HighQueryCount directly. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect

open BitProgram StructuredCalls HighMarkedFrontend HighQuerySetup
open HashGreedyProgram.NativeRound

abbrev Data := State 40 896

def markedBudget (frontCost S cost loopCost D : ℕ) : ℕ :=
  frontCost + cost + 110 * localBound S cost + loopCost + 3421 * D + 5218

def acceptedBudget (frontCost S cost loopCost D : ℕ) : ℕ :=
  frontCost + cost + 110 * localBound S cost + loopCost + 3430 * D + 5229

/-- Prefix storage contains no high-loop runtime or completed-rank count. -/
def space (q : SqrtLog.LeafQueryFrontend.Query) (A frontCost S B cost K D : ℕ) : ℕ :=
  max (A + frontCost) (max (max (prefixBound q S cost B) K) (931 * D + 54))

/-- Every actual high rank pays its stream, refresh, addition and odometer. -/
def loopBudget (n h t d Q J A T work : ℕ) : ℕ :=
  2^h*(QueryStreamCorrect.budget n t d Q J A T work+
    11*QueryHeadBudgets.compact A+16*(n+2)+28*h+27)+3

def loopSpace (n h t d J A T : ℕ) : ℕ :=
  max (max (max (QueryHeadBudgets.compact A) (QueryStreamCorrect.space n t d J A T))
    (20*(n+2))) (40*(h+1))

private theorem input_prefix (command : Cmd 40 896) (a : Data) (steps A bound : ℕ)
    (ht : steps  ≤  bound) (ha : ∀ i, (a.stacks i).length  ≤  A) :
    StageSpace command steps a (A + bound) := by
  constructor
  intro t z ht' hz i
  have h := trace_selectedStackBits (compiled command 778 777) {i} hz
  have h' : (z.stacks i).length  ≤  (a.stacks i).length + t := by
    simpa only [selectedStackBits,Finset.sum_singleton] using h
  have := ha i
  omega

section Return

variable {q : SqrtLog.LeafQueryFrontend.Query} {k : ℕ}
  {hg : SqrtLog.LeafParametersProgram.Guard (q.input k)}
  {front : Data} {padding : Fin 8 → ℕ} {S B cost : ℕ}
  (run : PreparedRun q k hg front padding S B cost)

local notation "seeded" => HighCountSeed.initialized (result front run.output) run.seedRegs

/-- The actual frontend, successful guard, complete high loop and canonical
marked return form one execution with the exact891-word callback frame. -/
theorem marked_of_loop (input last : Data) (frontSteps frontCost loopSteps A D K n count : ℕ)
    (hfront : Eval (HighMarkedFrontend.command k) frontSteps input front)
    (hfrontCost : frontSteps  ≤  frontCost) (hinput : ∀ i, (input.stacks i).length  ≤  A)
    (hloop : Eval HighQueryProgram.highLoop loopSteps seeded last)
    (hloopSpace : StageSpace HighQueryProgram.highLoop loopSteps seeded K)
    (hcount : BinaryArithmetic.toNat (last.stacks 788) = count)
    (hcountBound : count  ≤  2 ^ n) (hn : n + 1  ≤  D)
    (hbound : ∀ i, (last.stacks i).length  ≤  D)
    (hkept : ∀ i, HashMarkedReturn.kept i = true → last.stacks i = input.stacks i)
    (hblank : ∀ i, HashMarkedReturn.kept i = false →
      (i.val < 320 ∨ 324 < i.val) → input.stacks i = [])
    (hscratch : input.stacks 767 = []) :
    ∃ steps,
      Eval (HighQueryProgram.marked k) steps input (HighQueryExecution.returned last) ∧
      steps + 1  ≤  markedBudget frontCost S cost loopSteps D ∧
      (HighQueryExecution.returned last).stacks 323 = countWord count ∧
      HashMassAdapter.workspace (HighQueryExecution.returned last) = HashMassAdapter.workspace input ∧
      HashMassAdapter.read (HighQueryExecution.returned last) = HashMassAdapter.read input ∧
      RecordPrograms.state HashMassAdapter.recordPorts (HighQueryExecution.returned last)
        false true false (input.stacks 320) [] = HighQueryExecution.returned last ∧
      (HighQueryExecution.returned last).stacks 324 = [] ∧
      StageSpace (HighQueryProgram.marked k) (steps+1) input
        (space q A frontCost S B cost K D) := by
  have hc : BinaryArithmetic.toNat (last.stacks 788)  ≤  2^n := hcount.trans_le hcountBound
  have ht : last.stacks 767 = [] := (hkept 767 (by decide)).trans hscratch
  let ng := run.packingSteps + run.arithmeticSteps + 1 + (run.seedSteps + loopSteps) + 1
  obtain ⟨heg,hsg⟩ := run.guard_loop last loopSteps K hloop hloopSpace
  obtain ⟨nr,her,hrt,_htr,hsr⟩ := HighQueryExecution.markedReturn_trace_space last n D hc hn hbound ht
  have he : Eval (HighQueryProgram.marked k) (frontSteps+(ng+nr)) input
      (HighQueryExecution.returned last) := hfront.seq (heg.seq her)
  have hfs : StageSpace (HighMarkedFrontend.command k) frontSteps input
      (space q A frontCost S B cost K D) := by
    have h := input_prefix (HighMarkedFrontend.command k) input frontSteps A frontCost hfrontCost hinput
    exact ⟨fun t z ht hz i => (h.bound t z ht hz i).trans (Nat.le_max_left _ _)⟩
  have hgs : StageSpace HighQueryProgram.guardedCount ng front
      (space q A frontCost S B cost K D) := by
    exact ⟨fun t z ht hz i => (hsg.bound t z (by omega) hz i).trans
      ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))⟩
  have hrs : StageSpace HighQueryExecution.markedReturn nr last
      (space q A frontCost S B cost K D) := by
    exact ⟨fun t z ht hz i => (hsr.bound t z (by omega) hz i).trans
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))⟩
  have hpref := StageSpace.seq hfront (heg.seq her) hfs (StageSpace.seq heg her hgs hrs)
  refine ⟨_,he,?_,?_,HighQueryExecution.returned_workspace input last hkept hblank,?_,?_,?_,?_⟩
  · have hp := run.time
    dsimp only [markedBudget]
    omega
  · rw [HighQueryExecution.returned_count,hcount]
  · change (HighQueryExecution.returned last).stacks 322 = input.stacks 322
    simpa [HighQueryExecution.returned_stacks,HashMarkedReturn.kept,Fin.coe_ofNat_eq_mod]
      using hkept 322 (by decide)
  · have hr := HighQueryExecution.returned_record last
    rwa [hkept 320 (by decide)] at hr
  · simp [HighQueryExecution.returned_stacks,HashMarkedReturn.kept,Fin.coe_ofNat_eq_mod]
  · exact ⟨StructuredSpace.compiled_halt_stack_bound he 778 777 hpref.bound⟩

/-- The actual accepted query has the same complete sequence but its paid
return leaves the canonical whole word on788 and restores every other word. -/
theorem accepted_of_loop (input last : Data) (frontSteps frontCost loopSteps A D K n count : ℕ)
    (hfront : Eval (HighMarkedFrontend.acceptedCommand k) frontSteps input front)
    (hfrontCost : frontSteps  ≤  frontCost) (hinput : ∀ i, (input.stacks i).length  ≤  A)
    (hloop : Eval HighQueryProgram.highLoop loopSteps seeded last)
    (hloopSpace : StageSpace HighQueryProgram.highLoop loopSteps seeded K)
    (hcount : BinaryArithmetic.toNat (last.stacks 788) = count)
    (hcountBound : count  ≤  2 ^ n) (hn : n + 1  ≤  D)
    (hbound : ∀ i, (last.stacks i).length  ≤  D)
    (hkept : ∀ i, HashMarkedReturn.kept i = true → last.stacks i = input.stacks i)
    (hblank : ∀ i, i  ≠  788 → HashMarkedReturn.kept i = false → input.stacks i = [])
    (hscratch : input.stacks 767 = []) :
    ∃ steps,
      Eval (HighQueryProgram.accepted k) steps input (HighQueryExecution.accepted last) ∧
      steps + 1  ≤  acceptedBudget frontCost S cost loopSteps D ∧
      (HighQueryExecution.accepted last).stacks = Function.update input.stacks 788 (countWord count) ∧
      StageSpace (HighQueryProgram.accepted k) (steps+1) input
        (space q A frontCost S B cost K D) := by
  have hc : BinaryArithmetic.toNat (last.stacks 788)  ≤  2^n := hcount.trans_le hcountBound
  have ht : last.stacks 767 = [] := (hkept 767 (by decide)).trans hscratch
  let ng := run.packingSteps + run.arithmeticSteps + 1 + (run.seedSteps + loopSteps) + 1
  obtain ⟨heg,hsg⟩ := run.guard_loop last loopSteps K hloop hloopSpace
  obtain ⟨nr,her,hrt,_htr,hsr⟩ := HighQueryExecution.acceptedReturn_trace_space last n D hc hn hbound ht
  have he : Eval (HighQueryProgram.accepted k) (frontSteps+(ng+nr)) input
      (HighQueryExecution.accepted last) := hfront.seq (heg.seq her)
  have hfs : StageSpace (HighMarkedFrontend.acceptedCommand k) frontSteps input
      (space q A frontCost S B cost K D) := by
    have h := input_prefix (HighMarkedFrontend.acceptedCommand k) input frontSteps A frontCost hfrontCost hinput
    exact ⟨fun t z ht hz i => (h.bound t z ht hz i).trans (Nat.le_max_left _ _)⟩
  have hgs : StageSpace HighQueryProgram.guardedCount ng front
      (space q A frontCost S B cost K D) := by
    exact ⟨fun t z ht hz i => (hsg.bound t z (by omega) hz i).trans
      ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))⟩
  have hrs : StageSpace HighQueryExecution.acceptedReturn nr last
      (space q A frontCost S B cost K D) := by
    exact ⟨fun t z ht hz i => (hsr.bound t z (by omega) hz i).trans
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))⟩
  have hpref := StageSpace.seq hfront (heg.seq her) hfs (StageSpace.seq heg her hgs hrs)
  refine ⟨_,he,?_,?_,?_⟩
  · have hp := run.time
    dsimp only [acceptedBudget]
    omega
  · rw [HighQueryExecution.accepted_exact_frame input last hkept hblank,hcount]
  · exact ⟨StructuredSpace.compiled_halt_stack_bound he 778 777 hpref.bound⟩

end Return

section Complete

open SqrtLog LeafParametersProgram LeafProgram PreparedSource PreparedBranchCount

attribute [local irreducible] Execute.guardedModel

variable {q : LeafQueryFrontend.Query} {k : ℕ} {hg : Guard (q.input k)}
  {front : Data} {padding : Fin 8 → ℕ} {S B cost : ℕ}
  (run : PreparedRun q k hg front padding S B cost)

local notation "seeded" => HighCountSeed.initialized (result front run.output) run.seedRegs
local notation "model" => Execute.guardedModel (q.input k) padding
local notation "n" => BinaryArithmetic.toNat q.ambient

variable (RB RC RD RI RE : ℕ) (hv : q.Valid)
  (frontBase : Query.Data) (bw : Bank.Words)
  (hfrontState : Query.FrontState q k frontBase (project front) padding bw)
  (hready : q.Ready frontBase) (hindex : q.index=Encoding.encodeNat (markIndex q))
  (source : List (List (SAT.Literal (Fin (BinaryArithmetic.toNat q.ambient)))))
  (hsource : q.clauses=HashInputProgram.Expansion.encodedClauses source)
  (hwidth : ∀ clause∈source,clause.length ≤ k)
  (A T : ℕ)
  (hwords : ∀ i,((HighCountSeed.initialized (result front run.output) run.seedRegs).stacks i).length ≤ A)
  (hvalues : ∀ i,(Execute.guardedModel (q.input k) padding).val i ≤ A)
  (hAT : A ≤ T) (hqsize : 3^((Execute.guardedModel (q.input k) padding).val 34) ≤ T)

local notation "hashes" => List.map
  (fun terms => List.map (fun term =>
    (Prod.snd term,HashInputProgram.Expansion.originalClause source (Prod.fst term))) terms)
  (castRows (congrArg List.length hsource) (LeafQueryFrontend.Query.rows q))
local notation "count" => fullCount hashes (Option.isSome (LeafQueryFrontend.Query.mark q))
  (List.getD source (markIndex q) [])
local notation "work" => CostAssembly.assembledWork k (ProducedQueryResources.ambient q)
  (ProducedQueryResources.ofPacking q k RB RC RD RI RE hg run.first run.rest)
local notation "highCost" => loopBudget n (Finset.card (highSet q)) (Circuit.Model.val model 33)
  (Circuit.Model.val model 34) (Circuit.Model.val model 21) (Circuit.Model.val model 42) A T work
local notation "highSpace" => loopSpace n (Finset.card (highSet q)) (Circuit.Model.val model 33)
  (Circuit.Model.val model 34) (Circuit.Model.val model 42) A T

include hv hfrontState hready hindex hwidth hwords hvalues hAT hqsize in
/-- Complete fixed marked query: every conditioned evaluator and every high
rank is executed by the actual native programs. Only factual outputs of the
already executed frontend/preparation are used to start the continuation. -/
theorem marked (input : Data) (frontSteps frontCost inputCap : ℕ)
    (hfront : Eval (HighMarkedFrontend.command k) frontSteps input front)
    (hfrontCost : frontSteps  ≤  frontCost) (hinput : ∀ i,(input.stacks i).length ≤ inputCap)
    (hkept : ∀ i,HashMarkedReturn.kept i= true → (seeded).stacks i=input.stacks i)
    (hblank : ∀ i,HashMarkedReturn.kept i= false →
      (i.val < 320 ∨ 324 < i.val) → input.stacks i=[])
    (hscratch : input.stacks 767=[]) :
    ∃ steps output,
      Eval (HighQueryProgram.marked k) steps input output ∧
      steps+1 ≤ markedBudget frontCost S cost highCost (QueryHeadBudgets.compact A) ∧
      output.stacks 323=countWord count ∧
      HashMassAdapter.workspace output=HashMassAdapter.workspace input ∧
      HashMassAdapter.read output=HashMassAdapter.read input ∧
      RecordPrograms.state HashMassAdapter.recordPorts output false true false
        (input.stacks 320) []=output ∧ output.stacks 324=[] ∧
      StageSpace (HighQueryProgram.marked k) (steps+1) input
        (space q inputCap frontCost S B cost highSpace (QueryHeadBudgets.compact A)) := by
  change ∀ i : Fin 64, (Execute.guardedModel (q.input k) padding).val i ≤ A at hvalues
  have complete := @HighQueryCount.run q k hg front padding S B cost run
    RB RC RD RI RE hv frontBase bw hfrontState hready hindex
    source hsource hwidth A T hwords
  specialize complete hvalues hAT hqsize
  obtain ⟨nl,last,he,ht,hcount,_hwidth,_h323,_h791,_h789,_h790,_hguard,hframe,hbound,_htrace,hs⟩ := complete
  have htime : nl+1 ≤ highCost := by
    dsimp only [loopBudget]
    convert ht using 1
    ring
  have hn : n ≤ A := by
    have hh := hwords 338
    rw [HighQueryPreparedSource.mask run] at hh
    simpa [HighIncidenceProgram.descendingHighMask,
      OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.coordinates] using hh
  have hw := (HighQueryCount.compact_width (highSet q) hn).2
  have hp : StageSpace HighQueryProgram.highLoop nl seeded highSpace :=
    ⟨fun t z ht hz i => hs.bound t z (by omega) hz i⟩
  obtain ⟨steps,whole,hcost,hword,hworkspace,hread,hrecord,hscratch',hspace⟩ :=
    marked_of_loop run input last frontSteps frontCost nl inputCap
      (QueryHeadBudgets.compact A) highSpace n count hfront hfrontCost hinput he hp hcount
      (HighQueryLoop.full_count_le _ _ _) hw hbound
      (fun i hi => (hframe i hi).trans (hkept i hi)) hblank hscratch
  refine ⟨steps,_,whole,?_,hword,hworkspace,hread,hrecord,hscratch',hspace⟩
  exact hcost.trans (by dsimp only [markedBudget]; omega)

include hv hfrontState hready hindex hwidth hwords hvalues hAT hqsize in
/-- Complete fixed accepted query executes the same actual high-count loop,
then leaves exactly the canonical full count788 and restores all other words. -/
theorem accepted (input : Data) (frontSteps frontCost inputCap : ℕ)
    (hfront : Eval (HighMarkedFrontend.acceptedCommand k) frontSteps input front)
    (hfrontCost : frontSteps  ≤  frontCost) (hinput : ∀ i,(input.stacks i).length ≤ inputCap)
    (hkept : ∀ i,HashMarkedReturn.kept i= true → (seeded).stacks i=input.stacks i)
    (hblank : ∀ i,i ≠ 788 → HashMarkedReturn.kept i= false → input.stacks i=[])
    (hscratch : input.stacks 767=[]) :
    ∃ steps output,
      Eval (HighQueryProgram.accepted k) steps input output ∧
      steps+1 ≤ acceptedBudget frontCost S cost highCost (QueryHeadBudgets.compact A) ∧
      output.stacks=Function.update input.stacks 788 (countWord count) ∧
      StageSpace (HighQueryProgram.accepted k) (steps+1) input
        (space q inputCap frontCost S B cost highSpace (QueryHeadBudgets.compact A)) := by
  change ∀ i : Fin 64, (Execute.guardedModel (q.input k) padding).val i ≤ A at hvalues
  have complete := @HighQueryCount.run q k hg front padding S B cost run
    RB RC RD RI RE hv frontBase bw hfrontState hready hindex
    source hsource hwidth A T hwords
  specialize complete hvalues hAT hqsize
  obtain ⟨nl,last,he,ht,hcount,_hwidth,_h323,_h791,_h789,_h790,_hguard,hframe,hbound,_htrace,hs⟩ := complete
  have htime : nl+1 ≤ highCost := by
    dsimp only [loopBudget]
    convert ht using 1
    ring
  have hn : n ≤ A := by
    have hh := hwords 338
    rw [HighQueryPreparedSource.mask run] at hh
    simpa [HighIncidenceProgram.descendingHighMask,
      OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.coordinates] using hh
  have hw := (HighQueryCount.compact_width (highSet q) hn).2
  have hp : StageSpace HighQueryProgram.highLoop nl seeded highSpace :=
    ⟨fun t z ht hz i => hs.bound t z (by omega) hz i⟩
  obtain ⟨steps,whole,hcost,hword,hspace⟩ :=
    accepted_of_loop run input last frontSteps frontCost nl inputCap
      (QueryHeadBudgets.compact A) highSpace n count hfront hfrontCost hinput he hp hcount
      (HighQueryLoop.full_count_le _ _ _) hw hbound
      (fun i hi => (hframe i hi).trans (hkept i hi)) hblank hscratch
  refine ⟨steps,_,whole,?_,hword,hspace⟩
  exact hcost.trans (by dsimp only [acceptedBudget]; omega)

end Complete
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect
