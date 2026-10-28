import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutSemantics
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutChoicesTrace
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutInvariant
import OAI.Algorithms.SubexponentialSAT.SubexpMainPhysicalSystem
import OAI.Algorithms.SubexponentialSAT.SubexpMainDyadicReadiness
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutTrace
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutStored

namespace OAI.Algorithms

/-!
# The actual layout at the implemented schedule

The numerical premises are obtained from the setup guard, and the bounded
pattern comes from the exact sparse leaf. The layout uses only the choices
returned by the actual finite program.
-/

namespace SubexponentialSAT.SubexpMainScheduledLayout

open BitProgram StructuredCalls SubexpMainProgram SubexpSetupProgram
open SubexpPackingParameters SubexpLayoutSpec
open SubexpMainInvariant (Stored)
open SubexpLayoutPorts (Allocation)

local instance scheduledPrime (n : ℕ) : Fact (p n).Prime := ⟨p_prime n⟩

abbrev parameters (cfg : Config) (n : ℕ) (ready : DyadicSchedule.Ready cfg.k cfg.T n) :
    Parameters (p n) cfg.k (DyadicSchedule.delta cfg.k cfg.T n) (r n) (DyadicSchedule.tau n) :=
  SubexpMainLayoutSemantics.parameters
    (DyadicSchedule.parameters cfg.k cfg.T cfg.width_ge_two n (DyadicSchedule.ready_goodInput ready)) rfl

abbrev scopes {er es n k T : ℕ} {alloc : Allocation es} {a : MainState er es}
    {G : SubexpLeafData.Leaf n} (input : SubexpMainLayoutInput.Ready alloc a n k T G) :=
  SubexpLayoutScopeOrder.orderedScopes (SubexpMainLayout.Factors.sourceInputs alloc a)
    (SubexpMainLayoutInput.castLeaf input.variableCount.symm G)
    input.sparse.clause_sets_nodup input.ell_pos

theorem family {er es n k T : ℕ} {alloc : Allocation es} {a : MainState er es}
    {G : SubexpLeafData.Leaf n} (input : SubexpMainLayoutInput.Ready alloc a n k T G) :
    SubexpClauseFamilyProgram.Valid
      (SubexpLayoutConstruction.familyInputs (SubexpMainLayout.Factors.sourceInputs alloc a))
      (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a))
      (SubexpLayoutConstruction.variableCount (SubexpMainLayout.Factors.sourceInputs alloc a)) :=
  SubexpLayoutConstruction.family_valid (SubexpMainLayout.Factors.sourceInputs alloc a)
    input.modulus_pos input.ell_pos input.width input.dimension

def tables {er es n k T : ℕ} {alloc : Allocation es} {a : MainState er es}
    {G : SubexpLeafData.Leaf n} (input : SubexpMainLayoutInput.Ready alloc a n k T G) :=
  SubexpLayoutConstruction.tables (SubexpMainLayout.Factors.sourceInputs alloc a) (family input)
    (SubexpMainLayoutInput.castLeaf input.variableCount.symm G)

variable {cfg : Config} {er n B : ℕ} {hrBoot : 32 ≤ workRegs er} {hregs : 16 ≤ er}
variable {F : SAT.CNF (Fin n)} {alloc : Allocation (mainExtraStacks cfg)}
variable {a middle out : MainState er (mainExtraStacks cfg)}
variable (boot : SubexpMainBoot.Run cfg hrBoot F) (initial : Stored cfg boot.setupOutput B a)
variable (ready : DyadicSchedule.Ready cfg.k cfg.T n)
variable {G : SubexpLeafData.Leaf n}
variable (input : SubexpMainLayoutInput.Ready alloc a n cfg.k cfg.T G)
variable [NeZero (r n)]
variable {hd : ∀ v : Fin (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)),
  Subexp.IncidencePlanSpec.degree (scopes input) v.val ≤ DyadicSchedule.delta cfg.k cfg.T n}
variable (result : SubexpMainLayoutExecution.Result hregs alloc a middle out
  (p n) (r n) (DyadicSchedule.delta cfg.k cfg.T n) (DyadicSchedule.R cfg.k cfg.T n)
  (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a))
  (goodInput_s_pos (DyadicSchedule.ready_goodInput ready)) (DyadicSchedule.Q_pos n)
  (scopes input) hd (tables input))

noncomputable def layout : Layout (E := SubexpActualRing.E (p n))
    (Subexp.IncidencePlanSpec.pattern
      (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)) (scopes input))
    (parameters cfg n ready) :=
  SubexpMainLayoutSemantics.layout
    (DyadicSchedule.parameters cfg.k cfg.T cfg.width_ge_two n (DyadicSchedule.ready_goodInput ready))
    rfl result (SubexpMainLayoutPattern.bounded alloc a G input (by have := cfg.width_ge_two; omega))
    (by rw [SubexpMainParameterValues.sourceInputs_dimension alloc boot initial]
        exact SubexpMainDyadicReadiness.size cfg.k cfg.T cfg.width_ge_two ready)
    (SubexpMainDyadicReadiness.threshold cfg.k cfg.T cfg.width_ge_two ready)
    (SubexpMainDyadicReadiness.normalized_tail cfg.k cfg.T cfg.width_ge_two ready)

theorem layout_node (i : Fin ((p n)^4 - 1)) :
    (layout boot initial ready input result).node i =
      (SubexpMachineNodeOrder.nodeEquiv (p n) i).val := rfl

/-- Every cost witness is accompanied by its actual stage execution. -/
structure Run {cfg : Config} {er n : ℕ} [NeZero (r n)]
    (alloc : Allocation (mainExtraStacks cfg)) (hregs : 16 ≤ er)
    (a : MainState er (mainExtraStacks cfg)) (G : SubexpLeafData.Leaf n)
    (input : SubexpMainLayoutInput.Ready alloc a n cfg.k cfg.T G)
    (ready : DyadicSchedule.Ready cfg.k cfg.T n) where
  degree : ∀ v : Fin (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)),
    Subexp.IncidencePlanSpec.degree (scopes input) v.val ≤ DyadicSchedule.delta cfg.k cfg.T n
  factorState : MainState er (mainExtraStacks cfg)
  assignmentState : MainState er (mainExtraStacks cfg)
  start : MainState er (mainExtraStacks cfg)
  coefficientState : MainState er (mainExtraStacks cfg)
  packingState : MainState er (mainExtraStacks cfg)
  middle : MainState er (mainExtraStacks cfg)
  out : MainState er (mainExtraStacks cfg)
  steps : ℕ
  result : SubexpMainLayoutExecution.Result hregs alloc a middle out
    (p n) (r n) (DyadicSchedule.delta cfg.k cfg.T n) (DyadicSchedule.R cfg.k cfg.T n)
    (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a))
    (goodInput_s_pos (DyadicSchedule.ready_goodInput ready)) (DyadicSchedule.Q_pos n)
    (scopes input) degree (tables input)
  bound : steps ≤
    SubexpMainLayoutPrefix.runtimeBound alloc a factorState assignmentState (family input)
      (SubexpMainLayoutInput.castLeaf input.variableCount.symm G)
      input.sparse.clause_sets_nodup input.ell_pos (r n) ((p n)^4 - 1) (DyadicSchedule.delta cfg.k cfg.T n) +
    SubexpMainLayoutChoices.tailBound alloc hregs a start coefficientState packingState middle result.choices +
    SubexpMainLayoutRows.runtimeBound (List.ofFn result.choices.coefficients)
      result.choices.packing.packing (scopes input) degree result.rows + 2
  stages : SubexpMainLayoutTrace.StageTrace alloc hregs a factorState assignmentState start
    coefficientState packingState middle out result
    (SubexpMainLayout.Factors.runtimeBound alloc a (family input)
      (SubexpMainLayoutInput.castLeaf input.variableCount.symm G))
  entry : SubexpMainLayoutChoices.EntryFacts alloc a packingState
  trace : Eval (SubexpMainLayoutProgram.procedure er hregs alloc).invoke steps a out

theorem run_exists : Nonempty (Run alloc hregs a G input ready) := by
  obtain ⟨hd, f, s, t, c, pk, m, o, steps, result, hb, ht, he, hr⟩ :=
    SubexpMainLayoutTrace.execution alloc hregs a (p n) (r n)
      (DyadicSchedule.delta cfg.k cfg.T n) (DyadicSchedule.R cfg.k cfg.T n)
      cfg.k (DyadicSchedule.B cfg.k cfg.T n)
      (goodInput_s_pos (DyadicSchedule.ready_goodInput ready)) (DyadicSchedule.Q_pos n)
      (Subexp.LocalBasisBatchScheduleBounds.scheduled_two_ne_zero n)
      input.ell_pos input.width input.modulus_pos
      (SubexpMainLayoutInput.castLeaf input.variableCount.symm G)
      input.sparse.clause_sets_nodup input.leafBytes input.dimension input.capacity
      (by have := cfg.width_ge_two; omega) input.sparse.width input.sparse.occurrences
      input.no_empty input.delta input.metadata input.empty input.prime input.colors
      input.Q input.R input.precision input.exponent
  exact ⟨⟨hd, f, s, t, c, pk, m, o, steps, result, hb, ht, he, hr⟩⟩

noncomputable def Run.layout (actual : Run alloc hregs a G input ready) :
    Layout (E := SubexpActualRing.E (p n))
      (Subexp.IncidencePlanSpec.pattern
        (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)) (scopes input))
      (parameters cfg n ready) :=
  SubexpMainScheduledLayout.layout boot initial ready input actual.result

include initial in
theorem Run.stored (actual : Run alloc hregs a G input ready)
    (halloc : alloc.ordinaryCount = helperSize cfg)
    (hB : SubexpMainCacheBounds.regeneratedBound (p n) (D n) ≤ B) :
    Stored cfg boot.setupOutput B actual.out := by
  apply SubexpMainLayoutStored.stored actual.result actual.stages.choices halloc initial
  rw [SubexpMainParameterValues.sourceInputs_dimension alloc boot initial]
  exact hB

/-- The actual leaf parser state produces a checked layout run, with the
same stored invariant at its output. Every native input premise is derived. -/
theorem transferred_run (halloc : alloc.ordinaryCount = helperSize cfg)
    (base : MainState er (mainExtraStacks cfg))
    (invariant : SubexpMainInvariant.Invariant cfg boot.setupOutput B base)
    (valid : SubexpMainAssembly.validLeaf cfg n G) (hne : [] ∉ G) (tail : List Bool)
    (hB : SubexpMainCacheBounds.regeneratedBound (p n) (D n) ≤ B) :
    let a := transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))
    let input := SubexpMainLayoutInput.ready_transferred alloc halloc boot base invariant
      (DyadicSchedule.ready_goodInput ready) G valid hne tail
    ∃ actual : Run alloc hregs a G input ready,
      Stored cfg boot.setupOutput B actual.out := by
  dsimp only
  let inp := SubexpMainLayoutInput.ready_transferred alloc halloc boot base invariant
    (DyadicSchedule.ready_goodInput ready) G valid hne tail
  obtain ⟨actual⟩ := run_exists ready inp
  refine ⟨actual, ?_⟩
  exact Run.stored boot
    (SubexpMainInvariant.stored_transferred_input base invariant.toStored tail _)
    ready inp actual halloc hB

end SubexponentialSAT.SubexpMainScheduledLayout

end OAI.Algorithms
