import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainScheduledLayout
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawLayoutInput

namespace OAI.Algorithms

/-! Scheduled layout semantics for the actual ordered boot. The native Run
record and fixed layout program are reused without conversion. -/

namespace SubexponentialSAT.SubexpOrderedRawScheduledLayout

open BitProgram StructuredCalls SubexpMainProgram SubexpSetupProgram
open SubexpPackingParameters SubexpLayoutSpec
open SubexpMainInvariant (Stored)
open SubexpLayoutPorts (Allocation)
open SubexpMainScheduledLayout (parameters scopes family tables Run)

local instance scheduledPrime (n : ℕ) : Fact (p n).Prime := ⟨p_prime n⟩

variable {cfg : Config} {er n B : ℕ} {hrBoot : 32 ≤ workRegs er} {hregs : 16 ≤ er}
variable {F : SubexpOrderedRawPrefix.Formula n} {alloc : Allocation (mainExtraStacks cfg)}
variable {a middle out : MainState er (mainExtraStacks cfg)}
variable (boot : SubexpOrderedRawBoot.Run cfg hrBoot F) (initial : Stored cfg boot.setupOutput B a)
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
    (by rw [SubexpOrderedRawParameterValues.sourceInputs_dimension alloc boot initial]
        exact SubexpMainDyadicReadiness.size cfg.k cfg.T cfg.width_ge_two ready)
    (SubexpMainDyadicReadiness.threshold cfg.k cfg.T cfg.width_ge_two ready)
    (SubexpMainDyadicReadiness.normalized_tail cfg.k cfg.T cfg.width_ge_two ready)

theorem layout_node (i : Fin ((p n)^4 - 1)) :
    (layout boot initial ready input result).node i =
      (SubexpMachineNodeOrder.nodeEquiv (p n) i).val := rfl

noncomputable def runLayout (actual : Run alloc hregs a G input ready) :
    Layout (E := SubexpActualRing.E (p n))
      (Subexp.IncidencePlanSpec.pattern
        (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)) (scopes input))
      (parameters cfg n ready) :=
  SubexpOrderedRawScheduledLayout.layout boot initial ready input actual.result

include initial in
theorem run_stored (actual : Run alloc hregs a G input ready)
    (halloc : alloc.ordinaryCount = helperSize cfg)
    (hB : SubexpMainCacheBounds.regeneratedBound (p n) (D n) ≤ B) :
    Stored cfg boot.setupOutput B actual.out := by
  apply SubexpMainLayoutStored.stored actual.result actual.stages.choices halloc initial
  rw [SubexpOrderedRawParameterValues.sourceInputs_dimension alloc boot initial]
  exact hB

/-- The actual leaf parser state produces a checked layout run, with the
same stored invariant at its output. Every native input premise is derived. -/
theorem transferred_run (halloc : alloc.ordinaryCount = helperSize cfg)
    (base : MainState er (mainExtraStacks cfg))
    (invariant : SubexpMainInvariant.Invariant cfg boot.setupOutput B base)
    (valid : SubexpMainAssembly.validLeaf cfg n G) (hne : [] ∉ G) (tail : List Bool)
    (hB : SubexpMainCacheBounds.regeneratedBound (p n) (D n) ≤ B) :
    let a := transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))
    let input := SubexpOrderedRawLayoutInput.ready_transferred alloc halloc boot base invariant
      (DyadicSchedule.ready_goodInput ready) G valid hne tail
    ∃ actual : Run alloc hregs a G input ready,
      Stored cfg boot.setupOutput B actual.out := by
  dsimp only
  let inp := SubexpOrderedRawLayoutInput.ready_transferred alloc halloc boot base invariant
    (DyadicSchedule.ready_goodInput ready) G valid hne tail
  obtain ⟨actual⟩ := SubexpMainScheduledLayout.run_exists ready inp
  refine ⟨actual, ?_⟩
  exact run_stored boot
    (SubexpMainInvariant.stored_transferred_input base invariant.toStored tail _)
    ready inp actual halloc hB

end SubexponentialSAT.SubexpOrderedRawScheduledLayout

end OAI.Algorithms
