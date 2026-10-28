import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawScheduledRows
import OAI.Algorithms.SubexponentialSAT.SubexpNodePacketSemantics

namespace OAI.Algorithms

/-! The actual scheduled factor packet refers to the same row, origin,
and Boolean table as the physical factor system. -/

namespace SubexponentialSAT.SubexpOrderedRawScheduledPackets

open SubexpMainProgram SubexpSetupProgram SubexpLayoutSpec
open SubexpPackingParameters SubexpMainScheduledLayout
open SubexpMainInvariant (Stored)
open SubexpLayoutPorts (Allocation)

local instance scheduledPrime (n : ℕ) : Fact (p n).Prime := ⟨p_prime n⟩

variable {cfg : Config} {er n B : ℕ} {hrBoot : 32 ≤ workRegs er} {hregs : 16 ≤ er}
variable {F : SubexpOrderedRawPrefix.Formula n} {alloc : Allocation (mainExtraStacks cfg)}
variable {a : MainState er (mainExtraStacks cfg)}
variable (boot : SubexpOrderedRawBoot.Run cfg hrBoot F) (initial : Stored cfg boot.setupOutput B a)
variable (ready : DyadicSchedule.Ready cfg.k cfg.T n)
variable {G : SubexpLeafData.Leaf n}
variable (input : SubexpMainLayoutInput.Ready alloc a n cfg.k cfg.T G)
variable [NeZero (r n)]
variable (actual : Run alloc hregs a G input ready)

local notation "dim" => SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)

variable (target : SubexpSelectedConversions.Prepared (p n)
  (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)))
variable (node : Fin ((p n)^4 - 1))
variable (sourceWidth : List Bool) (hw : sourceWidth.length = SubexpLiftRing.baseWidth (p n) 1)
variable (cache : List (List (SubexpFactorPacketProvenance.Code (p n)
  (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)))))

noncomputable def packet (e : Fin (scopes input).length) :
    SubexpFactorPacketProvenance.Input (p n) dim (p n) ((scopes input).get e).length
      (DyadicSchedule.R cfg.k cfg.T n) :=
  SubexpNodePacketSemantics.input
    (DyadicSchedule.parameters cfg.k cfg.T cfg.width_ge_two n (DyadicSchedule.ready_goodInput ready))
    actual.result target node sourceWidth hw cache e

theorem row (e : Fin (scopes input).length) (i : Fin ((scopes input).get e).length) (w : Fin dim) :
    (((packet ready input actual target node sourceWidth hw cache e).sourceRows i w).map
      (SubexpRowSourceSemantics.denote actual.result.rows.cacheFacts.source)).eval =
      (SubexpOrderedRawScheduledReconstruction.systemLayout boot initial ready input actual).row e
        (SubexpOrderedRawScheduledRouting.scopeIndex input e i) w :=
  SubexpNodePacketSemantics.physical_input_row
    (SubexpMainLayoutInput.castLeaf input.variableCount.symm G)
    input.sparse.clause_sets_nodup input.ell_pos input.capacity input.dimension
    (DyadicSchedule.parameters cfg.k cfg.T cfg.width_ge_two n (DyadicSchedule.ready_goodInput ready))
    actual.result rfl
    (SubexpMainLayoutPattern.bounded alloc a G input (by have := cfg.width_ge_two; omega))
    (by rw [SubexpOrderedRawParameterValues.sourceInputs_dimension alloc boot initial]
        exact SubexpMainDyadicReadiness.size cfg.k cfg.T cfg.width_ge_two ready)
    (SubexpMainDyadicReadiness.threshold cfg.k cfg.T cfg.width_ge_two ready)
    (SubexpMainDyadicReadiness.normalized_tail cfg.k cfg.T cfg.width_ge_two ready)
    target node sourceWidth hw cache e i w

include boot initial in
theorem degree (e : Fin (scopes input).length) (i : Fin ((scopes input).get e).length) (w : Fin dim) :
    ((((packet ready input actual target node sourceWidth hw cache e).sourceRows i w).map
      (SubexpRowSourceSemantics.denote actual.result.rows.cacheFacts.source)).eval).natDegree ≤
        DyadicSchedule.R cfg.k cfg.T n :=
  SubexpNodePacketSemantics.physical_input_degree
    (SubexpMainLayoutInput.castLeaf input.variableCount.symm G)
    input.sparse.clause_sets_nodup input.ell_pos input.capacity input.dimension
    (DyadicSchedule.parameters cfg.k cfg.T cfg.width_ge_two n (DyadicSchedule.ready_goodInput ready))
    actual.result rfl
    (SubexpMainLayoutPattern.bounded alloc a G input (by have := cfg.width_ge_two; omega))
    (by rw [SubexpOrderedRawParameterValues.sourceInputs_dimension alloc boot initial]
        exact SubexpMainDyadicReadiness.size cfg.k cfg.T cfg.width_ge_two ready)
    (SubexpMainDyadicReadiness.threshold cfg.k cfg.T cfg.width_ge_two ready)
    (SubexpMainDyadicReadiness.normalized_tail cfg.k cfg.T cfg.width_ge_two ready)
    target node sourceWidth hw cache e i w

theorem origin (e : Fin (scopes input).length) (i : Fin ((scopes input).get e).length) (w : Fin dim) :
    actual.result.rows.cacheFacts.source.residueRing.decode
      ((packet ready input actual target node sourceWidth hw cache e).origins i w) =
      ((SubexpOrderedRawScheduledReconstruction.systemLayout boot initial ready input actual).row e
        (SubexpOrderedRawScheduledRouting.scopeIndex input e i) w).eval
        ((SubexpOrderedRawScheduledReconstruction.systemLayout boot initial ready input actual).node node) :=
  SubexpNodePacketSemantics.physical_input_origin
    (SubexpMainLayoutInput.castLeaf input.variableCount.symm G)
    input.sparse.clause_sets_nodup input.ell_pos input.capacity input.dimension
    (DyadicSchedule.parameters cfg.k cfg.T cfg.width_ge_two n (DyadicSchedule.ready_goodInput ready))
    actual.result rfl
    (SubexpMainLayoutPattern.bounded alloc a G input (by have := cfg.width_ge_two; omega))
    (by rw [SubexpOrderedRawParameterValues.sourceInputs_dimension alloc boot initial]
        exact SubexpMainDyadicReadiness.size cfg.k cfg.T cfg.width_ge_two ready)
    (SubexpMainDyadicReadiness.threshold cfg.k cfg.T cfg.width_ge_two ready)
    (SubexpMainDyadicReadiness.normalized_tail cfg.k cfg.T cfg.width_ge_two ready)
    target node sourceWidth hw cache e i w

theorem table (e : Fin (scopes input).length) :
    SubexpTableInterpolation.tablePolynomial
      (SubexpLagrangeCacheAlgebra.integerNodes (p n) (dim + 1))
      (SubexpLagrangeCacheAlgebra.integerNodes_units (p n) (dim + 1))
      (((packet ready input actual target node sourceWidth hw cache e).rows).map
        (SubexpRepresentedBuilder.mapRow (SubexpFactorPacketProvenance.decode (p n) dim))) =
      MvPolynomial.rename (SubexpOrderedRawScheduledRouting.scopeIndex input e).symm
        (GlobalPolynomial.interpolatedTable (SubexpOrderedRawScheduledReconstruction.system input)
          (SubexpActualRing.coordinateLift (p n) (dim + 1))
          (SubexpActualRing.coordinateLift_unitDifferences (p n) (dim + 1)) e) := by
  have hp : BinaryArithmetic.toNat
      (SubexpMainLayout.Factors.sourceInputs alloc a).counts.modulus = p n := by
    rw [SubexpMainParameterValues.sourceInputs_modulus_word]
    simpa only [CounterPrograms.value_eq_toNat] using input.prime
  exact SubexpNodePacketSemantics.produced_input_table target actual.result.rows.cacheFacts.source
    (SubexpMainMomentReadback.nodeCode (p n) dim node) (DyadicSchedule.R cfg.k cfg.T n)
    sourceWidth hw cache
    (SubexpNodePacketSemantics.expression
      (DyadicSchedule.parameters cfg.k cfg.T cfg.width_ge_two n (DyadicSchedule.ready_goodInput ready))
      actual.result)
    (SubexpMainLayout.Factors.sourceInputs alloc a) (family input)
    (SubexpMainLayoutInput.castLeaf input.variableCount.symm G)
    input.sparse.clause_sets_nodup input.ell_pos input.dimension rfl hp input.capacity e

#print axioms packet

end SubexponentialSAT.SubexpOrderedRawScheduledPackets


end OAI.Algorithms
