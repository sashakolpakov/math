import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawScheduledRouting

namespace OAI.Algorithms

/-! The generated row coefficients describe the same physical layout used
by reconstruction, at the same vertex and in the emitted scope order. -/

namespace SubexponentialSAT.SubexpOrderedRawScheduledRows

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

omit [NeZero (r n)] in
theorem scopeIndex_mem (e : Fin (scopes input).length)
    (i : Fin ((scopes input).get e).length) :
    ((SubexpOrderedRawScheduledRouting.scopeIndex input e i).val).val ∈ (scopes input).get e := by
  rw [SubexpOrderedRawScheduledRouting.scopeIndex_value input e i]
  exact List.get_mem _ _

theorem row_coefficients_denote {N : ℕ} (target : SubexpSelectedConversions.Prepared (p n) N)
    (e : Fin (scopes input).length)
    (v : Fin (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)))
    (hv : v.val ∈ (scopes input).get e)
    (hphysical : v ∈ (SubexpOrderedRawScheduledReconstruction.system input).scope e)
    (w : Fin (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a))) :
    PolynomialAlgorithm.denote
      ((SubexpDenseRowSemantics.rowCoefficients actual.result.rows.cacheFacts.source
        (List.ofFn actual.result.choices.coefficients) actual.result.rows.cacheFacts.inverse
        actual.result.rows.cacheFacts.negative actual.result.rows.cacheFacts.difference
        actual.result.choices.packing.packing (scopes input) actual.degree (N + 1) e v hv w).map
          target.ring.decode) =
      SubexpExplicitLift.liftPolynomial
        (SubexpActualRing.sectionValue (p n) (N + 1) (Nat.succ_pos N))
        (DyadicSchedule.R cfg.k cfg.T n)
        ((SubexpOrderedRawScheduledReconstruction.systemLayout boot initial ready input actual).row e
          ⟨v, hphysical⟩ w) := by
  have hrow := SubexpMainPhysicalLayoutRows.row_at
    (SubexpMainLayoutInput.castLeaf input.variableCount.symm G)
    input.sparse.clause_sets_nodup input.ell_pos input.capacity input.dimension
    (SubexpOrderedRawScheduledLayout.runLayout boot initial ready input actual) e v w
    ((Subexp.IncidencePlanSpec.mem_pattern_scope _ _ v e).mpr hv) hphysical
  change PolynomialAlgorithm.denote _ =
    SubexpExplicitLift.liftPolynomial _ _
      ((SubexpMainPhysicalSystem.layout _ _ _ _ _ (SubexpOrderedRawScheduledLayout.runLayout boot initial ready input actual)).row
        e ⟨v, hphysical⟩ w)
  rw [hrow]
  exact SubexpMainLayoutSemantics.row_coefficients_denote
    (DyadicSchedule.parameters cfg.k cfg.T cfg.width_ge_two n (DyadicSchedule.ready_goodInput ready))
    rfl actual.result
    (SubexpMainLayoutPattern.bounded alloc a G input (by have := cfg.width_ge_two; omega))
    (by rw [SubexpOrderedRawParameterValues.sourceInputs_dimension alloc boot initial]
        exact SubexpMainDyadicReadiness.size cfg.k cfg.T cfg.width_ge_two ready)
    (SubexpMainDyadicReadiness.threshold cfg.k cfg.T cfg.width_ge_two ready)
    (SubexpMainDyadicReadiness.normalized_tail cfg.k cfg.T cfg.width_ge_two ready)
    target e v hv w

end SubexponentialSAT.SubexpOrderedRawScheduledRows

end OAI.Algorithms
