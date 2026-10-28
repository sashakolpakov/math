import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainNodeProvenance
import OAI.Algorithms.SubexponentialSAT.SubexpMainScheduledPackets
import OAI.Algorithms.SubexponentialSAT.SubexpNodeReferenceTransport
import OAI.Algorithms.SubexponentialSAT.SubexpMainCanonicalJetReadback

namespace OAI.Algorithms

/-! The actual Main source family produces the canonical jet bytes of the
same physical factor system used by reconstruction. All packet, table,
node, and enumeration identifications are derived from the scheduled run. -/

namespace SubexponentialSAT.SubexpMainScheduledJet

noncomputable section

set_option quotPrecheck false

open SubexpMainProgram SubexpSetupProgram SubexpLayoutSpec
open SubexpPackingParameters SubexpMainScheduledLayout SubexpSymbolicCost
open SubexpMainInvariant (Stored)
open SubexpLayoutPorts (Allocation)

local instance scheduledPrime (n : ℕ) : Fact (p n).Prime := ⟨p_prime n⟩

variable {cfg : Config} {er n B : ℕ} {hrBoot : 32 ≤ workRegs er} {hregs : 16 ≤ er}
variable {F : SAT.CNF (Fin n)} {alloc : Allocation (mainExtraStacks cfg)}
variable {a : MainState er (mainExtraStacks cfg)}
variable (boot : SubexpMainBoot.Run cfg hrBoot F) (initial : Stored cfg boot.setupOutput B a)
variable (ready : DyadicSchedule.Ready cfg.k cfg.T n)
variable {G : SubexpLeafData.Leaf n}
variable (input : SubexpMainLayoutInput.Ready alloc a n cfg.k cfg.T G)
variable [NeZero (r n)]
variable (actual : Run alloc hregs a G input ready)
variable {initialized : MainState er (mainExtraStacks cfg)}
variable (hi : SubexpMainNodeInitialization.Result alloc
  (SubexpMainNodeSetup.prepared alloc actual.out) initialized
  (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)))
variable (node : Fin ((p n)^4 - 1))

local notation "dim" => SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)
local notation "Masters" => SubexpMainMomentData.store alloc initialized
local notation "Target" => SubexpMainMomentData.target (p n) dim
local notation "Source" => SubexpMainNodeArguments.source actual.result
local notation "Theta" => SubexpMainNodeArguments.theta (D := dim) node
local notation "Cache" => SubexpMainNodeArguments.cache actual.result
local notation "HM" => SubexpMainMomentData.context_masters actual.result hi
local notation "Ctx" => SubexpNodeContexts.sourceContext Masters dim []
local notation "Packet" => SubexpMainScheduledPackets.packet ready input actual Target node
  (Masters 129) (HM).sourceWidth Cache
local notation "Order" => List.finRange (scopes input).length
local notation "Words" => SubexpMainMomentRouting.factorWords actual.result
local notation "Physical" => SubexpMainScheduledReconstruction.systemLayout boot initial ready input actual
local notation "Enum" => SubexpMainScheduledEnumeration.physical boot initial ready input actual node
local notation "C" => DyadicSchedule.parameters cfg.k cfg.T cfg.width_ge_two n
  (DyadicSchedule.ready_goodInput ready)

/-- The native reference returned with the executed source family. -/
def reference (z : Fin dim → ℕ) :=
  SubexpMainNodeProvenance.reference C rfl actual.result hi
    (SubexpMainLayoutPattern.bounded alloc a G input (by have := cfg.width_ge_two; omega))
    (by rw [SubexpMainParameterValues.sourceInputs_dimension alloc boot initial]
        exact SubexpMainDyadicReadiness.size cfg.k cfg.T cfg.width_ge_two ready)
    (SubexpMainDyadicReadiness.threshold cfg.k cfg.T cfg.width_ge_two ready)
    (SubexpMainDyadicReadiness.normalized_tail cfg.k cfg.T cfg.width_ge_two ready) node z

/-- The proved pattern transport preserves the complete ordered reference. -/
theorem reference_eq (z : Fin dim → ℕ) :
    reference boot initial ready input actual hi node z =
      SubexpConcreteSourceProvenance.reference (ctx := Ctx)
        Physical node Enum Source Theta Packet Order Words Cache z := by
  symm
  exact congrFun (SubexpNodeReferenceTransport.reference_eq Ctx
    (SubexpMainPhysicalSystem.system_toPattern
      (SubexpMainLayoutInput.castLeaf input.variableCount.symm G)
      input.sparse.clause_sets_nodup input.ell_pos input.capacity input.dimension).symm
    (actual.layout boot initial ready input) node
    (SubexpMainScheduledEnumeration.numeric boot initial ready input actual node)
    Source Theta Packet Order Words Cache) z

/-- Actual canonical arithmetic makes the output bytes depend only on the
scheduled physical layout and node, independently of caller registers or
the existential source family returned by the worker. -/
theorem jet_eq_canonical
    (family : SubexpNodeJetSemantics.Family (p n) dim)
    (hrel : letI : One (QuarticCode (p n) dim) := ⟨(Target).one⟩
      ∀ z : Fin dim → ℕ,
        List.Forall₂ (SubexpSourceReference.BlockRel
          (SubexpFactorPacketProvenance.decode (p n) dim))
          (family z) (reference boot initial ready input actual hi node z)) :
    letI : One (QuarticCode (p n) dim) := ⟨(Target).one⟩
    letI : One (QuarticCode (p n) (Ctx).dimension) := ⟨(Target).one⟩
    SubexpNodePhaseExecution.jet (p n) dim (Target).modulus (Target).reduction
      (Target).zero (Target).one (SubexpQueryOrder.visitSlots dim)
      (SubexpNodeSourceJobs.expression (p n) Ctx family)
      (SubexpQueryOrder.generatedQueries dim) =
      SubexpNodeCanonicalJet.canonicalJetBytes Physical
        (SubexpMainCanonicalJetReadback.table
          (SubexpMainScheduledReconstruction.system input)) node := by
  let _ : One (QuarticCode (p n) dim) := ⟨(Target).one⟩
  let _ : One (QuarticCode (p n) (Ctx).dimension) := ⟨(Target).one⟩
  apply SubexpNodeCanonicalJet.jet_eq_canonicalJetBytes (ctx := Ctx)
    Target family Physical node Enum Source Theta Packet Order Words Cache
    (List.nodup_finRange _) (fun e => List.mem_finRange e)
    (SubexpMainScheduledRouting.scopeIndex input)
    (SubexpMainCanonicalJetReadback.table
      (SubexpMainScheduledReconstruction.system input))
  · intro e
    exact congrFun (congrFun
      (SubexpMainScheduledRouting.factorWords_eq boot initial ready input actual) e) node
  · exact SubexpMainScheduledPackets.table ready input actual Target node
      (Masters 129) (HM).sourceWidth Cache
  · exact SubexpMainScheduledPackets.origin boot initial ready input actual Target node
      (Masters 129) (HM).sourceWidth Cache
  · exact SubexpMainScheduledPackets.row boot initial ready input actual Target node
      (Masters 129) (HM).sourceWidth Cache
  · change SubexpFactorPacketProvenance.decode (p n) dim Theta =
      SubexpActualRing.sectionValue (p n) (dim+1) (Nat.succ_pos dim) ((Physical).node node)
    simp only [SubexpMainScheduledReconstruction.systemLayout,
      SubexpMainPhysicalLayoutFields.node]
    exact SubexpMainMomentReadback.nodeCode_decode (p n) dim node
  · exact SubexpMainNodeProvenance.cache_basis C actual.result
  · intro z
    rw [← reference_eq boot initial ready input actual hi node z]
    exact hrel z

end
end SubexponentialSAT.SubexpMainScheduledJet

end OAI.Algorithms
