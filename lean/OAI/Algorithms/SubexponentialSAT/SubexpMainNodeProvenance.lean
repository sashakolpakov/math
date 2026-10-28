import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainNodeArguments
import OAI.Algorithms.SubexponentialSAT.SubexpNodeWorkerProvenance
import OAI.Algorithms.SubexponentialSAT.SubexpNodePacketSemantics

namespace OAI.Algorithms

/-! Source provenance for the actual Main node arguments. The cache basis
comes from its executed cache producer, the source degrees from its generated
rows, and support lists from the same constructed layout. -/

namespace SubexponentialSAT.SubexpMainNodeProvenance

noncomputable section

open SubexpMainProgram Subexp SubexpLayoutSpec MulticolorTypes
open SubexpLiftRing SubexpSelectedConversions SubexpSymbolicCost
open SubexpNodeWorkspace SubexpNodeContexts SubexpMomentSourceProgram
open SubexpLayoutPorts (Allocation)
open SubexpMainMomentData (store target)

variable {p k Δ r : ℕ} {tau : ℚ} {er es D : ℕ} [Fact p.Prime] [NeZero r]
  {alloc : Allocation es} {a middle layoutOut initialized : MainState er es}
  {hregs : 16 ≤ er} {hr : 0 < r} {hQ : 0 < p^4-1}
  {scopes : List (List ℕ)}
  {hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ}
  {tables : List (List Bool)}
  (c : Parameters p k Δ r tau) (h4 : c.h = 4)
  (h : SubexpMainLayoutExecution.Result hregs alloc a middle layoutOut
    p r Δ c.R D hr hQ scopes hd tables)
  (hi : SubexpMainNodeInitialization.Result alloc
    (SubexpMainNodeSetup.prepared alloc layoutOut) initialized D)
  (hP : (IncidencePlanSpec.pattern D scopes).Bounded k Δ)
  (hsize : c.Dstar ≤ D)
  (hthreshold : (Fintype.card (UniversalType r (p^4-1) Δ) : ℚ)^3 *
    (1 + (Δ*k : ℕ)) ≤ tau^2*c.Dstar)
  (htail : SpectralRank.normalizedTail r (p^4-1-1)
    (TailInterval.intervalStart r (p^4-1) c.R) c.R ≤ tau/(Δ : ℚ))
  (node : Fin (p^4-1))

local notation "L" => SubexpMainLayoutSemantics.layout c h4 h hP hsize hthreshold htail
local notation "Enum" => SubexpMainLayoutEnumeration.enumeration c h4 h hP hsize hthreshold htail node
local notation "Masters" => store alloc initialized
local notation "Source" => SubexpMainNodeArguments.source h
local notation "Target" => target p D
local notation "MinusOne" => SubexpPreparedQuarticSetup.minusOne p (D+1)
local notation "HM" => SubexpMainMomentData.context_masters h hi
local notation "Theta" => SubexpMainNodeArguments.theta (D := D) node
local notation "Cache" => SubexpMainNodeArguments.cache h
local notation "Expr" => SubexpMainNodeArguments.rowExpr h
local notation "Packing" => h.choices.packing.packing
local notation "Words" => SubexpMainMomentRouting.factorWords h
local notation "Factor" => SubexpMainNodeArguments.factor h hi node
local notation "Order" => List.finRange scopes.length
local notation "Packet" => SubexpNodePacketRaw.packet Source Target Theta Factor
local notation "Bases" => SubexpEnumerationCode.outerBases Enum
local notation "Increments" => SubexpEnumerationCode.innerIncrements Enum
local notation "Blocks" => RawTemplateRefinement.blocks Packing node Order Words Packet Bases Increments
local notation "BlocksGood" => RawTemplateRefinement.blocks_good Packing node Order Words Packet Bases Increments
local notation "TC" => templateContext Masters D
local notation "TemplateBytes" => SubexpTemplateExecution.output TC Source Target MinusOne Blocks
local notation "Ctx" => sourceContext Masters D TemplateBytes
local notation "Inputs" => SubexpNodeTemplateMoment.inputs Masters Source Target MinusOne HM Blocks BlocksGood
local notation "Coefficients" => QuarticSearch.liftedCoefficients p (D+1)

theorem cache_basis (i : Fin p) :
    PolynomialAlgorithm.denote
      (((Cache).map (List.map (SubexpFactorPacketProvenance.decode p D))).getD i.val []) =
      TableInterpolation.basis (SubexpLagrangeCacheAlgebra.integerNodes p (D+1))
        (SubexpLagrangeCacheAlgebra.integerNodes_units p (D+1)) i := by
  have hlen : i.val < (Cache).length := by
    rw [SubexpMainNodeArguments.cache_length h]
    exact i.isLt
  have hrow := h.rows.lagrangeCorrect.get hlen
    (show i.val < (List.range p).length by simp)
  have hp := hrow.2
  simp only [List.get_eq_getElem, List.getElem_range,
    SubexpLagrangeCacheRowCorrectness.basisAt, dite_eq_left i.isLt,
    SubexpLagrangeCacheRowCorrectness.basis] at hp
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hlen), List.getElem_map]
  exact hp

local notation "c4" => SubexpMainLayoutSemantics.parameters c h4
local notation "P" => IncidencePlanSpec.pattern D scopes
local notation "Slots" => IncidencePlanSpec.slots D Δ scopes hd
local notation "Vertices" => OrderedComputedSource.finOrder D
local notation "Types" => PackingCanonicalSpec.types hr hQ Δ
local notation "Indices" => OrderedComputedSource.seedOrder D scopes.length Δ
local notation "Nodes" => SubexpNumericRowSemantics.nodes c4 rfl
local notation "Degree" => ComputedMachineSource.extension_degree c4 rfl
local notation "Start" => TailInterval.intervalStart r (p^4-1) c.R

theorem support_eq : RawTemplateRefinement.colorSupport Packing node =
    SubexpEnumerationCode.supportLists L node := by
  rw [SubexpMainLayoutSemantics.packing_eq c h]
  funext g
  exact RawTemplateSupports.colorSupport_eq P c4 hP (ComputedSource.fin_size hsize)
    hthreshold Degree Nodes Slots Vertices Types Indices h.choices.first h.choices.tail
    h.choices.nodup h.choices.complete Start htail node g

theorem outside_eq : RawTemplateRefinement.outsideSupport Packing =
    SubexpEnumerationCode.outsideList L node := by
  rw [SubexpMainLayoutSemantics.packing_eq c h]
  exact RawTemplateSupports.outsideSupport_eq P c4 hP (ComputedSource.fin_size hsize)
    hthreshold Degree Nodes Slots Vertices Types Indices h.choices.first h.choices.tail
    h.choices.nodup h.choices.complete Start htail node

include h4 hP hsize hthreshold htail in
theorem degree (hvalid : ∀ scope ∈ scopes, ∀ v ∈ scope, v < D)
    (e : Fin scopes.length) (i : Fin (scopes.get e).length) (w : Fin D) :
    (((Expr e.val ((scopes.get e).get i) w.val).map
      (SubexpRowSourceSemantics.denote Source)).eval).natDegree ≤ c.R := by
  let v : Fin D := ⟨(scopes.get e).get i,
    hvalid _ (List.get_mem scopes e) _ (List.get_mem _ i)⟩
  have hv : v.val ∈ scopes.get e := List.get_mem _ i
  let incidence : {v // v ∈ (P).scope e} :=
    ⟨v, (IncidencePlanSpec.mem_pattern_scope D scopes v e).mpr hv⟩
  have he : ((Expr e.val ((scopes.get e).get i) w.val).map
      (SubexpRowSourceSemantics.denote Source)).eval = (L).row e incidence w :=
    SubexpMainLayoutSemantics.expression_denote c h4 h hP hsize hthreshold htail e v hv w
  rw [he]
  exact (L).row_degree e incidence w

def reference (z : Fin D → ℕ) :=
  SubexpNodeWorkerProvenance.reference Masters Source Target MinusOne HM Theta Cache Expr
    scopes tables L node Enum Packing Words z

theorem provenance (hvalid : ∀ scope ∈ scopes, ∀ v ∈ scope, v < D) :
    letI : One (QuarticCode p D) := ⟨(Target).one⟩
    letI : One (QuarticCode p (Ctx).dimension) := ⟨(Target).one⟩
    ∀ z : Fin D → ℕ,
      letI : One (QuarticCode p ((Ctx).withExponent (SubexpExponentController.momentWord z)).dimension) :=
        ⟨(Target).one⟩
      List.Forall₂
        (SubexpProducedSourceRefinement.BlockProvenance
          (ctx := (Ctx).withExponent (SubexpExponentController.momentWord z)) Coefficients z)
        ((Inputs).map (fun b => b.withExponent (SubexpExponentController.momentWord z)))
        (reference c h4 h hi hP hsize hthreshold htail node z) := by
  exact SubexpNodeWorkerProvenance.provenance Masters Source Target MinusOne HM Theta Cache Expr
    scopes tables L node Enum Packing Words
    (support_eq c h4 h hP hsize hthreshold htail node)
    (outside_eq c h4 h hP hsize hthreshold htail node)
    (SubexpPreparedQuarticSetup.minusOne_value p (D+1))
    (degree c h4 h hP hsize hthreshold htail hvalid)
    (cache_basis c h)

end

end SubexponentialSAT.SubexpMainNodeProvenance

end OAI.Algorithms
