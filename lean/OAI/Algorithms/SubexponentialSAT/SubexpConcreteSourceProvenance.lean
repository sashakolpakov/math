import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedFactorWitness
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutSourceProvenance

namespace OAI.Algorithms

/-! Packet-local Taylor and cache correctness supplies the complete input
provenance used by the actual node job producer. The conclusion concerns the
same ordered blocks whose bytes are emitted by the raw-template program. -/

namespace SubexponentialSAT.SubexpConcreteSourceProvenance

noncomputable section

open SubexpMomentSourceProgram SubexpTemplateSourceData
open SubexpQuarticRing SubexpLiftRing SubexpSymbolicCost
open SubexpSelectedConversions SubexpLayoutSpec MulticolorTypes

variable {p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime] {ctx : Context}
  {F : Type*} [Fintype F] {arity : F → ℕ}
  {pattern : Factor.Pattern (Fin ctx.dimension) F}
  {params : Parameters p k Δ r tau}
  (L : Layout (E := SubexpActualRing.E p) pattern params) (node : Fin params.Q)
  (packing : Subexp.ConstructivePacking.PackingData
    (Fin ctx.dimension) (UniversalType r params.Q Δ))
  (enum : EnumerationData L node)
  (source : Prepared p 0) (target : Prepared p ctx.dimension)
  (theta : SubexpFactorPacketProvenance.Code p ctx.dimension)
  (packetInputs : ∀ e, SubexpFactorPacketProvenance.Input p ctx.dimension p (arity e) params.R)
  (es : List F) (words : F → MulticolorTypes.Word r params.Q)
  (minusOne : SubexpQuarticRing.Word (baseWidth p (ctx.dimension + 1)))
  (templateCtx : TemplateContext)
  (hwidth : ctx.width.length = baseWidth p 1)

local notation "coefficients" => QuarticSearch.liftedCoefficients p (ctx.dimension + 1)
local notation "R" => SubexpFactorPacketProvenance.Ring p ctx.dimension

def inputs : List (BlockData ctx) :=
  SubexpLayoutSourceProvenance.inputs hwidth templateCtx source target minusOne
    L node packing enum es words
    (fun e => SubexpFactorPacketProvenance.blueprintRows source target theta (packetInputs e))

def reference (cache : List (List (SubexpFactorPacketProvenance.Code p ctx.dimension)))
    (a : Fin ctx.dimension → ℕ) :=
  SubexpLayoutSourceProvenance.reference coefficients L node enum es
    (SubexpActualRing.residueSection p (ctx.dimension + 1) (Nat.succ_pos ctx.dimension)).lift
    (cache.map (List.map (SubexpFactorPacketProvenance.decode p ctx.dimension)))
    (fun e => SubexpFactorPacketProvenance.referenceData source theta (packetInputs e) (words e node)) a

local instance (bits : List Bool) [One (QuarticCode p ctx.dimension)] :
    One (QuarticCode p (ctx.withExponent bits).dimension) :=
  inferInstanceAs (One (QuarticCode p ctx.dimension))

/-- All weight, factor, group, and block relations are derived from the
executed point arithmetic and local row/cache facts. No source-expression,
complete block-value, or jet equality is a premise. -/
theorem provenance
    (hdimension : templateCtx.dimension = ctx.dimension)
    (hindex : templateCtx.indexWidth = indexBits ctx.dimension)
    (hsupport : Subexp.RawTemplateRefinement.colorSupport packing node =
      SubexpEnumerationCode.supportLists L node)
    (houtside : Subexp.RawTemplateRefinement.outsideSupport packing =
      SubexpEnumerationCode.outsideList L node)
    (hminusOne : wordValue p (ctx.dimension + 1) minusOne = -1)
    (hdegree : ∀ e ∈ es, ∀ i w,
      ((((packetInputs e).sourceRows i w).map (SubexpRowSourceSemantics.denote source)).eval).natDegree ≤ params.R)
    (cache : List (List (SubexpFactorPacketProvenance.Code p ctx.dimension)))
    (hshared : ∀ e ∈ es, (packetInputs e).cache = cache)
    (nodes : Fin p → R) (hu : TableInterpolation.UnitDifferences nodes)
    (hcache : ∀ i : Fin p,
      PolynomialAlgorithm.denote
        ((cache.map (List.map (SubexpFactorPacketProvenance.decode p ctx.dimension))).getD i.val []) =
        TableInterpolation.basis nodes hu i) :
    letI : One (QuarticCode p ctx.dimension) := ⟨target.one⟩
    ∀ a : Fin ctx.dimension → ℕ,
      List.Forall₂
        (SubexpProducedSourceRefinement.BlockProvenance
          (ctx := ctx.withExponent (SubexpExponentController.momentWord a)) coefficients a)
        ((inputs L node packing enum source target theta packetInputs es words minusOne templateCtx hwidth).map
          (fun b => b.withExponent (SubexpExponentController.momentWord a)))
        (reference L node enum source theta packetInputs es words cache a) := by
  let : One (QuarticCode p ctx.dimension) := ⟨target.one⟩
  intro a
  apply SubexpLayoutSourceProvenance.provenance coefficients hwidth templateCtx source target
    minusOne L node packing enum es words
    (fun e => SubexpFactorPacketProvenance.blueprintRows source target theta (packetInputs e))
    (SubexpActualRing.residueSection p (ctx.dimension + 1) (Nat.succ_pos ctx.dimension)).lift
    (cache.map (List.map (SubexpFactorPacketProvenance.decode p ctx.dimension)))
    (fun e => SubexpFactorPacketProvenance.referenceData source theta (packetInputs e) (words e node))
    hsupport houtside
  exact SubexpOrderedFactorWitness.factorWitnesses source target theta packetInputs es words
    minusOne packing node templateCtx hdimension hindex hminusOne hdegree cache hshared nodes hu hcache
    (SubexpEnumerationCode.outerBases enum) (SubexpEnumerationCode.innerIncrements enum)

end

end SubexponentialSAT.SubexpConcreteSourceProvenance

end OAI.Algorithms
