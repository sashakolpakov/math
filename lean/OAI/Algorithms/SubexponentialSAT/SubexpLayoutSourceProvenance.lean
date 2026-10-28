import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedSourceProvenance
import OAI.Algorithms.SubexponentialSAT.Subexp.RawTemplateSupports

namespace OAI.Algorithms

/-! The ordered raw-template interpretation supplies the exact provenance
family consumed by the node job program. Support identities concern local
layout metadata; the computed-layout module proves them for its selectors. -/

namespace SubexponentialSAT.SubexpLayoutSourceProvenance

noncomputable section

open SubexpMomentSourceProgram SubexpMomentSourceSemantics
open SubexpTemplateSourceData SubexpProducedSourceRefinement
open SubexpQuarticRing SubexpLiftRing SubexpSymbolicCost
open SubexpLayoutSpec MulticolorTypes Subexp.ConstructivePacking

variable {p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime] {ctx : Context}
  (coefficients : Fin 4 → ZMod (p ^ (ctx.dimension + 1)))
  [One (QuarticCode p ctx.dimension)]
  (hwidth : ctx.width.length = baseWidth p 1)
  (templateCtx : TemplateContext)
  (source : SubexpSelectedConversions.Prepared p 0)
  (target : SubexpSelectedConversions.Prepared p ctx.dimension)
  (minusOne : SubexpQuarticRing.Word (baseWidth p (ctx.dimension + 1)))
  {F K : Type*} [Fintype F] [Field K] [Algebra (ZMod p) K]
  {pattern : Factor.Pattern (Fin ctx.dimension) F}
  {params : Parameters p k Δ r tau}
  (L : Layout (E := K) pattern params) (node : Fin params.Q)
  (packing : PackingData (Fin ctx.dimension) (UniversalType r params.Q Δ))
  (enum : EnumerationData L node)
  (es : List F) (words : F → MulticolorTypes.Word r params.Q)
  (packets : F → SubexpTemplateFactors.Factor p ctx.dimension)

local notation "R" => LiftRing.Extension (QuarticSearch.poly coefficients)

def inputs : List (BlockData ctx) :=
  blocksData ctx hwidth templateCtx source target minusOne
    (Subexp.RawTemplateRefinement.blocksOfEnumeration L node packing enum es words packets)
    (Subexp.RawTemplateRefinement.blocksOfEnumeration_good L node packing enum es words packets)

omit [One (QuarticCode p ctx.dimension)] in
theorem input_templates :
    (inputs hwidth templateCtx source target minusOne L node packing enum es words packets).map
        BlockData.template =
      (Subexp.RawTemplateRefinement.blocksOfEnumeration L node packing enum es words packets).map
        (SubexpTemplateData.preparedBlock templateCtx source target minusOne) :=
  blocksData_templates ctx hwidth templateCtx source target minusOne _ _

variable (lift : K → LiftRing.Extension (QuarticSearch.poly coefficients))
  (cache : List (List (LiftRing.Extension (QuarticSearch.poly coefficients))))
  (data : F → SubexpProgramBuilder.FactorData ctx.dimension p params.R r K
    (LiftRing.Extension (QuarticSearch.poly coefficients)))

def reference (a : Fin ctx.dimension → ℕ) :=
  SubexpSourceReference.blocks (D := ctx.dimension) (p := p) (q := params.R) (r := r)
    (F := ZMod p) (K := K) («R» := R) (algebraMap (ZMod p) K) lift
    (fun z : ZMod p => (z.val : R)) cache (es.map data)
    (SubexpEnumerationCode.supportLists L node) (SubexpEnumerationCode.outsideList L node)
    (SubexpEnumerationCode.outerBases enum) (SubexpEnumerationCode.innerIncrements enum) a

local instance (bits : List Bool) : One (QuarticCode p (ctx.withExponent bits).dimension) :=
  inferInstanceAs (One (QuarticCode p ctx.dimension))

/-- Every exponent uses the same physical template and the same ordered
factor provenance. No complete expression or jet equality is assumed. -/
theorem provenance
    (hsupport : Subexp.RawTemplateRefinement.colorSupport packing node =
      SubexpEnumerationCode.supportLists L node)
    (houtside : Subexp.RawTemplateRefinement.outsideSupport packing =
      SubexpEnumerationCode.outsideList L node)
    (hf : SubexpOrderedSourceProvenance.FactorWitnesses coefficients templateCtx source target
      minusOne packing node es words packets (algebraMap (ZMod p) K) lift cache (es.map data)
      (SubexpEnumerationCode.outerBases enum) (SubexpEnumerationCode.innerIncrements enum))
    (a : Fin ctx.dimension → ℕ) :
    List.Forall₂
      (BlockProvenance (ctx := ctx.withExponent (SubexpExponentController.momentWord a))
        coefficients a)
      ((inputs hwidth templateCtx source target minusOne L node packing enum es words packets).map
        (fun b => b.withExponent (SubexpExponentController.momentWord a)))
      (reference coefficients L node enum es lift cache data a) := by
  apply SubexpTemplateSourceFamily.blocks_withExponent
  have h := SubexpOrderedSourceProvenance.blocks_provenance coefficients hwidth templateCtx
    source target minusOne packing node es words packets (algebraMap (ZMod p) K) lift cache
    (es.map data) (SubexpEnumerationCode.outerBases enum)
    (SubexpEnumerationCode.innerIncrements enum) hf a
  simpa only [inputs, Subexp.RawTemplateSupports.blocksOfEnumeration_eq,
    reference, hsupport, houtside] using h

end

end SubexponentialSAT.SubexpLayoutSourceProvenance

end OAI.Algorithms
