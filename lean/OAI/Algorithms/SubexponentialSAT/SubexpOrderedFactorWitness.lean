import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedSourceProvenance
import OAI.Algorithms.SubexponentialSAT.SubexpTemplateFactorWitness

namespace OAI.Algorithms

/-! The actual assigned color filters the original factor indices before
the local packet witnesses are assembled. No quotient by packet equality or
reordering of duplicate factor occurrences is used. -/

namespace SubexponentialSAT.SubexpOrderedFactorWitness

noncomputable section

open SubexpLiftRing SubexpQuarticRing SubexpSymbolicCost
open SubexpSelectedConversions SubexpTemplateSourceData

variable {p q r Q Δ : ℕ} [Fact p.Prime] {ctx : SourceContext}
variable {F : Type*} {arity : F → ℕ}
variable (source : Prepared p 0) (target : Prepared p ctx.dimension)
variable (theta : SubexpFactorPacketProvenance.Code p ctx.dimension)
variable (inputs : ∀ e, SubexpFactorPacketProvenance.Input p ctx.dimension p (arity e) q)
variable (es : List F) (words : F → MulticolorTypes.Word r Q)
variable (minusOne : SubexpQuarticRing.Word (baseWidth p (ctx.dimension+1)))
variable (packing : Subexp.ConstructivePacking.PackingData
  (Fin ctx.dimension) (MulticolorTypes.UniversalType r Q Δ)) (node : Fin Q)

local notation "R" => SubexpFactorPacketProvenance.Ring p ctx.dimension

/-- Every visited base/color/increment has the exact factor witness required
by the ordered source proof. Only the original packet data and local cache,
degree, and context facts are supplied. -/
theorem factorWitnesses (templateCtx : TemplateContext)
    (hdimension : templateCtx.dimension = ctx.dimension)
    (hindex : templateCtx.indexWidth = indexBits ctx.dimension)
    (hminusOne : wordValue p (ctx.dimension+1) minusOne = -1)
    (hdegree : ∀ e ∈ es, ∀ i w,
      ((((inputs e).sourceRows i w).map (SubexpRowSourceSemantics.denote source)).eval).natDegree ≤ q)
    (cache : List (List (SubexpFactorPacketProvenance.Code p ctx.dimension)))
    (hshared : ∀ e ∈ es, (inputs e).cache = cache)
    (nodes : Fin p → R) (hu : TableInterpolation.UnitDifferences nodes)
    (hcache : ∀ i : Fin p,
      PolynomialAlgorithm.denote ((cache.map (List.map (SubexpFactorPacketProvenance.decode p ctx.dimension))).getD i.val []) =
        TableInterpolation.basis nodes hu i)
    (bases : List (Fin ctx.dimension → ZMod p))
    (increments : Fin r → List (Fin ctx.dimension → ZMod p)) :
    letI : One (SubexpFactorPacketProvenance.Code p ctx.dimension) := ⟨target.one⟩
    SubexpOrderedSourceProvenance.FactorWitnesses
      (QuarticSearch.liftedCoefficients p (ctx.dimension+1))
      templateCtx source target minusOne packing node es words
      (fun e => SubexpFactorPacketProvenance.blueprintRows source target theta (inputs e))
      (algebraMap (ZMod p) (SubexpActualRing.E p))
      (SubexpActualRing.residueSection p (ctx.dimension+1) (Nat.succ_pos ctx.dimension)).lift
      (cache.map (List.map (SubexpFactorPacketProvenance.decode p ctx.dimension)))
      (es.map (fun e => SubexpFactorPacketProvenance.referenceData
        source theta (inputs e) (words e node))) bases increments := by
  let _ : One (SubexpFactorPacketProvenance.Code p ctx.dimension) := ⟨target.one⟩
  intro base hbase g increment hincrement
  let ids := es.filter (fun e => decide (words e node = g))
  have h := SubexpTemplateFactorWitness.factorWitness source target theta inputs ids
    (fun e => words e node) minusOne
    (Subexp.RawTemplateRefinement.scalarWords base)
    (Subexp.RawTemplateRefinement.scalarWords increment)
    (Subexp.RawTemplateRefinement.colorSupport packing node g)
    templateCtx hdimension hindex hminusOne
    (fun e he => hdegree e (List.mem_filter.mp he).1) cache
    (fun e he => hshared e (List.mem_filter.mp he).1) nodes hu hcache
  let data : F → SubexpProgramBuilder.FactorData ctx.dimension p q r
      (SubexpActualRing.E p)
      (LiftRing.Extension
        (QuarticSearch.poly (QuarticSearch.liftedCoefficients p (ctx.dimension + 1)))) :=
    fun e => SubexpFactorPacketProvenance.referenceData
      source theta (inputs e) (words e node)
  have hdata :
      (es.map data).filter (fun f => decide (f.color = g)) =
        (es.filter (fun e => decide (words e node = g))).map data := by
    rw [List.filter_map]
    rfl
  have href : SubexpOrderedSourceProvenance.referenceFactors
      (QuarticSearch.liftedCoefficients p (ctx.dimension+1))
      (algebraMap (ZMod p) (SubexpActualRing.E p))
      (SubexpActualRing.residueSection p (ctx.dimension+1) (Nat.succ_pos ctx.dimension)).lift
      (cache.map (List.map (SubexpFactorPacketProvenance.decode p ctx.dimension)))
      (es.map (fun e => SubexpFactorPacketProvenance.referenceData
        source theta (inputs e) (words e node))) g base increment =
      ids.map (fun e => SubexpSourceReference.factor
        (SubexpActualRing.residueSection p (ctx.dimension+1) (Nat.succ_pos ctx.dimension)).lift
        (cache.map (List.map (SubexpFactorPacketProvenance.decode p ctx.dimension)))
        (SubexpFactorPacketProvenance.referenceData source theta (inputs e) (words e node))
        (fun w => algebraMap (ZMod p) (SubexpActualRing.E p) (base w + increment w))) := by
    let lift : SubexpActualRing.E p →
        LiftRing.Extension
          (QuarticSearch.poly (QuarticSearch.liftedCoefficients p (ctx.dimension + 1))) :=
      (SubexpActualRing.residueSection p (ctx.dimension + 1)
        (Nat.succ_pos ctx.dimension)).lift
    let decode : SubexpFactorPacketProvenance.Code p ctx.dimension →
        LiftRing.Extension
          (QuarticSearch.poly (QuarticSearch.liftedCoefficients p (ctx.dimension + 1))) :=
      SubexpFactorPacketProvenance.decode p ctx.dimension
    change
      ((es.map data).filter (fun f => decide (f.color = g))).map
          (fun f => SubexpSourceReference.factor lift
            (cache.map (List.map decode)) f
            (fun i => algebraMap (ZMod p) (SubexpActualRing.E p) (base i + increment i))) =
        (es.filter (fun e => decide (words e node = g))).map
          (fun e => SubexpSourceReference.factor lift
            (cache.map (List.map decode))
            (data e)
            (fun i => algebraMap (ZMod p) (SubexpActualRing.E p) (base i + increment i)))
    rw [hdata, List.map_map]
    rfl
  rw [href]
  convert h using 1
  all_goals simp only [SubexpTemplateFactorWitness.term, Subexp.RawTemplateRefinement.term,
    Subexp.RawTemplateRefinement.colorFactors, Subexp.RawTemplateRefinement.scalarWords_value,
    ids]
  all_goals rfl

end

end SubexponentialSAT.SubexpOrderedFactorWitness

end OAI.Algorithms
