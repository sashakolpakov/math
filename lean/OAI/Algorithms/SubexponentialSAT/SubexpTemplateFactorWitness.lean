import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTemplateSourceProvenance
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPacketProvenance

namespace OAI.Algorithms

/-! Local witnesses for factor lists in an actual prepared template. The
original factor indices remain in the list, including repeated occurrences.
No prepared-factor equality or final factor-value equality is an input. -/

namespace SubexponentialSAT.SubexpTemplateFactorWitness

open SubexpLiftRing SubexpQuarticRing SubexpSymbolicCost
open SubexpSelectedConversions SubexpTemplatePointServices
open SubexpTemplateSourceData

variable {p D q : ℕ} [Fact p.Prime] {F : Type*} {arity : F → ℕ}

/-- A raw template term assembled in the supplied original-index order. -/
def term (source : Prepared p 0) (target : Prepared p D) (theta : SubexpFactorPacketProvenance.Code p D)
    (inputs : ∀ e, SubexpFactorPacketProvenance.Input p D p (arity e) q) (ids : List F)
    (increment : Fin D → BaseWord p) (support : List (Fin D)) :
    SubexpTemplateData.Term p D where
  increment := increment
  support := support
  factors := ids.map (fun e => SubexpFactorPacketProvenance.blueprintRows source target theta (inputs e))

private theorem map_related {A B C : Type*} (ids : List A)
    (f : A → B) (g : A → C) (rel : B → C → Prop)
    (h : ∀ e ∈ ids, rel (f e) (g e)) :
    List.Forall₂ rel (ids.map f) (ids.map g) := by
  induction ids with
  | nil => exact .nil
  | cons e es ih =>
      exact .cons (h e (by simp)) (ih (fun x hx => h x (by simp [hx])))

section Preparation

variable (source : Prepared p 0) (target : Prepared p D) (theta : SubexpFactorPacketProvenance.Code p D)
variable (inputs : ∀ e, SubexpFactorPacketProvenance.Input p D p (arity e) q) (ids : List F)
variable (minusOne : Word (baseWidth p (D+1)))
variable (base increment : Fin D → BaseWord p) (support : List (Fin D))

/-- Each executed factor call has exactly the prepared form of its local
packet witness. Both lists use the original factor indices. -/
theorem preparedFactors_eq (templateCtx : TemplateContext)
    (hdimension : templateCtx.dimension = D)
    (hindex : templateCtx.indexWidth = indexBits D) :
    SubexpTemplateData.preparedFactors templateCtx source target minusOne base
      (term source target theta inputs ids increment support) =
      (ids.map (fun e => SubexpFactorPacketProvenance.factor source target theta minusOne
        (quarticPoint p source.modulus base increment) (inputs e))).map
        (SubexpBlockAssemblySemantics.Factor.prepared
          (SubexpDenseSerialization.encodeFixedQuarticCoefficients p D)
          (SubexpWeightCode.rawScalar D)) := by
  simp only [SubexpTemplateData.preparedFactors, term, SubexpTemplateData.point,
    List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro e he
  exact (SubexpFactorPacketProvenance.factor_prepared source target theta minusOne
    (quarticPoint p source.modulus base increment) (inputs e)
    (SubexpTemplateFactors.contextFor templateCtx
      (quarticPoint p source.modulus base increment)) hdimension hindex).symm

end Preparation

section Witness

noncomputable section

variable {ctx : SourceContext} {r : ℕ}
variable (source : Prepared p 0) (target : Prepared p ctx.dimension)
variable (theta : SubexpFactorPacketProvenance.Code p ctx.dimension)
variable (inputs : ∀ e, SubexpFactorPacketProvenance.Input p ctx.dimension p (arity e) q)
variable (ids : List F) (colors : F → Fin r)
variable (minusOne : Word (baseWidth p (ctx.dimension+1)))
variable (base increment : Fin ctx.dimension → BaseWord p)
variable (support : List (Fin ctx.dimension))

local notation "R" => SubexpFactorPacketProvenance.Ring p ctx.dimension

/-- The template's own modular point addition supplies the reference point.
The remaining assumptions describe only local source rows, cache entries,
and the runtime context's dimensions. -/
theorem factorWitness (templateCtx : TemplateContext)
    (hdimension : templateCtx.dimension = ctx.dimension)
    (hindex : templateCtx.indexWidth = indexBits ctx.dimension)
    (hminusOne : wordValue p (ctx.dimension+1) minusOne = -1)
    (hdegree : ∀ e ∈ ids, ∀ i w,
      ((((inputs e).sourceRows i w).map (SubexpRowSourceSemantics.denote source)).eval).natDegree ≤ q)
    (cache : List (List (SubexpFactorPacketProvenance.Code p ctx.dimension)))
    (hshared : ∀ e ∈ ids, (inputs e).cache = cache)
    (nodes : Fin p → R) (hu : TableInterpolation.UnitDifferences nodes)
    (hcache : ∀ i : Fin p,
      PolynomialAlgorithm.denote ((cache.map (List.map (SubexpFactorPacketProvenance.decode p ctx.dimension))).getD i.val []) =
        TableInterpolation.basis nodes hu i) :
    letI : One (SubexpFactorPacketProvenance.Code p ctx.dimension) := ⟨target.one⟩
    SubexpTemplateSourceProvenance.FactorWitness (ctx := ctx)
      templateCtx source target minusOne (QuarticSearch.liftedCoefficients p (ctx.dimension+1))
      base (term source target theta inputs ids increment support)
      (ids.map (fun e => SubexpSourceReference.factor
        (SubexpActualRing.residueSection p (ctx.dimension+1) (Nat.succ_pos ctx.dimension)).lift
        (cache.map (List.map (SubexpFactorPacketProvenance.decode p ctx.dimension)))
        (SubexpFactorPacketProvenance.referenceData source theta (inputs e) (colors e))
        (fun w => algebraMap (ZMod p) (SubexpActualRing.E p)
          (SubexpWordLift.sourceValue p (base w) +
            SubexpWordLift.sourceValue p (increment w))))) := by
  let _ : One (SubexpFactorPacketProvenance.Code p ctx.dimension) := ⟨target.one⟩
  let point := quarticPoint p source.modulus base increment
  refine ⟨ids.map (fun e => SubexpFactorPacketProvenance.factor source target theta minusOne point (inputs e)), ?_, ?_⟩
  · exact (preparedFactors_eq source target theta inputs ids minusOne base increment support
      templateCtx hdimension hindex).symm
  · apply map_related
    intro e he
    have hlocal := SubexpFactorPacketProvenance.factor_reference source target theta minusOne point (inputs e)
      hminusOne (hdegree e he) nodes hu
      (fun i => by simpa only [hshared e he] using hcache i) (colors e)
    have hpoint : (fun w => source.residueRing.decode (point w)) =
        fun w => algebraMap (ZMod p) (SubexpActualRing.E p)
          (SubexpWordLift.sourceValue p (base w) +
            SubexpWordLift.sourceValue p (increment w)) := by
      funext w
      exact quarticPoint_decode p source.modulus source base increment w
    unfold SubexpFactorPacketProvenance.FactorReference
      SubexpFactorPacketProvenance.referenceFactor at hlocal
    unfold SubexpFactorPacketProvenance.Ring SubexpActualRing.Ring
      SubexpActualRing.F at hlocal
    have hdecode :
        SubexpMomentSourceSemantics.coefficientValue p ctx.dimension
            (QuarticSearch.liftedCoefficients p (ctx.dimension + 1)) =
          SubexpFactorPacketProvenance.decode p ctx.dimension := by
      funext x
      rfl
    rw [hdecode]
    unfold SubexpSourceReference.FactorRel at hlocal ⊢
    simpa only [hshared e he, hpoint] using hlocal

end
end Witness

end SubexponentialSAT.SubexpTemplateFactorWitness

end OAI.Algorithms
