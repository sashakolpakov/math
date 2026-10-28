import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTemplateSourceProvenance
import OAI.Algorithms.SubexponentialSAT.SubexpActualSourceCorrectness

namespace OAI.Algorithms

/-! Updating the exponent preserves the reusable packet provenance. This
installs the actual source constructor from prepared template data and local
factor witnesses, without a source-byte or complete block-value premise. -/

namespace SubexponentialSAT.SubexpTemplateSourceFamily

noncomputable section

open SubexpMomentSourceProgram SubexpMomentSourceSemantics
open SubexpProducedSourceRefinement SubexpTemplateSourceProvenance
open SubexpTemplateSourceData SubexpTemplatePointServices
open SubexpQuarticRing SubexpLiftRing SubexpSymbolicCost

variable {p : ℕ} [Fact p.Prime] {ctx : Context}
  (c : Fin 4 → ZMod (p ^ (ctx.dimension + 1)))
  [One (QuarticCode p ctx.dimension)]

local notation "R" => LiftRing.Extension (QuarticSearch.poly c)
local notation "RefTerm" => SubexpBlockAssemblySemantics.Term R
  (SymbolicCost.CoeffList ctx.dimension R)
local notation "RefBlock" => SubexpBlockAssemblySemantics.Block R
  (SymbolicCost.CoeffList ctx.dimension R)

local instance (bits : List Bool) : One (QuarticCode p (ctx.withExponent bits).dimension) :=
  inferInstanceAs (One (QuarticCode p ctx.dimension))

theorem term_withExponent (bits : List Bool) (a : Fin ctx.dimension → ℕ)
    {input : TermData ctx} {reference : RefTerm}
    (h : TermProvenance c a input reference) :
    TermProvenance (ctx := ctx.withExponent bits) c a (input.withExponent bits) reference := h

theorem group_withExponent (bits : List Bool) (a : Fin ctx.dimension → ℕ)
    {inputs : List (TermData ctx)} {references : List RefTerm}
    (h : List.Forall₂ (TermProvenance c a) inputs references) :
    List.Forall₂ (TermProvenance (ctx := ctx.withExponent bits) c a)
      (inputs.map (fun t => t.withExponent bits)) references := by
  induction h with
  | nil => exact .nil
  | cons h hs ih => exact .cons (term_withExponent c bits a h) ih

theorem block_withExponent (bits : List Bool) (a : Fin ctx.dimension → ℕ)
    {input : BlockData ctx} {reference : RefBlock}
    (h : BlockProvenance c a input reference) :
    BlockProvenance (ctx := ctx.withExponent bits) c a (input.withExponent bits) reference := by
  refine ⟨h.1, ?_⟩
  have liftGroups : ∀ {gs : List (List (TermData ctx))} {rs : List (List RefTerm)},
      List.Forall₂ (List.Forall₂ (TermProvenance c a)) gs rs →
      List.Forall₂ (List.Forall₂ (TermProvenance (ctx := ctx.withExponent bits) c a))
        (gs.map (List.map (fun t => t.withExponent bits))) rs := by
    intro gs rs hg
    induction hg with
    | nil => exact .nil
    | cons h hs ih => exact .cons (group_withExponent c bits a h) ih
  exact liftGroups h.2

theorem blocks_withExponent (bits : List Bool) (a : Fin ctx.dimension → ℕ)
    {inputs : List (BlockData ctx)} {references : List RefBlock}
    (h : List.Forall₂ (BlockProvenance c a) inputs references) :
    List.Forall₂ (BlockProvenance (ctx := ctx.withExponent bits) c a)
      (inputs.map (fun b => b.withExponent bits)) references := by
  induction h with
  | nil => exact .nil
  | cons h hs ih => exact .cons (block_withExponent c bits a h) ih

local instance : Zero (Raw p ctx.dimension) := ⟨[]⟩
local instance : One (Raw p ctx.dimension) := ⟨SubexpAlgorithm.rawOne ctx.dimension⟩

/-- The only semantic premises here concern individual factor packets and
the canonical base coordinates. All nested weight relations and all source
bytes are derived from the actual finite source constructor. -/
theorem source_family_exists
    (hwidth : ctx.width.length = baseWidth p 1)
    (htarget : ctx.target.length = baseWidth p (ctx.dimension + 1))
    (hmodulus : BinaryArithmetic.toNat ctx.modulus = p ^ (ctx.dimension + 1))
    (hzero : ctx.zero = SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension 0)
    (hone : ctx.one = SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension 1)
    (templateCtx : TemplateContext)
    (source : SubexpSelectedConversions.Prepared p 0)
    (target : SubexpSelectedConversions.Prepared p ctx.dimension)
    (minusOne : Word (baseWidth p (ctx.dimension + 1)))
    (bs : List (SubexpTemplateData.Block p ctx.dimension))
    (hn : ∀ b ∈ bs, BlockGood b)
    (hbase : ∀ b ∈ bs, ∀ i, BinaryArithmetic.toNat (b.base i).val < p)
    (referenceFactors : (Fin ctx.dimension → BaseWord p) →
      SubexpTemplateData.Term p ctx.dimension →
      List (SubexpBlockAssemblySemantics.Factor R (SymbolicCost.CoeffList ctx.dimension R)))
    (hf : ∀ b ∈ bs, ∀ ts ∈ b.groups, ∀ t ∈ ts,
      FactorWitness templateCtx source target minusOne c b.base t (referenceFactors b.base t))
    (hc : ContextGood
      (ctx.withExponent (SubexpExponentController.momentWord (fun _ : Fin ctx.dimension => 0)))
      (fun _ : Fin ctx.dimension => 0))
    (htemplate : ctx.template = encodeTemplate
      (bs.map (SubexpTemplateData.preparedBlock templateCtx source target minusOne)))
    (base : StructuredProgram.State 16 128)
    (hready : SubexpMomentSourceHost.Ready {ctx with exponent := []} base) :
    let inputs := blocksData ctx hwidth templateCtx source target minusOne bs hn
    ∃ (sourceBytes : List Bool → List Bool)
      (actual : (Fin ctx.dimension → ℕ) →
        List (SubexpBlockAssemblySemantics.Block (QuarticCode p ctx.dimension) (Raw p ctx.dimension))),
      SubexpOuterJobs.SourceSpec SubexpMomentSourceHost.fixedCommand
        (SubexpOuterJobs.ValidMoment ctx.dimension) sourceBytes
        (uniformTotalBudget ctx inputs + 8) (uniformSourceBytes ctx inputs) base ∧
      (∀ a : Fin ctx.dimension → ℕ,
        sourceBytes (SubexpExponentController.momentWord a) =
          SubexpPostfixControl.serializeCode
            (SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension)
            (SubexpAlgorithm.momentExpression ((actual a).map
              (SubexpBlockAssemblySemantics.Block.expression
                (SubexpWeightCode.rawScalar ctx.dimension)))).compile) ∧
      (∀ a : Fin ctx.dimension → ℕ,
        List.Forall₂ (SubexpSourceReference.BlockRel (coefficientValue p ctx.dimension c))
          (actual a) (bs.map fun b => referenceBlock c referenceFactors b a)) ∧
      ∀ a : Fin ctx.dimension → ℕ,
        (sourceBytes (SubexpExponentController.momentWord a)).length ≤
          uniformSourceBytes ctx inputs := by
  dsimp only
  apply SubexpActualSourceCorrectness.source_family_exists p ctx htarget hmodulus c
    hzero hone (blocksData ctx hwidth templateCtx source target minusOne bs hn) hc
  · rw [blocksData_templates]
    exact htemplate
  · exact hready
  · intro a
    exact blocks_withExponent c (SubexpExponentController.momentWord a) a
      (blocks_provenance hwidth templateCtx source target minusOne c referenceFactors bs hn hbase hf a)

end

end SubexponentialSAT.SubexpTemplateSourceFamily

end OAI.Algorithms
