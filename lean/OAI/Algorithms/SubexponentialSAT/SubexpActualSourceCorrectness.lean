import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpActualSourceSpec
import OAI.Algorithms.SubexponentialSAT.SubexpProducedSourceRefinement

namespace OAI.Algorithms

/-!
# Semantic installation of the actual source constructor

The source-byte function in this theorem is obtained from terminating runs
of the fixed source program. Input packet provenance determines typed
expressions for those same bytes. Neither a source stream nor an equality
to a complete moment expression is supplied by the caller.
-/

namespace SubexponentialSAT.SubexpActualSourceCorrectness

open SubexpMomentSourceProgram SubexpMomentSourceSemantics
open SubexpSymbolicCost SubexpQuarticRing SubexpLiftRing
open SubexpProducedSourceRefinement

variable (p : ℕ) [Fact p.Prime] (ctx : Context)
  (htarget : ctx.target.length = baseWidth p (ctx.dimension + 1))
  (hmodulus : BinaryArithmetic.toNat ctx.modulus = p ^ (ctx.dimension + 1))
  (c : Fin 4 → ZMod (p ^ (ctx.dimension + 1)))
  [quarticOne : One (QuarticCode p ctx.dimension)]

local notation "R" => LiftRing.Extension (QuarticSearch.poly c)
local notation "C" => QuarticCode p ctx.dimension
local notation "decode" => coefficientValue p ctx.dimension c

attribute [local instance]
  SubexpProducedSourceRefinement.instZeroRawDimension
  SubexpProducedSourceRefinement.instOneRawDimension

local instance (bits : List Bool) :
    One (QuarticCode p (ctx.withExponent bits).dimension) :=
  inferInstanceAs (One (QuarticCode p ctx.dimension))

include htarget hmodulus in
/-- The actual source service has one byte specification whose expressions
refine the reference blocks factor by factor. Every source equality here is
a conclusion of the machine run and local packet typing. -/
theorem source_family_exists
    (hzero : ctx.zero = SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension 0)
    (hone : ctx.one = SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension 1)
    (inputs : List (BlockData ctx))
    (hc : ContextGood
      (ctx.withExponent (SubexpExponentController.momentWord (fun _ : Fin ctx.dimension => 0)))
      (fun _ : Fin ctx.dimension => 0))
    (htemplate : ctx.template = encodeTemplate (inputs.map BlockData.template))
    (base : StructuredProgram.State 16 128)
    (hready : SubexpMomentSourceHost.Ready {ctx with exponent := []} base)
    (reference : (Fin ctx.dimension → ℕ) →
      List (SubexpBlockAssemblySemantics.Block R (SymbolicCost.CoeffList ctx.dimension R)))
    (hprovenance : ∀ a : Fin ctx.dimension → ℕ,
      List.Forall₂
        (BlockProvenance (ctx := ctx.withExponent
          (SubexpExponentController.momentWord a)) c a)
        (inputs.map (fun b => b.withExponent (SubexpExponentController.momentWord a)))
        (reference a)) :
    ∃ (sourceBytes : List Bool → List Bool)
      (actual : (Fin ctx.dimension → ℕ) →
        List (SubexpBlockAssemblySemantics.Block C (Raw p ctx.dimension))),
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
        List.Forall₂ (SubexpSourceReference.BlockRel decode) (actual a) (reference a)) ∧
      ∀ a : Fin ctx.dimension → ℕ,
        (sourceBytes (SubexpExponentController.momentWord a)).length ≤
          uniformSourceBytes ctx inputs := by
  classical
  obtain ⟨sourceBytes,hspec,houtputs⟩ :=
    SubexpActualSourceSpec.sourceSpec_exists ctx inputs hc htemplate base hready
  choose outputs hagreement hbytes using houtputs
  have htyped (a : Fin ctx.dimension → ℕ) :=
    source_refinement_exists (p := p)
      (ctx := ctx.withExponent (SubexpExponentController.momentWord a))
      htarget hmodulus c hzero hone (hagreement a) (hprovenance a)
  choose typed hsyntax hrelation using htyped
  let actual (a : Fin ctx.dimension → ℕ) :=
    (typed a).map (TypedBlock.syntax
      (ctx := ctx.withExponent (SubexpExponentController.momentWord a)) htarget)
  refine ⟨sourceBytes,actual,hspec,?_,?_,?_⟩
  · intro a
    let ctx' := ctx.withExponent (SubexpExponentController.momentWord a)
    have hmap := @List.map_map
      (SubexpBlockAssemblySemantics.Block
        (QuarticCode p ctx'.dimension) (Raw p ctx'.dimension))
      (SubexpAlgorithm.Block (Raw p ctx'.dimension))
      (TypedBlock p ctx' a)
      (@SubexpBlockAssemblySemantics.Block.expression
        (QuarticCode p ctx'.dimension) (Raw p ctx'.dimension)
        (@SubexpProducedSourceRefinement.instZeroRawDimension p ctx')
        (@SubexpProducedSourceRefinement.instOneRawDimension p ctx' quarticOne)
        (SubexpWeightCode.rawScalar ctx'.dimension))
      (TypedBlock.syntax (ctx := ctx') htarget)
      (typed a)
    have hserialized := congrArg
      (fun bs : List (SubexpAlgorithm.Block (Raw p ctx'.dimension)) =>
        SubexpPostfixControl.serializeCode
          (SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx'.dimension)
          (@SubexpAlgorithm.momentExpression (Raw p ctx'.dimension)
            SubexpProducedSourceRefinement.instZeroRawDimension
            (@SubexpProducedSourceRefinement.instOneRawDimension p ctx' quarticOne)
            bs).compile)
      hmap.symm
    have hzeroInstance :
        @SubexpProducedSourceRefinement.instZeroRawDimension p ctx' =
          @SubexpProducedSourceRefinement.instZeroRawDimension p ctx := by
      rfl
    have honeInstance :
        @SubexpProducedSourceRefinement.instOneRawDimension p ctx'
            quarticOne =
          @SubexpProducedSourceRefinement.instOneRawDimension p ctx quarticOne := by
      rfl
    have htransport :
        SubexpPostfixControl.serializeCode
            (SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx'.dimension)
            (@SubexpAlgorithm.momentExpression (Raw p ctx'.dimension)
              (@SubexpProducedSourceRefinement.instZeroRawDimension p ctx')
              (@SubexpProducedSourceRefinement.instOneRawDimension p ctx' quarticOne)
              (((typed a).map (TypedBlock.syntax (ctx := ctx') htarget)).map
                (@SubexpBlockAssemblySemantics.Block.expression
                  (QuarticCode p ctx'.dimension) (Raw p ctx'.dimension)
                  (@SubexpProducedSourceRefinement.instZeroRawDimension p ctx')
                  (@SubexpProducedSourceRefinement.instOneRawDimension p ctx' quarticOne)
                  (SubexpWeightCode.rawScalar ctx'.dimension)))).compile =
          SubexpPostfixControl.serializeCode
            (SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension)
            (@SubexpAlgorithm.momentExpression (Raw p ctx.dimension)
              (@SubexpProducedSourceRefinement.instZeroRawDimension p ctx)
              (@SubexpProducedSourceRefinement.instOneRawDimension p ctx quarticOne)
              (((typed a).map (TypedBlock.syntax (ctx := ctx') htarget)).map
                (@SubexpBlockAssemblySemantics.Block.expression
                  (QuarticCode p ctx.dimension) (Raw p ctx.dimension)
                  (@SubexpProducedSourceRefinement.instZeroRawDimension p ctx)
                  (@SubexpProducedSourceRefinement.instOneRawDimension p ctx quarticOne)
                  (SubexpWeightCode.rawScalar ctx.dimension)))).compile := by
      cases hzeroInstance
      cases honeInstance
      rfl
    dsimp only [ctx'] at hserialized htransport
    rw [hbytes a, hsyntax a]
    simp only [actual, expression, blocks]
    simpa only [Function.comp_def] using hserialized.trans htransport
  · intro a
    exact hrelation a
  · intro a
    rw [hbytes a]
    simpa only [uniformSourceBytes_withExponent] using
      source_length_le_uniform (hagreement a)

end SubexponentialSAT.SubexpActualSourceCorrectness

end OAI.Algorithms
