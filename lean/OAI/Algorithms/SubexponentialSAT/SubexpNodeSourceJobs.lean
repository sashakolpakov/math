import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeJobsStage
import OAI.Algorithms.SubexponentialSAT.SubexpActualSourceCorrectness

namespace OAI.Algorithms

/-! The fixed source constructor is installed in the actual node job loop.
Its source bytes and typed expressions are obtained from the source machine's
execution theorem; neither is supplied as an external execution contract. -/

namespace SubexponentialSAT.SubexpNodeSourceJobs

open BitProgram StructuredCalls
open SubexpMomentSourceProgram SubexpMomentSourceSemantics
open SubexpSymbolicCost SubexpQuarticRing SubexpLiftRing

abbrev Data := SubexpNodeJobsStage.Data

def program := SubexpNodeJobsStage.masterProgram SubexpMomentSourceHost.fixedCommand

theorem program_runs (ctx : Context) (inputs : List (BlockData ctx))
    (hc : ContextGood
      (ctx.withExponent (SubexpExponentController.momentWord (fun _ : Fin ctx.dimension => 0)))
      (fun _ : Fin ctx.dimension => 0))
    (htemplate : ctx.template = encodeTemplate (inputs.map BlockData.template))
    (d : Data)
    (hready : SubexpMomentSourceHost.Ready {ctx with exponent := []}
      (SubexpNodeJobsStage.project d))
    (hgrid : SubexpOuterJobs.Context (SubexpNodeJobsStage.project d)
      ctx.dimension (indexBits ctx.dimension))
    (h138 : d.stacks 138 = []) (h139 : d.stacks 139 = [])
    (h152 : d.stacks 152 = []) (h100 : d.stacks 100 = [])
    (h127 : d.stacks 127 = Encoding.encodeList id (SubexpOuterJobs.momentRecords ctx.dimension))
    (h248 : d.stacks 248 = []) (h249 : d.stacks 249 = []) :
    ∃ (sourceBytes : List Bool → List Bool) (out : Data),
      RunsIn program
        (SubexpNodeJobsStage.masterBound sourceBytes ctx.dimension (indexBits ctx.dimension)
          (uniformTotalBudget ctx inputs + 8) (uniformSourceBytes ctx inputs) d)
        (d.withPC (some program.entry)) (out.withPC none) ∧
      out.stacks = Function.update d.stacks 100
        (SubexpNodeJobsStage.output sourceBytes ctx.dimension (indexBits ctx.dimension)) ∧
      ∀ a : Fin ctx.dimension → ℕ,
        ∃ outputs : List (BlockResult (ctx.withExponent (SubexpExponentController.momentWord a)) a),
          List.Forall₂ (fun b output => output.input = b)
            (inputs.map (fun b => b.withExponent (SubexpExponentController.momentWord a))) outputs ∧
          sourceBytes (SubexpExponentController.momentWord a) =
            source (ctx.withExponent (SubexpExponentController.momentWord a)) outputs := by
  obtain ⟨sourceBytes,hspec,hmeaning⟩ :=
    SubexpActualSourceSpec.sourceSpec_exists ctx inputs hc htemplate
      (SubexpNodeJobsStage.project d) hready
  obtain ⟨out,hrun,hs⟩ := SubexpNodeJobsStage.master_program_runs
    SubexpMomentSourceHost.fixedCommand sourceBytes ctx.dimension (indexBits ctx.dimension)
    (uniformTotalBudget ctx inputs + 8) (uniformSourceBytes ctx inputs) d hgrid hspec
    h138 h139 h152 h100 h127 h248 h249
  exact ⟨sourceBytes,out,hrun,hs,hmeaning⟩

section Typed

variable (p : ℕ) [Fact p.Prime] (ctx : Context)
  (htarget : ctx.target.length = baseWidth p (ctx.dimension + 1))
  (hmodulus : BinaryArithmetic.toNat ctx.modulus = p ^ (ctx.dimension + 1))
  (c : Fin 4 → ZMod (p ^ (ctx.dimension + 1)))
  [One (QuarticCode p ctx.dimension)]

local notation "R" => LiftRing.Extension (QuarticSearch.poly c)
local notation "C" => QuarticCode p ctx.dimension
local notation "decode" => coefficientValue p ctx.dimension c

local instance : Zero (Raw p ctx.dimension) := ⟨[]⟩
local instance : One (Raw p ctx.dimension) := ⟨SubexpAlgorithm.rawOne ctx.dimension⟩

local instance (bits : List Bool) :
    One (QuarticCode p (ctx.withExponent bits).dimension) :=
  inferInstanceAs (One (QuarticCode p ctx.dimension))

local instance (bits : List Bool) : Zero (Raw p (ctx.withExponent bits).dimension) :=
  inferInstanceAs (Zero (Raw p ctx.dimension))

local instance (bits : List Bool) : One (Raw p (ctx.withExponent bits).dimension) :=
  inferInstanceAs (One (Raw p ctx.dimension))

def expression (actual : (Fin ctx.dimension → ℕ) →
    List (SubexpBlockAssemblySemantics.Block C (Raw p ctx.dimension)))
    (a : Fin ctx.dimension → ℕ) : Algorithm.Expr (Raw p ctx.dimension) :=
  SubexpAlgorithm.momentExpression ((actual a).map
    (SubexpBlockAssemblySemantics.Block.expression (SubexpWeightCode.rawScalar ctx.dimension)))

include htarget hmodulus in
/-- Local packet provenance determines the exact expressions emitted at all
moments, and the real job loop serializes precisely their extraction jobs. -/
theorem typed_program_runs
    (hzero : ctx.zero = SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension 0)
    (hone : ctx.one = SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension 1)
    (inputs : List (BlockData ctx))
    (hc : ContextGood
      (ctx.withExponent (SubexpExponentController.momentWord (fun _ : Fin ctx.dimension => 0)))
      (fun _ : Fin ctx.dimension => 0))
    (htemplate : ctx.template = encodeTemplate (inputs.map BlockData.template))
    (reference : (Fin ctx.dimension → ℕ) →
      List (SubexpBlockAssemblySemantics.Block R (SymbolicCost.CoeffList ctx.dimension R)))
    (hprovenance : ∀ a : Fin ctx.dimension → ℕ,
      List.Forall₂
        (SubexpProducedSourceRefinement.BlockProvenance
          (ctx := ctx.withExponent (SubexpExponentController.momentWord a)) c a)
        (inputs.map (fun b => b.withExponent (SubexpExponentController.momentWord a)))
        (reference a))
    (d : Data)
    (hready : SubexpMomentSourceHost.Ready {ctx with exponent := []}
      (SubexpNodeJobsStage.project d))
    (hgrid : SubexpOuterJobs.Context (SubexpNodeJobsStage.project d)
      ctx.dimension (indexBits ctx.dimension))
    (h138 : d.stacks 138 = []) (h139 : d.stacks 139 = [])
    (h152 : d.stacks 152 = []) (h100 : d.stacks 100 = [])
    (h127 : d.stacks 127 = Encoding.encodeList id (SubexpOuterJobs.momentRecords ctx.dimension))
    (h248 : d.stacks 248 = []) (h249 : d.stacks 249 = []) :
    ∃ (sourceBytes : List Bool → List Bool)
      (actual : (Fin ctx.dimension → ℕ) →
        List (SubexpBlockAssemblySemantics.Block C (Raw p ctx.dimension))) (out : Data),
      RunsIn program
        (SubexpNodeJobsStage.masterBound sourceBytes ctx.dimension (indexBits ctx.dimension)
          (uniformTotalBudget ctx inputs + 8) (uniformSourceBytes ctx inputs) d)
        (d.withPC (some program.entry)) (out.withPC none) ∧
      out.stacks = Function.update d.stacks 100
        (SubexpMomentProgram.input (SubexpQueryOrder.generatedJobs
          (SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension)
          (expression p ctx actual))) ∧
      (∀ a : Fin ctx.dimension → ℕ,
        List.Forall₂ (SubexpSourceReference.BlockRel decode) (actual a) (reference a)) ∧
      (∀ a : Fin ctx.dimension → ℕ,
        sourceBytes (SubexpExponentController.momentWord a) =
          SubexpPostfixControl.serializeCode
            (SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension)
            (expression p ctx actual a).compile) ∧
      ∀ a : Fin ctx.dimension → ℕ,
        (sourceBytes (SubexpExponentController.momentWord a)).length ≤
          uniformSourceBytes ctx inputs := by
  obtain ⟨sourceBytes,actual,hspec,hbytes,hrelation,hsize⟩ :=
    SubexpActualSourceCorrectness.source_family_exists p ctx htarget hmodulus c
      hzero hone inputs hc htemplate (SubexpNodeJobsStage.project d) hready
      reference hprovenance
  obtain ⟨out,hrun,hs⟩ := SubexpNodeJobsStage.master_program_runs
    SubexpMomentSourceHost.fixedCommand sourceBytes ctx.dimension (indexBits ctx.dimension)
    (uniformTotalBudget ctx inputs + 8) (uniformSourceBytes ctx inputs) d hgrid hspec
    h138 h139 h152 h100 h127 h248 h249
  have hout := SubexpNodeJobsStage.output_generated sourceBytes
    (SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension)
    (expression p ctx actual) (fun a _ => hbytes a)
  rw [hout] at hs
  exact ⟨sourceBytes,actual,out,hrun,hs,hrelation,hbytes,hsize⟩

end Typed
end SubexponentialSAT.SubexpNodeSourceJobs

end OAI.Algorithms
