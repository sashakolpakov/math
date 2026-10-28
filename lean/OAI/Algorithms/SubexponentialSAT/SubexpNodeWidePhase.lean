import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodePhaseExecution
import OAI.Algorithms.SubexponentialSAT.SubexpNodeWidePipeline

namespace OAI.Algorithms

/-! The concrete moment phase in the widened node workspace. All static
ports are outside the installed phase image and remain unchanged. -/

namespace SubexponentialSAT.SubexpNodeWidePhase

open BitProgram StructuredCalls
open SubexpQuarticRing SubexpLiftRing SubexpSymbolicCost SymbolicCost
open SubexpCanonicalWords

abbrev Data := State 16 288
def ports : Fin 256 → Fin 288 := Fin.castAdd 32
theorem ports_injective : Function.Injective ports := Fin.castAdd_injective _ _
def localState (d : Data) := projectState id ports d

def resultStacks (s : Fin 288 → List Bool) (jet shape : List Bool) : Fin 288 → List Bool :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update s 78 []) 116 []) 100 []) 101 []) 102 jet) 104 shape

theorem embedded_stacks (d : Data) (out : SubexpNodePhaseExecution.Data)
    (jet shape : List Bool)
    (h : out.stacks = SubexpNodePhaseExecution.resultStacks (localState d).stacks jet shape) :
    (embedState id ports d out).stacks = resultStacks d.stacks jet shape := by
  change Function.extend ports out.stacks d.stacks = _
  rw [h]
  simp only [SubexpNodePhaseExecution.resultStacks,
    ProgramLinking.extend_update ports_injective]
  have hb := congrArg StructuredProgram.State.stacks
    (embedState_project id ports d Function.injective_id ports_injective)
  change Function.extend ports (localState d).stacks d.stacks = d.stacks at hb
  rw [hb]
  rfl

theorem result_frame (s : Fin 288 → List Bool) (jet shape : List Bool) (i : Fin 288)
    (h78 : i ≠ 78) (h116 : i ≠ 116) (h100 : i ≠ 100)
    (h101 : i ≠ 101) (h102 : i ≠ 102) (h104 : i ≠ 104) :
    resultStacks s jet shape i = s i := by
  simp [resultStacks,h78,h116,h100,h101,h102,h104]

variable (p D : ℕ) [Fact p.Prime]
  (M : SubexpPreparedQuartic.Modulus p (D+1))
  (t z o : QuarticCode p D) (slots : List (RawIndex D))
  (source : (Fin D → ℕ) → Algorithm.Expr (CoeffList D (QuarticCode p D)))
  (c : Fin 4 → ZMod (p^(D+1)))
  (hz : quotientDenote c (z.map (wordValue p (D+1))) = 0)
  (hcanonical : CanonicalQuad p (D+1) z)
  (width : List Bool) (hwidth : width.length = baseWidth p (D+1))
  (hslots : ∀ k ∈ slots, Retained D k)

include hz hcanonical hwidth hslots in
theorem command_eval (d : Data) (qs : List (SubexpExtractionJobs.Query D))
    (valid : ∀ q ∈ qs, q.z < D)
    (hr : SubexpMomentStep.Ready (SubexpNodePhaseExecution.localState (localState d)) M.bits width)
    (hcontext : SubexpDenseMultiplication.ContextReady
      (SubexpEvaluationProgram.contextOf (SubexpNodePhaseExecution.localState (localState d)).stacks)
      M.bits width (SubexpDenseProgram.Projection.queryBytes slots) (SubexpQuarticFlatMul.flat t)
      (List.replicate (indexBits D) true))
    (hdimension : d.stacks 109 = List.replicate D true)
    (hstream : d.stacks 100 = Encoding.encodeList id (SubexpMomentPhase.records p D source qs))
    (h101 : d.stacks 101 = []) (h102 : d.stacks 102 = []) (h104 : d.stacks 104 = [])
    (h106 : d.stacks 106 = []) (h107 : d.stacks 107 = []) (h108 : d.stacks 108 = []) :
    ∃ n ≤ SubexpConcreteMomentPhase.cost p D M t z o slots source qs +
        SubexpNodePhaseExecution.clearCost (localState d) + 2, ∃ out : Data,
      Eval SubexpNodeWidePipeline.phase n d out ∧
      out.stacks = resultStacks d.stacks (SubexpNodePhaseExecution.jet p D M t z o slots source qs)
        (List.replicate (4 * baseWidth p (D+1)) false) := by
  obtain ⟨small,⟨n,hn,ht⟩,hs⟩ := SubexpNodePhaseExecution.program_runs p D M t z o slots source
    c hz hcanonical width hwidth hslots (localState d) qs valid hr hcontext hdimension hstream
    h101 h102 h104 h106 h107 h108
  exact ⟨n,hn,embedState id ports d small,
    eval_call_from_state SubexpNodeMomentPipeline.phaseProgram id ports d
      Function.injective_id ports_injective ht,
    embedded_stacks d small _ _ hs⟩

theorem jet_length (qs : List (SubexpExtractionJobs.Query D)) :
    (SubexpNodePhaseExecution.jet p D M t z o slots source qs).length =
      D * (4 * baseWidth p (D+1)) := by
  rw [SubexpNodePhaseExecution.jet, SubexpMomentPhase.cellsBytes_length,
    SubexpMomentPhase.fold_length, SubexpMomentPhase.zeroCells_length]

end SubexponentialSAT.SubexpNodeWidePhase

end OAI.Algorithms
