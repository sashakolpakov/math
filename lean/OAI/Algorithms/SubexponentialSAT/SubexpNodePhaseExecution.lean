import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeMomentPipeline
import OAI.Algorithms.SubexponentialSAT.SubexpNodeCacheSetup
import OAI.Algorithms.SubexponentialSAT.SubexpMomentSemantics
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! The last node-worker stage executes the concrete moment machine after
physically clearing the active node and its rank. Its exact stack equation
provides the reusable workspace required by the outer collector. -/

namespace SubexponentialSAT.SubexpNodePhaseExecution

open BitProgram StructuredCalls
open SubexpQuarticRing SubexpLiftRing SubexpSymbolicCost SymbolicCost
open SubexpCanonicalWords

abbrev Data := State 16 256
abbrev Store := Fin 256 → List Bool

def ports : Fin 128 → Fin 256 := Fin.castAdd 128
theorem ports_injective : Function.Injective ports := Fin.castAdd_injective _ _

def prepared (d : Data) : Data :=
  SubexpNodeCacheSetup.clearOut (SubexpNodeCacheSetup.clearOut d 78) 116

def localState (d : Data) : SubexpMomentProgram.Data := projectState id ports (prepared d)

def clearCost (d : Data) : ℕ := 2 * (d.stacks 78).length + 2 * (d.stacks 116).length + 6

def resultStacks (s : Store) (jet shape : List Bool) : Store :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update s 78 []) 116 []) 100 []) 101 []) 102 jet) 104 shape

theorem native_stacks (p D : ℕ) (d out : SubexpMomentProgram.Data) (jet : List Bool)
    (hf : SubexpMomentPhase.Framed
      (SubexpJetInitProgram.initialized d D (baseWidth p (D+1))) out)
    (h100 : out.stacks 100 = []) (h101 : out.stacks 101 = [])
    (h102 : out.stacks 102 = jet) :
    out.stacks = Function.update (Function.update (Function.update
      (Function.update d.stacks 100 []) 101 []) 102 jet) 104
        (List.replicate (4 * baseWidth p (D+1)) false) := by
  funext i
  by_cases h : i = 100
  · subst i
    simpa using h100
  by_cases h' : i = 101
  · subst i
    simpa using h101
  by_cases h'' : i = 102
  · subst i
    simpa using h102
  by_cases h''' : i = 104
  · subst i
    simpa using SubexpMomentPhase.framed_initialized_cell (p := p) (D := D) hf
  · simpa [h, h', h'', h'''] using
      SubexpMomentPhase.framed_initialized_other (p := p) (D := D) hf i h h' h'' h'''

theorem embedded_stacks (d : Data) (out : SubexpMomentProgram.Data)
    (jet shape : List Bool)
    (h : out.stacks = Function.update (Function.update (Function.update
      (Function.update (localState d).stacks 100 []) 101 []) 102 jet) 104 shape) :
    (embedState id ports (prepared d) out).stacks = resultStacks d.stacks jet shape := by
  change Function.extend ports out.stacks (prepared d).stacks = _
  rw [h, ProgramLinking.extend_update ports_injective,
    ProgramLinking.extend_update ports_injective, ProgramLinking.extend_update ports_injective,
    ProgramLinking.extend_update ports_injective]
  have hb := congrArg StructuredProgram.State.stacks
    (embedState_project id ports (prepared d) Function.injective_id ports_injective)
  change Function.extend ports (localState d).stacks (prepared d).stacks =
    (prepared d).stacks at hb
  rw [hb]
  rfl

theorem result_frame (s : Store) (jet shape : List Bool) (i : Fin 256)
    (h78 : i ≠ 78) (h116 : i ≠ 116) (h100 : i ≠ 100)
    (h101 : i ≠ 101) (h102 : i ≠ 102) (h104 : i ≠ 104) :
    resultStacks s jet shape i = s i := by
  simp [resultStacks, h78, h116, h100, h101, h102, h104]

variable (p D : ℕ) [Fact p.Prime]
  (M : SubexpPreparedQuartic.Modulus p (D+1))
  (t z o : QuarticCode p D) (slots : List (RawIndex D))
  (source : (Fin D → ℕ) → Algorithm.Expr (CoeffList D (QuarticCode p D)))
  (c : Fin 4 → ZMod (p^(D+1)))
  (hz : quotientDenote c (z.map (wordValue p (D+1))) = 0)
  (hcanonical : CanonicalQuad p (D+1) z)
  (width : List Bool) (hwidth : width.length = baseWidth p (D+1))
  (hslots : ∀ k ∈ slots, Retained D k)

def jet (qs : List (SubexpExtractionJobs.Query D)) : List Bool :=
  SubexpMomentPhase.cellsBytes p D
    (qs.foldl (SubexpMomentPhase.step p D M t z o slots source)
      (SubexpMomentPhase.zeroCells p D))

include hz hcanonical hwidth hslots in
theorem command_eval (d : Data) (qs : List (SubexpExtractionJobs.Query D))
    (valid : ∀ q ∈ qs, q.z < D)
    (hr : SubexpMomentStep.Ready (localState d) M.bits width)
    (hcontext : SubexpDenseMultiplication.ContextReady
      (SubexpEvaluationProgram.contextOf (localState d).stacks) M.bits width
      (SubexpDenseProgram.Projection.queryBytes slots) (SubexpQuarticFlatMul.flat t)
      (List.replicate (indexBits D) true))
    (hdimension : d.stacks 109 = List.replicate D true)
    (hstream : d.stacks 100 = Encoding.encodeList id (SubexpMomentPhase.records p D source qs))
    (h101 : d.stacks 101 = []) (h102 : d.stacks 102 = []) (h104 : d.stacks 104 = [])
    (h106 : d.stacks 106 = []) (h107 : d.stacks 107 = []) (h108 : d.stacks 108 = []) :
    ∃ n ≤ SubexpConcreteMomentPhase.cost p D M t z o slots source qs + clearCost d + 1,
      ∃ out : Data, Eval SubexpNodeMomentPipeline.phaseCommand n d out ∧
      out.stacks = resultStacks d.stacks (jet p D M t z o slots source qs)
        (List.replicate (4 * baseWidth p (D+1)) false) := by
  have h109' : (localState d).stacks 109 = List.replicate D true := by
    simpa [localState, projectState, ports, prepared, SubexpNodeCacheSetup.clearOut] using hdimension
  have h100' : (localState d).stacks 100 =
      Encoding.encodeList id (SubexpMomentPhase.records p D source qs) := by
    simpa [localState, projectState, ports, prepared, SubexpNodeCacheSetup.clearOut] using hstream
  have h101' : (localState d).stacks 101 = [] := by
    simpa [localState, projectState, ports, prepared, SubexpNodeCacheSetup.clearOut] using h101
  have h102' : (localState d).stacks 102 = [] := by
    simpa [localState, projectState, ports, prepared, SubexpNodeCacheSetup.clearOut] using h102
  have h104' : (localState d).stacks 104 = [] := by
    simpa [localState, projectState, ports, prepared, SubexpNodeCacheSetup.clearOut] using h104
  have h106' : (localState d).stacks 106 = [] := by
    simpa [localState, projectState, ports, prepared, SubexpNodeCacheSetup.clearOut] using h106
  have h107' : (localState d).stacks 107 = [] := by
    simpa [localState, projectState, ports, prepared, SubexpNodeCacheSetup.clearOut] using h107
  have h108' : (localState d).stacks 108 = [] := by
    simpa [localState, projectState, ports, prepared, SubexpNodeCacheSetup.clearOut] using h108
  obtain ⟨n,hn,e,he,hf,_,he100,he101,he102⟩ :=
    SubexpConcreteMomentPhase.command_eval p D M t z o slots source c hz hcanonical
      width hwidth hslots (localState d) qs valid hr hcontext h109' h100'
      h101' h102' h104' h106' h107' h108'
  have ht : Trace SubexpConcreteMomentPhase.program (n+1)
      ((localState d).withPC (some SubexpConcreteMomentPhase.program.entry))
      (e.withPC none) := compiled_halt_trace he 100 102
  have hl := eval_call_from_state SubexpConcreteMomentPhase.program id ports (prepared d)
    Function.injective_id ports_injective ht
  have h78 := SubexpNodeCacheSetup.clear_eval d 78
  have h116 := SubexpNodeCacheSetup.clear_eval (SubexpNodeCacheSetup.clearOut d 78) 116
  have hall := h78.seq (h116.seq hl)
  refine ⟨_,?_,embedState id ports (prepared d) e,hall,?_⟩
  · simp only [SubexpNodeCacheSetup.clearOut, Function.update_of_ne (by decide : (116 : Fin 256) ≠ 78)]
    unfold clearCost
    omega
  · exact embedded_stacks d e _ _ (native_stacks p D (localState d) e _ hf he100 he101 he102)

include hz hcanonical hwidth hslots in
theorem program_runs (d : Data) (qs : List (SubexpExtractionJobs.Query D))
    (valid : ∀ q ∈ qs, q.z < D)
    (hr : SubexpMomentStep.Ready (localState d) M.bits width)
    (hcontext : SubexpDenseMultiplication.ContextReady
      (SubexpEvaluationProgram.contextOf (localState d).stacks) M.bits width
      (SubexpDenseProgram.Projection.queryBytes slots) (SubexpQuarticFlatMul.flat t)
      (List.replicate (indexBits D) true))
    (hdimension : d.stacks 109 = List.replicate D true)
    (hstream : d.stacks 100 = Encoding.encodeList id (SubexpMomentPhase.records p D source qs))
    (h101 : d.stacks 101 = []) (h102 : d.stacks 102 = []) (h104 : d.stacks 104 = [])
    (h106 : d.stacks 106 = []) (h107 : d.stacks 107 = []) (h108 : d.stacks 108 = []) :
    ∃ out : Data, RunsIn SubexpNodeMomentPipeline.phaseProgram
        (SubexpConcreteMomentPhase.cost p D M t z o slots source qs + clearCost d + 2)
        (d.withPC (some SubexpNodeMomentPipeline.phaseProgram.entry)) (out.withPC none) ∧
      out.stacks = resultStacks d.stacks (jet p D M t z o slots source qs)
        (List.replicate (4 * baseWidth p (D+1)) false) := by
  obtain ⟨n,hn,e,he,hs⟩ := command_eval p D M t z o slots source c hz hcanonical width hwidth
    hslots d qs valid hr hcontext hdimension hstream h101 h102 h104 h106 h107 h108
  exact ⟨e,⟨n+1,by omega,compiled_halt_trace he 100 102⟩,hs⟩

end SubexponentialSAT.SubexpNodePhaseExecution

end OAI.Algorithms
