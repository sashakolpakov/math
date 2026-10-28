import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSourceReady
import OAI.Algorithms.SubexponentialSAT.SubexpMomentSourceSize
import OAI.Algorithms.SubexponentialSAT.SubexpOuterJobSetup

namespace OAI.Algorithms

/-! Install the actual reset-and-construct source service in the outer loop.
The semantic byte function below describes outputs of proved terminating
runs; it is not an input stream or an executable advice table. -/

namespace SubexponentialSAT.SubexpActualSourceSpec

open BitProgram StructuredCalls
open SubexpMomentSourceProgram
open scoped BigOperators

abbrev Data := State 16 128

theorem momentWord_injective (D : ℕ) :
    Function.Injective (@SubexpExponentController.momentWord D) := by
  intro a b h
  exact List.ofFn_injective (SymbolicCost.unaryWords_injective h)

/-- One fixed byte function is obtained from the actual source service.
Its witnesses retain the computed weights and their exact local semantics. -/
theorem sourceSpec_exists (ctx : Context) (bs : List (BlockData ctx))
    (hc : ContextGood
      (ctx.withExponent (SubexpExponentController.momentWord (fun _ : Fin ctx.dimension => 0)))
      (fun _ : Fin ctx.dimension => 0))
    (hTemplate : ctx.template = encodeTemplate (bs.map BlockData.template))
    (base : Data)
    (hready : SubexpMomentSourceHost.Ready {ctx with exponent := []} base) :
    ∃ sourceBytes : List Bool → List Bool,
      SubexpOuterJobs.SourceSpec SubexpMomentSourceHost.fixedCommand
        (SubexpOuterJobs.ValidMoment ctx.dimension) sourceBytes
        (uniformTotalBudget ctx bs + 8) (uniformSourceBytes ctx bs) base ∧
      ∀ a : Fin ctx.dimension → ℕ,
        ∃ outs : List (BlockResult (ctx.withExponent (SubexpExponentController.momentWord a)) a),
          List.Forall₂ (fun b out => out.input = b)
            (bs.map (fun b => b.withExponent (SubexpExponentController.momentWord a))) outs ∧
          sourceBytes (SubexpExponentController.momentWord a) =
            source (ctx.withExponent (SubexpExponentController.momentWord a)) outs := by
  classical
  have good (a : Fin ctx.dimension → ℕ) :
      ContextGood (ctx.withExponent (SubexpExponentController.momentWord a)) a :=
    hc.withExponent a
  have template (a : Fin ctx.dimension → ℕ) :
      (ctx.withExponent (SubexpExponentController.momentWord a)).template =
        encodeTemplate ((bs.map (fun b => b.withExponent
          (SubexpExponentController.momentWord a))).map BlockData.template) := by
    rw [encodeTemplate_withExponent]
    exact hTemplate
  have fixed (a : Fin ctx.dimension → ℕ) :=
    SubexpMomentSourceHost.fixedCommand_eval
      (ctx.withExponent (SubexpExponentController.momentWord a)) a (good a)
      (bs.map (fun b => b.withExponent (SubexpExponentController.momentWord a))) (template a)
  choose outs houts hrun using fixed
  let sourceAt (a : Fin ctx.dimension → ℕ) : List Bool :=
    source (ctx.withExponent (SubexpExponentController.momentWord a)) (outs a)
  let sourceBytes : List Bool → List Bool :=
    Function.extend (@SubexpExponentController.momentWord ctx.dimension) sourceAt (fun _ => [])
  have hbytes (a : Fin ctx.dimension → ℕ) :
      sourceBytes (SubexpExponentController.momentWord a) = sourceAt a :=
    (momentWord_injective ctx.dimension).extend_apply sourceAt (fun _ => []) a
  refine ⟨sourceBytes, ?_, ?_⟩
  · intro bits d hv hf hx hs
    rcases hv with ⟨a, ha, rfl⟩
    have hd : (∑ i, a i) ≤ 2 * ctx.dimension + 1 :=
      (Algorithm.mem_exponentList ctx.dimension (2 * ctx.dimension + 1) a).mp ha
    have ready : SubexpMomentSourceHost.Ready
        (ctx.withExponent (SubexpExponentController.momentWord a)) d :=
      SubexpSourceReady.ready_of_frame ctx base d (SubexpExponentController.momentWord a)
        hready hf hx hs
    obtain ⟨n, rf, hn, he⟩ := hrun a d ready
    have ht : totalBudget (ctx.withExponent (SubexpExponentController.momentWord a)) a
        (bs.map (fun b => b.withExponent (SubexpExponentController.momentWord a))) (outs a) ≤
          uniformTotalBudget ctx bs := by
      simpa only [uniformTotalBudget_withExponent] using totalBudget_le_uniform (good a) hd (houts a)
    have hw : (sourceAt a).length ≤ uniformSourceBytes ctx bs := by
      simpa only [sourceAt, uniformSourceBytes_withExponent] using source_length_le_uniform (houts a)
    rw [hbytes]
    exact ⟨n, ⟨rf, Function.update d.stacks 1 (sourceAt a)⟩, by omega, hw, he, rfl⟩
  · intro a
    exact ⟨outs a, houts a, hbytes a⟩

/-- The fixed source constructor is invoked at every actually generated
moment. No source-service contract or precomputed exponent stream is an
input to this execution theorem. -/
theorem jobs_program_runs (ctx : Context) (bs : List (BlockData ctx))
    (hc : ContextGood
      (ctx.withExponent (SubexpExponentController.momentWord (fun _ : Fin ctx.dimension => 0)))
      (fun _ : Fin ctx.dimension => 0))
    (hTemplate : ctx.template = encodeTemplate (bs.map BlockData.template))
    (base : Data)
    (hready : SubexpMomentSourceHost.Ready {ctx with exponent := []} base)
    (hgrid : SubexpOuterJobs.Context base ctx.dimension (SubexpSymbolicCost.indexBits ctx.dimension))
    (h14 : base.stacks 14 = []) (h111 : base.stacks 111 = [])
    (hwork : ∀ i ∈ SubexpExponentSourceProgram.work, base.stacks i = []) :
    ∃ (sourceBytes : List Bool → List Bool) (e : Data),
      RunsIn (SubexpOuterJobSetup.program SubexpMomentSourceHost.fixedCommand)
        (SubexpOuterJobSetup.bound ctx.dimension (SubexpSymbolicCost.indexBits ctx.dimension)
          (uniformTotalBudget ctx bs + 8) (uniformSourceBytes ctx bs))
        (base.withPC (some (SubexpOuterJobSetup.program SubexpMomentSourceHost.fixedCommand).entry))
        (e.withPC none) ∧
      e.stacks = Function.update base.stacks 14
        (SubexpMomentProgram.input
          (SubexpOuterJobs.allJobs sourceBytes ctx.dimension
            (SubexpSymbolicCost.indexBits ctx.dimension)
            (SubexpOuterJobs.momentRecords ctx.dimension)).reverse) ∧
      ∀ a : Fin ctx.dimension → ℕ,
        ∃ outs : List (BlockResult (ctx.withExponent (SubexpExponentController.momentWord a)) a),
          List.Forall₂ (fun b out => out.input = b)
            (bs.map (fun b => b.withExponent (SubexpExponentController.momentWord a))) outs ∧
          sourceBytes (SubexpExponentController.momentWord a) =
            source (ctx.withExponent (SubexpExponentController.momentWord a)) outs := by
  obtain ⟨sourceBytes, hspec, hmeaning⟩ := sourceSpec_exists ctx bs hc hTemplate base hready
  have h0 : base.stacks 0 = [] := by
    have h := congrFun (congrArg StructuredProgram.State.stacks hready) (0 : Fin 63)
    simpa [projectState, SubexpMomentSourceHost.ports, state] using h
  have h1 : base.stacks 1 = [] := by
    have h := congrFun (congrArg StructuredProgram.State.stacks hready) (1 : Fin 63)
    simpa [projectState, SubexpMomentSourceHost.ports, state] using h
  obtain ⟨e, he, hs⟩ := SubexpOuterJobSetup.program_runs
    SubexpMomentSourceHost.fixedCommand sourceBytes ctx.dimension
    (SubexpSymbolicCost.indexBits ctx.dimension)
    (uniformTotalBudget ctx bs + 8) (uniformSourceBytes ctx bs)
    base hgrid hspec h0 h1 h14 h111 hwork
  exact ⟨sourceBytes, e, he, hs, hmeaning⟩

end SubexponentialSAT.SubexpActualSourceSpec

end OAI.Algorithms
