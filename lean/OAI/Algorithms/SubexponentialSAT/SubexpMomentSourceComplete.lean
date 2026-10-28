import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMomentSourceExecution

namespace OAI.Algorithms

/-! Composition of actual current-X weights, table source assembly, and the
fixed r-fold moment source constructor. The reusable input is unweighted. -/

namespace SubexponentialSAT.SubexpMomentSourceProgram

open BitProgram StructuredCalls

attribute [local irreducible] WeightResult.literal TermResult.prepared BlockResult.prepared

private def kernelInverse (i : Fin 63) : Fin 24 := match i.val with
  | 0 => 0 | 1 => 1 | 27 => 2 | 28 => 3 | 8 => 4 | 9 => 5 | 10 => 6 | 11 => 7
  | 12 => 8 | 13 => 9 | 14 => 10 | 15 => 11 | 16 => 12 | 61 => 13
  | 17 => 14 | 18 => 15 | 3 => 16 | 4 => 17 | 59 => 18 | 60 => 19
  | 58 => 20 | 5 => 21 | 6 => 22 | 7 => 23 | _ => 0

theorem kernelPorts_injective : Function.Injective kernelPorts :=
  (show Function.LeftInverse kernelInverse kernelPorts from by
    intro i; fin_cases i <;> rfl).injective

def source (ctx : Context) {a : Fin ctx.dimension → ℕ}
    (outs : List (BlockResult ctx a)) : Word :=
  SubexpKernelControl.momentCode ctx.zero ctx.one
    ((preparedBlocks outs).map (SubexpBlockAssembly.compiledBlock ctx.zero ctx.one))

def totalBudget (ctx : Context) (a : Fin ctx.dimension → ℕ)
    (bs : List (BlockData ctx)) (outs : List (BlockResult ctx a)) : ℕ :=
  preparationBudget ctx a bs outs+
    SubexpBlockAssembly.assemblySteps ctx.zero ctx.one (preparedBlocks outs)+
    SubexpKernelControl.kernelCost ctx.zero ctx.one
      ((preparedBlocks outs).map (SubexpBlockAssembly.compiledBlock ctx.zero ctx.one))+
    9*(source ctx outs).length+17

theorem assemble_eval (ctx : Context) (r : Fin 8 → Bool)
    (bs : List SubexpBlockAssembly.Block) :
    Eval (.call (ProgramLinking.liftProgram SubexpBlockAssembly.actualProgram registers assemblyPorts))
      (SubexpBlockAssembly.assemblySteps ctx.zero ctx.one bs)
      (state ctx (flags r false false false) (SubexpBlockAssembly.encodeBlocks bs)
        SubexpBlockAssembly.emptyBuffers [] [] [] [])
      (state ctx (flags r false false false) (SubexpBlockAssembly.assembled ctx.zero ctx.one bs)
        SubexpBlockAssembly.emptyBuffers [] [] [] []) := by
  let d := state ctx (flags r false false false) (SubexpBlockAssembly.encodeBlocks bs)
    SubexpBlockAssembly.emptyBuffers [] [] [] []
  have h := eval_call_lifted SubexpBlockAssembly.actualProgram registers assemblyPorts d
    registers_injective assemblyPorts_injective
    (SubexpBlockAssembly.actualProgram_measured ctx.zero ctx.one bs)
  simpa only [SubexpBlockAssembly.serviceState,SubexpBlockAssembly.state,d,assembly_embed,flags_flags] using h

theorem kernel_project (ctx : Context) (r : Fin 8 → Bool) (bs : List SubexpKernelControl.Block) :
    SubexpKernelService.initialState
      (projectState registers kernelPorts (state ctx r (SubexpKernelControl.encodeBlocks bs)
        SubexpBlockAssembly.emptyBuffers [] [] [] [])) ctx.zero ctx.one bs =
      projectState registers kernelPorts (state ctx r (SubexpKernelControl.encodeBlocks bs)
        SubexpBlockAssembly.emptyBuffers [] [] [] []) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;> rfl

theorem kernel_embed (ctx : Context) (r : Fin 8 → Bool) (input output : Word) :
    embedState registers kernelPorts
      (state ctx r input SubexpBlockAssembly.emptyBuffers [] [] [] [])
      (SubexpKernelService.finalState
        (projectState registers kernelPorts
          (state ctx r input SubexpBlockAssembly.emptyBuffers [] [] [] [])) ctx.zero ctx.one output) =
      state ctx (flags r false false false) [] SubexpBlockAssembly.emptyBuffers [] [] [] output := by
  apply embedState_eq_of_ports _ _ _ _ _ registers_injective kernelPorts_injective
  · intro i
    fin_cases i <;> rfl
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0,h.symm⟩
    have h1 : i ≠ 1 := fun h => hi ⟨1,h.symm⟩
    have h2 : i ≠ 2 := fun h => hi ⟨2,h.symm⟩
    simp [state,flags,h0,h1,h2]
  · intro i
    fin_cases i <;> rfl
  · intro i hi
    have h1 : i ≠ 1 := fun h => hi ⟨1,by simpa [kernelPorts] using h.symm⟩
    have h58 : i ≠ 58 := fun h => hi ⟨20,by simpa [kernelPorts] using h.symm⟩
    fin_cases i <;> first | contradiction | rfl

theorem capture_source_eval (ctx : Context) (r : Fin 8 → Bool)
    {a : Fin ctx.dimension → ℕ} (outs : List (BlockResult ctx a)) :
    Eval (.call (ProgramLinking.liftProgram SubexpKernelService.program registers kernelPorts))
      (SubexpKernelControl.kernelCost ctx.zero ctx.one
        ((preparedBlocks outs).map (SubexpBlockAssembly.compiledBlock ctx.zero ctx.one))+
        9*(source ctx outs).length+16)
      (state ctx r (SubexpBlockAssembly.assembled ctx.zero ctx.one (preparedBlocks outs))
        SubexpBlockAssembly.emptyBuffers [] [] [] [])
      (state ctx (flags r false false false) [] SubexpBlockAssembly.emptyBuffers [] [] [] (source ctx outs)) := by
  let bs := (preparedBlocks outs).map (SubexpBlockAssembly.compiledBlock ctx.zero ctx.one)
  let d := state ctx r (SubexpKernelControl.encodeBlocks bs)
    SubexpBlockAssembly.emptyBuffers [] [] [] []
  have ht := SubexpKernelService.program_trace (projectState registers kernelPorts d) ctx.zero ctx.one bs
  change Trace _ _ ((SubexpKernelService.initialState _ ctx.zero ctx.one bs).withPC _)
    ((SubexpKernelService.finalState _ ctx.zero ctx.one (source ctx outs)).withPC none) at ht
  rw [kernel_project] at ht
  have h := eval_call_from_state SubexpKernelService.program registers kernelPorts d
    registers_injective kernelPorts_injective ht
  simpa only [d,kernel_embed,bs,source,SubexpBlockAssembly.assembled] using h

/-- The actual fixed source program constructs all exponent-dependent weights,
all factor instruction streams, and the final separated moment source. The
returned records expose local arithmetic witnesses; none is caller supplied. -/
theorem program_runs (ctx : Context) (a : Fin ctx.dimension → ℕ)
    (hc : ContextGood ctx a) (bs : List (BlockData ctx))
    (hTemplate : ctx.template = encodeTemplate (bs.map BlockData.template))
    (r : Fin 8 → Bool) :
    ∃ (outs : List (BlockResult ctx a)) (rf : Fin 8 → Bool),
      List.Forall₂ (fun b out => out.input = b) bs outs ∧
      RunsIn program (totalBudget ctx a bs outs)
        ((state ctx r [] SubexpBlockAssembly.emptyBuffers [] [] [] []).withPC (some program.entry))
        ((state ctx (flags rf false false false) [] SubexpBlockAssembly.emptyBuffers [] [] []
          (source ctx outs)).withPC none) := by
  obtain ⟨outs,np,rp,houts,hnp,hp⟩ := prepareBlocks_eval ctx a hc bs hTemplate r []
  have ha := assemble_eval ctx rp (preparedBlocks outs)
  have hs := capture_source_eval ctx (flags rp false false false) outs
  simp only [flags_flags] at hs
  have ht := compiled_halt_trace (Eval.seq hp (Eval.seq ha hs)) 0 1
  refine ⟨outs,rp,houts,⟨_,?_,ht⟩⟩
  unfold totalBudget
  omega

end SubexponentialSAT.SubexpMomentSourceProgram

end OAI.Algorithms
