import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMomentSourceComplete

namespace OAI.Algorithms

/-! Physical call interface for the outer retained-exponent/job loop. -/

namespace SubexponentialSAT.SubexpMomentSourceHost

open BitProgram StructuredCalls

abbrev Data := State 16 128
abbrev Code := Cmd 16 128
abbrev SourceContext := SubexpMomentSourceProgram.Context

def registers : Fin 8 → Fin 16 := Fin.castAdd 8

/-- Preserve X0/source1 and put D/I on2/3. Move the three conflicting local
work stacks to63/64/65. The job output14 and outer streams110/111 are framed. -/
def ports (i : Fin 63) : Fin 128 :=
  if i = 2 then 63 else if i = 3 then 64 else if i = 14 then 65
  else if i = 27 then 2 else if i = 28 then 3 else ⟨i.val,by omega⟩

private def inverse (i : Fin 128) : Fin 63 :=
  if i = 63 then 2 else if i = 64 then 3 else if i = 65 then 14
  else if i = 2 then 27 else if i = 3 then 28 else ⟨i.val % 63,Nat.mod_lt _ (by decide)⟩

theorem registers_injective : Function.Injective registers := Fin.castAdd_injective 8 8
theorem ports_injective : Function.Injective ports :=
  (show Function.LeftInverse inverse ports from by intro i; fin_cases i <;> rfl).injective

def command : Code := .call
  (ProgramLinking.liftProgram SubexpMomentSourceProgram.program registers ports)

private def resetList : List (Fin 16) → StructuredProgram.Cmd 16 128
  | [] => .skip
  | i :: is => .seq (.atom (.set i false)) (resetList is)

private def resetListState (is : List (Fin 16)) (d : Data) : Data :=
  ⟨fun i => if i ∈ is then false else d.regs i, d.stacks⟩

private theorem resetList_eval (is : List (Fin 16)) (d : Data) :
    StructuredProgram.Eval (resetList is) is.length d (resetListState is d) := by
  induction is generalizing d with
  | nil => simpa [resetList, resetListState] using StructuredProgram.Eval.skip d
  | cons i is ih =>
    have h := StructuredProgram.Eval.seq (StructuredProgram.Eval.atom (.set i false) d)
      (ih ((StructuredProgram.Atom.set i false).eval d))
    have he : resetListState is ((StructuredProgram.Atom.set i false).eval d) =
        resetListState (i :: is) d := by
      apply congrArg₂ StructuredProgram.State.mk
      · funext j
        simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr, Function.update]
        ac_rfl
      · rfl
    simpa only [resetList, List.length_cons, he, Nat.add_comm] using h

/-- Eight actual register writes give every invocation the same local entry
state. Caller data on every stack is preserved. -/
def reset : Code := .base (resetList [0, 1, 2, 3, 4, 5, 6, 7])

def resetState (d : Data) : Data :=
  ⟨fun i => if i.val < 8 then false else d.regs i, d.stacks⟩

theorem reset_eval (d : Data) : Eval reset 8 d (resetState d) := by
  have h := resetList_eval [0, 1, 2, 3, 4, 5, 6, 7] d
  have he : resetListState [0, 1, 2, 3, 4, 5, 6, 7] d = resetState d := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> rfl
    · rfl
  rw [he] at h
  exact .base h

def fixedCommand : Code := .seq reset command

def fixedProgram := StructuredCalls.compiled fixedCommand 0 1

def Ready (ctx : SourceContext) (d : Data) : Prop :=
  projectState registers ports d = SubexpMomentSourceProgram.state ctx (d.regs ∘ registers)
    [] SubexpBlockAssembly.emptyBuffers [] [] [] []

private theorem source_stacks (ctx : SourceContext) (r r' : Fin 8 → Bool) (code : List Bool) :
    (SubexpMomentSourceProgram.state ctx r' [] SubexpBlockAssembly.emptyBuffers [] [] [] code).stacks =
      Function.update
        (SubexpMomentSourceProgram.state ctx r [] SubexpBlockAssembly.emptyBuffers [] [] [] []).stacks 1 code := by
  funext i
  fin_cases i <;> rfl

/-- The actual source service returns only source1; every other caller stack
is preserved, including the current exponent, dimensions, job stream, and
the reusable template. Local arithmetic may change the Boolean registers. -/
theorem command_eval (ctx : SourceContext) (a : Fin ctx.dimension → ℕ)
    (hc : SubexpMomentSourceProgram.ContextGood ctx a)
    (bs : List (SubexpMomentSourceProgram.BlockData ctx))
    (hTemplate : ctx.template = SubexpMomentSourceProgram.encodeTemplate
      (bs.map SubexpMomentSourceProgram.BlockData.template))
    (d : Data) (hready : Ready ctx d) :
    ∃ (outs : List (SubexpMomentSourceProgram.BlockResult ctx a)) (n : ℕ) (rf : Fin 16 → Bool),
      List.Forall₂ (fun b out => out.input = b) bs outs ∧
      n ≤ SubexpMomentSourceProgram.totalBudget ctx a bs outs ∧
      Eval command n d ⟨rf,Function.update d.stacks 1 (SubexpMomentSourceProgram.source ctx outs)⟩ := by
  obtain ⟨outs,rl,houts,⟨n,hn,ht⟩⟩ :=
    SubexpMomentSourceProgram.program_runs ctx a hc bs hTemplate (d.regs ∘ registers)
  have h := eval_call_from_state SubexpMomentSourceProgram.program registers ports d
    registers_injective ports_injective (by rw [hready]; exact ht)
  let localEnd := SubexpMomentSourceProgram.state ctx
    (SubexpMomentSourceProgram.flags rl false false false) []
    SubexpBlockAssembly.emptyBuffers [] [] [] (SubexpMomentSourceProgram.source ctx outs)
  let endpoint := embedState registers ports d localEnd
  have hstart : embedState registers ports d
      (SubexpMomentSourceProgram.state ctx (d.regs ∘ registers)
        [] SubexpBlockAssembly.emptyBuffers [] [] [] []) = d := by
    rw [←hready]
    exact embedState_project registers ports d registers_injective ports_injective
  have hstack : endpoint.stacks = Function.update d.stacks 1 (SubexpMomentSourceProgram.source ctx outs) := by
    change Function.extend ports localEnd.stacks d.stacks = _
    rw [source_stacks ctx (d.regs ∘ registers)]
    rw [ProgramLinking.extend_update ports_injective]
    have hs := congrArg StructuredProgram.State.stacks hstart
    change Function.extend ports
      (SubexpMomentSourceProgram.state ctx (d.regs ∘ registers)
        [] SubexpBlockAssembly.emptyBuffers [] [] [] []).stacks d.stacks = d.stacks at hs
    rw [hs]
    rfl
  have he : endpoint = ⟨endpoint.regs,Function.update d.stacks 1
      (SubexpMomentSourceProgram.source ctx outs)⟩ := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · exact hstack
  refine ⟨outs,n,endpoint.regs,houts,hn,?_⟩
  change Eval command n d endpoint at h
  rwa [he] at h

/-- The output witnesses are selected once from an actual terminating run of
the fixed source program. The same trace is then lifted for every caller;
there is no supplied source stream or register-independence assumption. -/
theorem fixedCommand_eval (ctx : SourceContext) (a : Fin ctx.dimension → ℕ)
    (hc : SubexpMomentSourceProgram.ContextGood ctx a)
    (bs : List (SubexpMomentSourceProgram.BlockData ctx))
    (hTemplate : ctx.template = SubexpMomentSourceProgram.encodeTemplate
      (bs.map SubexpMomentSourceProgram.BlockData.template)) :
    ∃ outs : List (SubexpMomentSourceProgram.BlockResult ctx a),
      List.Forall₂ (fun b out => out.input = b) bs outs ∧
      ∀ (d : Data), Ready ctx d →
        ∃ (n : ℕ) (rf : Fin 16 → Bool),
          n ≤ SubexpMomentSourceProgram.totalBudget ctx a bs outs + 8 ∧
          Eval fixedCommand n d
            ⟨rf, Function.update d.stacks 1 (SubexpMomentSourceProgram.source ctx outs)⟩ := by
  obtain ⟨outs,rl,houts,⟨n,hn,ht⟩⟩ :=
    SubexpMomentSourceProgram.program_runs ctx a hc bs hTemplate (fun _ => false)
  refine ⟨outs,houts,?_⟩
  intro d hready
  have hproject : projectState registers ports (resetState d) =
      SubexpMomentSourceProgram.state ctx (fun _ => false)
        [] SubexpBlockAssembly.emptyBuffers [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      simp [resetState, registers, i.isLt]
    · exact congrArg StructuredProgram.State.stacks hready
  have h := eval_call_from_state SubexpMomentSourceProgram.program registers ports (resetState d)
    registers_injective ports_injective (by rw [hproject]; exact ht)
  let localEnd := SubexpMomentSourceProgram.state ctx
    (SubexpMomentSourceProgram.flags rl false false false) []
    SubexpBlockAssembly.emptyBuffers [] [] [] (SubexpMomentSourceProgram.source ctx outs)
  let endpoint := embedState registers ports (resetState d) localEnd
  have hstart : embedState registers ports (resetState d)
      (SubexpMomentSourceProgram.state ctx (fun _ => false)
        [] SubexpBlockAssembly.emptyBuffers [] [] [] []) = resetState d := by
    rw [←hproject]
    exact embedState_project registers ports (resetState d) registers_injective ports_injective
  have hstack : endpoint.stacks =
      Function.update d.stacks 1 (SubexpMomentSourceProgram.source ctx outs) := by
    change Function.extend ports localEnd.stacks d.stacks = _
    rw [source_stacks ctx (fun _ => false)]
    rw [ProgramLinking.extend_update ports_injective]
    have hs := congrArg StructuredProgram.State.stacks hstart
    change Function.extend ports
      (SubexpMomentSourceProgram.state ctx (fun _ => false)
        [] SubexpBlockAssembly.emptyBuffers [] [] [] []).stacks d.stacks = d.stacks at hs
    rw [hs]
    rfl
  have he : endpoint = ⟨endpoint.regs, Function.update d.stacks 1
      (SubexpMomentSourceProgram.source ctx outs)⟩ := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · exact hstack
  refine ⟨8 + n,endpoint.regs,by omega,?_⟩
  change Eval command n (resetState d) endpoint at h
  rw [he] at h
  exact Eval.seq (reset_eval d) h

theorem fixedProgram_runs (ctx : SourceContext) (a : Fin ctx.dimension → ℕ)
    (hc : SubexpMomentSourceProgram.ContextGood ctx a)
    (bs : List (SubexpMomentSourceProgram.BlockData ctx))
    (hTemplate : ctx.template = SubexpMomentSourceProgram.encodeTemplate
      (bs.map SubexpMomentSourceProgram.BlockData.template)) :
    ∃ outs : List (SubexpMomentSourceProgram.BlockResult ctx a),
      List.Forall₂ (fun b out => out.input = b) bs outs ∧
      ∀ (d : Data), Ready ctx d →
        ∃ rf : Fin 16 → Bool,
          RunsIn fixedProgram (SubexpMomentSourceProgram.totalBudget ctx a bs outs + 9)
            (d.withPC (some fixedProgram.entry))
            ((⟨rf, Function.update d.stacks 1
              (SubexpMomentSourceProgram.source ctx outs)⟩ : Data).withPC none) := by
  obtain ⟨outs,houts,h⟩ := fixedCommand_eval ctx a hc bs hTemplate
  refine ⟨outs,houts,?_⟩
  intro d hd
  obtain ⟨n,rf,hn,he⟩ := h d hd
  exact ⟨rf,n + 1,by omega,compiled_halt_trace he 0 1⟩

end SubexponentialSAT.SubexpMomentSourceHost

end OAI.Algorithms
