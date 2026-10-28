import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgramCompatibility

namespace OAI.Algorithms

/-! Sequential composition of the complete all-D matrix builder and the
closed signed bucket controller. The sole open service is the explicitly
stated native integer entry contract, to be supplied by LayoutProgram. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Matrix
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.LayoutMatrixProgram

def bucketCall : Code 288 := .call (ProgramLinking.liftProgram
  BucketProgram.Controller.signedProgram controllerRegs controllerPorts)
def command (entry : Code 256) : Code 288 :=
  .seq (LayoutMatrixProgram.command entry) bucketCall
def program (entry : Code 256) := compiled (command entry) 281 21

theorem command_eval (entry : Code 256) (base : Fin 288 → List Bool)
    (h285 : base 285=[]) (h286 : base 286=[])
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → Pair → Prop) (T B : ℕ)
    (hc : EntryContract entry base Valid Rel T B) (D n : ℕ) (js : List ℕ)
    (hi : base 17=ids js) (hv : ∀ j < D,∀ v∈js,Valid j v)
    (hjs : ∀ v∈js,v < n) (regs : Fin 16 → Bool) (W : List Bool)
    (hbase : ∀ i : Fin 25,base (controllerPorts i)=
      (BucketProgram.Controller.signedInitial (regs ∘ controllerRegs) W [] js n js.length).stacks i) :
    ∃ rows ys t e,
      MatrixRel Rel B D js rows ∧
      List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) rows ys ∧
      t ≤ commandCost T B D n js+BucketProgram.preMatrixCost W rows+
        BucketProgram.Controller.cost W ys js n js.length+2 ∧
      Eval (command entry) t (initialState base regs D) e ∧
      e.stacks 21=BucketProgram.Controller.tableOutput
        (BucketProgram.Controller.labelledRecords W ys js n js.length) := by
  obtain ⟨tm,htm,rm,rows,hm,hr⟩ := LayoutMatrixProgram.command_eval entry base h285 h286
    Valid Rel T B hc D n js hi hv (by intro v hv; exact (hjs v hv).le) regs
  have hp := project_finalState base rm W js n js.length rows (by
    intro i
    simpa [BucketProgram.Controller.signedInitial,BucketProgram.Controller.wideState] using hbase i)
  obtain ⟨rf,ys,hy,tb,htb,hb⟩ := BucketProgram.Controller.signedProgram_runsIn
    (rm ∘ controllerRegs) W rows js n js.length (matrixRel_dimensions hr).2 rfl hjs
  rw [←hp] at hb
  have he := eval_call_from_state BucketProgram.Controller.signedProgram controllerRegs controllerPorts
    (finalState base rm rows) (Fin.castAdd_injective _ _) (Fin.castAdd_injective _ _) hb
  let e := embedState controllerRegs controllerPorts (finalState base rm rows)
    (BucketProgram.Controller.signedFinal rf W ys js n js.length)
  refine ⟨rows,ys,tm+tb,e,hr,hy,by omega,hm.seq he,?_⟩
  exact embedState_stack controllerRegs controllerPorts _ _ (Fin.castAdd_injective _ _) 21

theorem program_runsIn (entry : Code 256) (base : Fin 288 → List Bool)
    (h285 : base 285=[]) (h286 : base 286=[])
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → Pair → Prop) (T B : ℕ)
    (hc : EntryContract entry base Valid Rel T B) (D n : ℕ) (js : List ℕ)
    (hi : base 17=ids js) (hv : ∀ j < D,∀ v∈js,Valid j v)
    (hjs : ∀ v∈js,v < n) (regs : Fin 16 → Bool) (W : List Bool)
    (hbase : ∀ i : Fin 25,base (controllerPorts i)=
      (BucketProgram.Controller.signedInitial (regs ∘ controllerRegs) W [] js n js.length).stacks i) :
    ∃ (rows : List (List Pair)) (ys : List (List (List Bool))) (e : Data 288),
      MatrixRel Rel B D js rows ∧
      List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) rows ys ∧
      RunsIn (program entry)
        (commandCost T B D n js+BucketProgram.preMatrixCost W rows+
          BucketProgram.Controller.cost W ys js n js.length+3)
        ((initialState base regs D).withPC (some (program entry).entry)) (e.withPC none) ∧
      e.stacks 21=BucketProgram.Controller.tableOutput
        (BucketProgram.Controller.labelledRecords W ys js n js.length) := by
  obtain ⟨rows,ys,t,e,hr,hy,ht,he,ho⟩ := command_eval entry base h285 h286 Valid Rel T B hc
    D n js hi hv hjs regs W hbase
  exact ⟨rows,ys,e,hr,hy,⟨t+1,by omega,compiled_halt_trace he 281 21⟩,ho⟩

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Matrix

end

end OAI.Algorithms
