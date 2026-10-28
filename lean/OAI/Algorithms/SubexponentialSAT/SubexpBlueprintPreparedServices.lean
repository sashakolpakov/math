import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpBlueprintFactorProgram
import OAI.Algorithms.SubexponentialSAT.SubexpPreparedFactorExecution

namespace OAI.Algorithms

/-!
# Concrete scalar preparation inside the factor blueprint

The fixed 5-register, 22-stack preparation program runs on the blueprint's
assigned physical ports. All context words are preserved. The final theorem
includes the eight actual register-reset instructions preceding the call.
-/

namespace SubexponentialSAT.SubexpBlueprintPreparedServices

open BitProgram StructuredCalls SubexpBlueprintFactor

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem preparedRegs_injective : Function.Injective preparedRegs :=
  Fin.castAdd_injective _ _

private def preparedPortSource (i : Fin 128) : ℕ := match i.val with
  | 100 => 0 | 109 => 1 | 110 => 2 | 111 => 3 | 112 => 4 | 113 => 5
  | 114 => 6 | 94 => 7 | 95 => 8 | 115 => 9 | 116 => 10 | 117 => 11
  | 118 => 12 | 119 => 13 | 120 => 14 | 121 => 15 | 122 => 16
  | 123 => 17 | 124 => 18 | 125 => 19 | 126 => 20 | 127 => 21 | _ => 22

private theorem preparedPortSource_left (i : Fin 22) :
    preparedPortSource (preparedPorts i) = i.val := by
  fin_cases i <;> rfl

theorem preparedPorts_injective : Function.Injective preparedPorts := by
  intro i j h
  apply Fin.ext
  simpa only [preparedPortSource_left] using congrArg preparedPortSource h

/-- A small frame rule avoids reducing the entire 128-stack state at every
unassigned port of the lifted call. -/
theorem serviceState_stack_eq (ctx : Context) (regs : Fin 8 → Bool)
    (input : Word) (i : Fin 128) :
    (serviceState ctx regs input).stacks i =
      if i = 66 then ctx.sourceModulus else if i = 73 then ctx.sourceReduction
      else if i = 74 then ctx.sourceWidth else if i = 79 then ctx.targetWidth
      else if i = 90 then ctx.sourceZero else if i = 91 then ctx.pointStream
      else if i = 92 then ctx.targetModulus else if i = 93 then ctx.targetMinusOne
      else if i = 94 then List.replicate ctx.dimension true
      else if i = 95 then List.replicate ctx.indexWidth true
      else if i = 100 then input else [] := by
  simp only [serviceState,state]
  split <;> simp_all [Fin.ext_iff]

theorem project_prepared (ctx : Context)
    (hindex : ctx.indexWidth = SubexpSymbolicCost.indexBits ctx.dimension)
    (input : Word) :
    projectState preparedRegs preparedPorts (serviceState ctx (fun _ => false) input) =
      SubexpPreparedFactor.serviceState ctx.dimension input := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    change (serviceState ctx (fun _ => false) input).stacks (preparedPorts i) = _
    rw [serviceState_stack_eq]
    fin_cases i <;>
      simp [preparedPorts,SubexpPreparedFactor.stores,
        SubexpPreparedFactor.emptyBuffers,hindex]

/-- Only the input/output word changes; every arithmetic master in Context
and every stack outside the concrete call's footprint keeps its value. -/
theorem embed_prepared (ctx : Context)
    (hindex : ctx.indexWidth = SubexpSymbolicCost.indexBits ctx.dimension)
    (input output : Word) :
    embedState preparedRegs preparedPorts (serviceState ctx (fun _ => false) input)
      (SubexpPreparedFactor.serviceState ctx.dimension output) =
      serviceState ctx (fun _ => false) output := by
  apply embedState_eq_of_ports _ _ _ _ _ preparedRegs_injective preparedPorts_injective
  · intros; rfl
  · intros; rfl
  · intro i
    exact congrArg (fun d : State 5 22 => d.stacks i) (project_prepared ctx hindex output)
  · intro i hi
    have h100 : i ≠ 100 := fun h => hi ⟨0,h.symm⟩
    simp only [serviceState_stack_eq,h100,ite_false]

/-- Eight actual Boolean-register instructions leave every stack untouched. -/
theorem reset_eval (d : Data) :
    Eval reset 8 d ⟨fun _ => false,d.stacks⟩ := by
  let a0 := StructuredProgram.Atom.set (s := 128) (0 : Fin 8) false
  let a1 := StructuredProgram.Atom.set (s := 128) (1 : Fin 8) false
  let a2 := StructuredProgram.Atom.set (s := 128) (2 : Fin 8) false
  let a3 := StructuredProgram.Atom.set (s := 128) (3 : Fin 8) false
  let a4 := StructuredProgram.Atom.set (s := 128) (4 : Fin 8) false
  let a5 := StructuredProgram.Atom.set (s := 128) (5 : Fin 8) false
  let a6 := StructuredProgram.Atom.set (s := 128) (6 : Fin 8) false
  let a7 := StructuredProgram.Atom.set (s := 128) (7 : Fin 8) false
  have h := Eval.seq (Eval.base (StructuredProgram.Eval.atom a0 d))
    (Eval.seq (Eval.base (StructuredProgram.Eval.atom a1 (a0.eval d)))
    (Eval.seq (Eval.base (StructuredProgram.Eval.atom a2 (a1.eval (a0.eval d))))
    (Eval.seq (Eval.base (StructuredProgram.Eval.atom a3 (a2.eval (a1.eval (a0.eval d)))))
    (Eval.seq (Eval.base (StructuredProgram.Eval.atom a4 (a3.eval (a2.eval (a1.eval (a0.eval d))))))
    (Eval.seq (Eval.base (StructuredProgram.Eval.atom a5 (a4.eval (a3.eval (a2.eval (a1.eval (a0.eval d)))))))
    (Eval.seq (Eval.base (StructuredProgram.Eval.atom a6 (a5.eval (a4.eval (a3.eval (a2.eval (a1.eval (a0.eval d))))))))
      (Eval.base (StructuredProgram.Eval.atom a7 (a6.eval (a5.eval (a4.eval (a3.eval (a2.eval (a1.eval (a0.eval d)))))))))))))))
  have hf : a7.eval (a6.eval (a5.eval (a4.eval (a3.eval (a2.eval (a1.eval (a0.eval d))))))) =
      (⟨fun _ => false,d.stacks⟩ : Data) := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;>
        simp [a0,a1,a2,a3,a4,a5,a6,a7,StructuredProgram.Atom.eval,
          StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
          execInstr]
    · rfl
  simpa only [reset, atom, hf] using h

/-- The actual lifted scalar-preparation call retains its exact native cost. -/
theorem prepared_eval (ctx : Context)
    (hindex : ctx.indexWidth = SubexpSymbolicCost.indexBits ctx.dimension)
    (rows : List SubexpTableSource.Row) :
    Eval (.call (ProgramLinking.liftProgram SubexpPreparedFactor.program
        preparedRegs preparedPorts))
      (SubexpPreparedFactor.runCost ctx.dimension rows)
      (serviceState ctx (fun _ => false) (SubexpTableSource.encodeRows rows))
      (serviceState ctx (fun _ => false)
        (SubexpTableSource.encodeRows (SubexpPreparedFactor.prepareRows ctx.dimension rows))) := by
  have h := eval_call_lifted SubexpPreparedFactor.program preparedRegs preparedPorts
    (serviceState ctx (fun _ => false) (SubexpTableSource.encodeRows rows))
    preparedRegs_injective preparedPorts_injective
    (SubexpPreparedFactor.program_trace ctx.dimension rows)
  simpa only [embed_prepared ctx hindex] using h

/-- This is the final suffix of BlueprintFactor.command. It starts with
arbitrary caller registers and finishes with all eight registers false. -/
theorem prepare_eval (ctx : Context)
    (hindex : ctx.indexWidth = SubexpSymbolicCost.indexBits ctx.dimension)
    (regs : Fin 8 → Bool) (rows : List SubexpTableSource.Row) :
    Eval (.seq reset (.call (ProgramLinking.liftProgram SubexpPreparedFactor.program
        preparedRegs preparedPorts)))
      (8 + SubexpPreparedFactor.runCost ctx.dimension rows)
      (serviceState ctx regs (SubexpTableSource.encodeRows rows))
      (serviceState ctx (fun _ => false)
        (SubexpTableSource.encodeRows (SubexpPreparedFactor.prepareRows ctx.dimension rows))) := by
  have hr := reset_eval (serviceState ctx regs (SubexpTableSource.encodeRows rows))
  exact hr.seq (prepared_eval ctx hindex rows)

end SubexponentialSAT.SubexpBlueprintPreparedServices

end OAI.Algorithms
