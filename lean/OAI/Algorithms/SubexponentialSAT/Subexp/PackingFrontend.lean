import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingFrontendData
import OAI.Algorithms.SubexponentialSAT.SubexpPlanAlphabetBounds

namespace OAI.Algorithms

/-! Actual execution of the fixed packing controller's first three stages. -/
namespace SubexponentialSAT.Subexp.PackingFrontend

open BitProgram StructuredCalls PackingProgramSupport

def plansState (p : Params) (regs : Fin 16 → Bool) : Data :=
  ⟨regs,fun i => if i=25 then p.planStream else (PackingProgram.inputState p.input regs).stacks i⟩

def labelsState (p : Params) (regs : Fin 16 → Bool) : Data :=
  ⟨regs,fun i => if i=26 then p.labelStream else (PackingProgram.inputState p.input regs).stacks i⟩

private theorem plans_call_stacks (p : Params) (regs : Fin 16 → Bool) (rs : Fin 13 → Bool) :
    (install (by decide : 13 ≤ 16) (by decide : 25 ≤ 48)
      (PackingPlumbing.run PackingProgram.plansSetup (PackingProgram.inputState p.input regs))
      (SubexpPlanAlphabetBase.data rs p.D p.Δ p.scopes
        (List.replicate p.D true) [] p.planStream [])).stacks = fun i =>
      if i=16 then SubexpPlanAlphabetBase.scopeBytes p.scopes
      else if i=17 then List.replicate p.D true
      else if i=18 then List.replicate p.Δ true
      else if i=20 then List.replicate p.D true
      else if i=24 then p.planStream
      else (PackingProgram.inputState p.input regs).stacks i := by
  funext i
  fin_cases i <;> simp [Fin.coe_ofNat_eq_mod,install,PackingPlumbing.run,PackingPlumbing.Op.next,
    PackingProgram.plansSetup,StackRoutines.copyStacks,PackingProgram.inputState,
    SubexpPlanAlphabetBase.data,Params.input]

private theorem labels_call_stacks (p : Params) (regs : Fin 16 → Bool) (rs : Fin 8 → Bool) :
    (install (by decide : 8 ≤ 16) (by decide : 15 ≤ 48)
      (PackingPlumbing.run PackingProgram.labelsSetup (plansState p regs))
      (PackingVertexLabels.state rs p.rows.flatten [] p.width [] [] []
        (List.replicate p.D true) p.labelStream [])).stacks = fun i =>
      if i=0 then p.rows.flatten else if i=3 then p.width
      else if i=12 then List.replicate p.D true else if i=13 then p.labelStream
      else (PackingProgram.inputState p.input regs).stacks i := by
  funext i
  fin_cases i <;> simp [Fin.coe_ofNat_eq_mod,install,PackingPlumbing.run,PackingPlumbing.Op.next,
    PackingProgram.labelsSetup,PackingPlumbing.move,
    StackRoutines.copyStacks,StackRoutines.transferStacks,
    PackingProgram.inputState,PackingVertexLabels.state,plansState,Params.input]

private theorem types_call_stacks (p : Params) (regs : Fin 16 → Bool) (rs : Fin 10 → Bool) :
    (install (by decide : 10 ≤ 16) (by decide : 9 ≤ 48)
      (PackingPlumbing.run PackingProgram.typesSetup (labelsState p regs))
      (UniversalTypeProgram.outputState p.alphabet p.typeRows rs)).stacks = fun i =>
      if i=0 then p.typeStream else if i=1 then ProgramEncoding.encodeRecords p.alphabet
      else if i=5 then [false] else if i=26 then p.labelStream
      else (PackingProgram.inputState p.input regs).stacks i := by
  funext i
  fin_cases i <;> simp [Fin.coe_ofNat_eq_mod,install,PackingPlumbing.run,PackingPlumbing.Op.next,
    PackingProgram.typesSetup,StackRoutines.copyStacks,PackingProgram.inputState,
    UniversalTypeProgram.outputState,labelsState,Params.input,Params.typeStream]

theorem plans_eval (p : Params) (regs : Fin 16 → Bool)
    (hd : ∀ v : Fin p.D, IncidencePlanSpec.degree p.scopes v.val ≤ p.Δ) :
    ∃ (n : ℕ) (rf : Fin 16 → Bool), n ≤ p.plansBound ∧
      Eval PackingProgram.plans n (PackingProgram.inputState p.input regs) (plansState p rf) := by
  let a := PackingProgram.inputState p.input regs
  let b := PackingPlumbing.run PackingProgram.plansSetup a
  have hv : PackingPlumbing.Valid PackingProgram.plansSetup a := by
    simp [PackingProgram.plansSetup,PackingPlumbing.Valid,PackingPlumbing.Op.Valid,
      PackingPlumbing.Op.next,StackRoutines.copyStacks,a,PackingProgram.inputState]
  have hsetup := PackingPlumbing.eval PackingProgram.plansSetup a hv
  have hsetupCost : PackingPlumbing.cost PackingProgram.plansSetup a =
      7*((SubexpPlanAlphabetBase.scopeBytes p.scopes).length+p.D+p.Δ)+15 := by
    simp [PackingPlumbing.cost,PackingPlumbing.Op.cost,PackingPlumbing.Op.next,
      PackingProgram.plansSetup,a,PackingProgram.inputState,Params.input,StackRoutines.copyStacks]
    ring
  rw [hsetupCost] at hsetup
  have hproject : project (by decide : 13 ≤ 16) (by decide : 25 ≤ 48) b =
      SubexpPlanAlphabetBase.data (b.regs ∘ registers (by decide)) p.D p.Δ p.scopes [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [b,a,stackPorts,PackingPlumbing.run,PackingPlumbing.Op.next,
      PackingProgram.plansSetup,StackRoutines.copyStacks,PackingProgram.inputState,Params.input
]
  obtain ⟨n,rs,hn,ht⟩ := SubexpPlanAlphabetBase.program_trace
    (b.regs ∘ registers (by decide)) p.D p.Δ p.scopes hd
  rw [← hproject] at ht
  let inner := SubexpPlanAlphabetBase.data rs p.D p.Δ p.scopes
    (List.replicate p.D true) [] p.planStream []
  let c := install (by decide : 13 ≤ 16) (by decide : 25 ≤ 48) b inner
  have hcall : Eval PackingProgram.plansCall n b c :=
    lowCall_eval SubexpPlanAlphabetBase.program (by decide) (by decide) b inner ht
  have hc : c.stacks = fun i =>
      if i=16 then SubexpPlanAlphabetBase.scopeBytes p.scopes
      else if i=17 then List.replicate p.D true
      else if i=18 then List.replicate p.Δ true
      else if i=20 then List.replicate p.D true
      else if i=24 then p.planStream
      else (PackingProgram.inputState p.input regs).stacks i := plans_call_stacks p regs rs
  have hsaveValid : PackingPlumbing.Valid PackingProgram.plansSave c := by
    simp [PackingProgram.plansSave,PackingPlumbing.move,PackingPlumbing.Valid,PackingPlumbing.Op.Valid]
  have hsave := PackingPlumbing.eval PackingProgram.plansSave c hsaveValid
  let d := PackingPlumbing.run PackingProgram.plansSave c
  have hdstate : d = plansState p d.regs := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [d,PackingPlumbing.run,PackingPlumbing.Op.next,
      PackingProgram.plansSave,PackingPlumbing.move,
      StackRoutines.transferStacks,StackRoutines.clearStacks,hc,
      PackingProgram.inputState]
  have hsaveCost : PackingPlumbing.cost PackingProgram.plansSave c =
      6*p.planStream.length+2*(SubexpPlanAlphabetBase.scopeBytes p.scopes).length+4*p.D+2*p.Δ+18 := by
    simp [PackingPlumbing.cost,PackingPlumbing.Op.cost,PackingPlumbing.Op.next,
      PackingProgram.plansSave,PackingPlumbing.move,hc,PackingProgram.inputState,
      StackRoutines.transferStacks,StackRoutines.clearStacks]
    ring
  rw [hsaveCost] at hsave
  change Eval _ _ c d at hsave
  rw [hdstate] at hsave
  refine ⟨_,d.regs,?_,hsetup.seq (hcall.seq hsave)⟩
  dsimp [Params.plansBound]
  omega

theorem planList_valid (p : Params)
    (hd : ∀ v : Fin p.D, IncidencePlanSpec.degree p.scopes v.val ≤ p.Δ)
    (hcount : p.rows.length=p.scopes.length+(p.Δ+1)*p.D) :
    ∀ plan ∈ p.planList, ∀ i ∈ plan, i < p.rows.length := by
  intro plan hp i hi
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hp
  rw [hcount]
  exact IncidencePlanSpec.vertexPlan_valid p.D p.Δ p.scopes hd v i hi

theorem labels_eval (p : Params) (regs : Fin 16 → Bool)
    (hrows : ∀ row ∈ p.rows, row.length=p.width.length)
    (hplans : ∀ plan ∈ p.planList, ∀ i ∈ plan, i < p.rows.length) :
    ∃ (n : ℕ) (rf : Fin 16 → Bool), n ≤ p.labelsBound ∧
      Eval PackingProgram.labels n (plansState p regs) (labelsState p rf) := by
  let a := plansState p regs
  let b := PackingPlumbing.run PackingProgram.labelsSetup a
  have hv : PackingPlumbing.Valid PackingProgram.labelsSetup a := by
    simp [PackingProgram.labelsSetup,PackingPlumbing.move,PackingPlumbing.Valid,PackingPlumbing.Op.Valid,
      PackingPlumbing.Op.next,StackRoutines.copyStacks,a,plansState,PackingProgram.inputState]
  have hsetup := PackingPlumbing.eval PackingProgram.labelsSetup a hv
  have hsetupCost : PackingPlumbing.cost PackingProgram.labelsSetup a =
      7*p.rows.flatten.length+7*p.width.length+6*p.planStream.length+16 := by
    simp [PackingPlumbing.cost,PackingPlumbing.Op.cost,PackingPlumbing.Op.next,
      PackingProgram.labelsSetup,PackingPlumbing.move,a,plansState,PackingProgram.inputState,
      Params.input,StackRoutines.copyStacks,StackRoutines.transferStacks]
    ring
  rw [hsetupCost] at hsetup
  have hproject : project (by decide : 8 ≤ 16) (by decide : 15 ≤ 48) b =
      PackingVertexLabels.state (b.regs ∘ registers (by decide)) p.rows.flatten [] p.width []
        p.planStream [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [b,a,stackPorts,PackingPlumbing.run,PackingPlumbing.Op.next,
      PackingProgram.labelsSetup,PackingPlumbing.move,StackRoutines.copyStacks,StackRoutines.transferStacks,
      PackingProgram.inputState,plansState,Params.input]
  obtain ⟨n,rs,hn,ht⟩ := PackingVertexLabels.program_trace p.rows p.width p.planList
    (b.regs ∘ registers (by decide)) 0 [] [] hrows hplans
  have hinput : PackingVertexLabels.state (b.regs ∘ registers (by decide)) p.rows.flatten [] p.width []
      (ProgramEncoding.encodeRecords (p.planList.map PackingVertexLabels.planPayload) ++ []) []
      (List.replicate 0 true) [] [] = project (by decide : 8 ≤ 16) (by decide : 15 ≤ 48) b := by
    rw [hproject,← p.planStream_eq]
    simp only [List.append_nil,List.replicate_zero]
  rw [hinput] at ht
  let inner := PackingVertexLabels.state rs p.rows.flatten [] p.width [] [] []
    (List.replicate p.D true) p.labelStream []
  let c := install (by decide : 8 ≤ 16) (by decide : 15 ≤ 48) b inner
  have ht' : Trace PackingVertexLabels.program n
      ((project (by decide : 8 ≤ 16) (by decide : 15 ≤ 48) b).withPC (some PackingVertexLabels.program.entry))
      (inner.withPC none) := by
    simpa only [inner,Params.labelStream,Nat.zero_add,Params.planList_length,List.append_nil] using ht
  have hcall : Eval PackingProgram.labelsCall n b c :=
    lowCall_eval PackingVertexLabels.program (by decide) (by decide) b inner ht'
  have hc : c.stacks = fun i =>
      if i=0 then p.rows.flatten else if i=3 then p.width
      else if i=12 then List.replicate p.D true else if i=13 then p.labelStream
      else (PackingProgram.inputState p.input regs).stacks i := labels_call_stacks p regs rs
  have hsaveValid : PackingPlumbing.Valid PackingProgram.labelsSave c := by
    simp [PackingProgram.labelsSave,PackingPlumbing.move,PackingPlumbing.Valid,PackingPlumbing.Op.Valid]
  have hsave := PackingPlumbing.eval PackingProgram.labelsSave c hsaveValid
  let d := PackingPlumbing.run PackingProgram.labelsSave c
  have hdstate : d = labelsState p d.regs := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [d,PackingPlumbing.run,PackingPlumbing.Op.next,
      PackingProgram.labelsSave,PackingPlumbing.move,
      StackRoutines.transferStacks,StackRoutines.clearStacks,hc,
      PackingProgram.inputState]
  have hsaveCost : PackingPlumbing.cost PackingProgram.labelsSave c =
      6*p.labelStream.length+2*p.rows.flatten.length+2*p.width.length+2*p.D+15 := by
    simp [PackingPlumbing.cost,PackingPlumbing.Op.cost,PackingPlumbing.Op.next,
      PackingProgram.labelsSave,PackingPlumbing.move,hc,PackingProgram.inputState,
      StackRoutines.transferStacks,StackRoutines.clearStacks]
    ring
  rw [hsaveCost] at hsave
  change Eval _ _ c d at hsave
  rw [hdstate] at hsave
  refine ⟨_,d.regs,?_,hsetup.seq (hcall.seq hsave)⟩
  dsimp [Params.labelsBound]
  omega

theorem types_eval (p : Params) (regs : Fin 16 → Bool) :
    ∃ (n : ℕ) (rf : Fin 16 → Bool), n ≤ p.typesBound ∧
      Eval PackingProgram.types n (labelsState p regs)
        (PackingProgram.frontendOutputState p.input p.labelStream p.typeStream rf) := by
  let a := labelsState p regs
  let b := PackingPlumbing.run PackingProgram.typesSetup a
  have hv : PackingPlumbing.Valid PackingProgram.typesSetup a := by
    simp [PackingProgram.typesSetup,PackingPlumbing.Valid,PackingPlumbing.Op.Valid,
      PackingPlumbing.Op.next,StackRoutines.copyStacks,a,labelsState,PackingProgram.inputState]
  have hsetup := PackingPlumbing.eval PackingProgram.typesSetup a hv
  have hsetupCost : PackingPlumbing.cost PackingProgram.typesSetup a =
      7*(ProgramEncoding.encodeRecords p.alphabet).length+7*p.Δ+10 := by
    simp [PackingPlumbing.cost,PackingPlumbing.Op.cost,PackingPlumbing.Op.next,
      PackingProgram.typesSetup,a,labelsState,PackingProgram.inputState,Params.input,StackRoutines.copyStacks]
    ring
  rw [hsetupCost] at hsetup
  have hproject : project (by decide : 10 ≤ 16) (by decide : 9 ≤ 48) b =
      UniversalTypeProgram.inputState p.alphabet (List.replicate p.Δ true)
        (b.regs ∘ registers (by decide)) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [b,a,stackPorts,PackingPlumbing.run,PackingPlumbing.Op.next,
      PackingProgram.typesSetup,StackRoutines.copyStacks,PackingProgram.inputState,labelsState,
      Params.input]
  obtain ⟨rs,n,hn,ht⟩ := UniversalTypeProgram.program_runsIn p.alphabet (List.replicate p.Δ true)
    (b.regs ∘ registers (by decide))
  rw [← hproject] at ht
  simp only [List.length_replicate] at hn ht
  let inner := UniversalTypeProgram.outputState p.alphabet p.typeRows rs
  let c := install (by decide : 10 ≤ 16) (by decide : 9 ≤ 48) b inner
  have hcall : Eval PackingProgram.typesCall n b c :=
    lowCall_eval UniversalTypeProgram.program (by decide) (by decide) b inner ht
  have hc : c.stacks = fun i =>
      if i=0 then p.typeStream else if i=1 then ProgramEncoding.encodeRecords p.alphabet
      else if i=5 then [false] else if i=26 then p.labelStream
      else (PackingProgram.inputState p.input regs).stacks i := types_call_stacks p regs rs
  have hsaveValid : PackingPlumbing.Valid PackingProgram.typesSave c := by
    simp [PackingProgram.typesSave,PackingPlumbing.move,PackingPlumbing.Valid,PackingPlumbing.Op.Valid]
  have hsave := PackingPlumbing.eval PackingProgram.typesSave c hsaveValid
  let d := PackingPlumbing.run PackingProgram.typesSave c
  have hdstate : d = PackingProgram.frontendOutputState p.input p.labelStream p.typeStream d.regs := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [d,PackingPlumbing.run,PackingPlumbing.Op.next,
      PackingProgram.typesSave,PackingPlumbing.move,
      StackRoutines.transferStacks,StackRoutines.clearStacks,hc,
      PackingProgram.inputState]
  have hsaveCost : PackingPlumbing.cost PackingProgram.typesSave c =
      6*p.typeStream.length+2*(ProgramEncoding.encodeRecords p.alphabet).length+14 := by
    simp [PackingPlumbing.cost,PackingPlumbing.Op.cost,PackingPlumbing.Op.next,
      PackingProgram.typesSave,PackingPlumbing.move,hc,PackingProgram.inputState,
      StackRoutines.transferStacks,StackRoutines.clearStacks]
    ring
  rw [hsaveCost] at hsave
  change Eval _ _ c d at hsave
  rw [hdstate] at hsave
  refine ⟨_,d.regs,?_,hsetup.seq (hcall.seq hsave)⟩
  dsimp [Params.typesBound]
  omega

/-- Execution of the existing fixed controller, with all six masters retained
and every non-output work stack empty. -/
theorem frontend_eval (p : Params) (regs : Fin 16 → Bool)
    (hd : ∀ v : Fin p.D, IncidencePlanSpec.degree p.scopes v.val ≤ p.Δ)
    (hrows : ∀ row ∈ p.rows, row.length=p.width.length)
    (hcount : p.rows.length=p.scopes.length+(p.Δ+1)*p.D) :
    ∃ (n : ℕ) (rf : Fin 16 → Bool), n ≤ p.bound ∧
      Eval PackingProgram.frontend n (PackingProgram.inputState p.input regs)
        (PackingProgram.frontendOutputState p.input p.labelStream p.typeStream rf) := by
  obtain ⟨np,rp,hp,ep⟩ := plans_eval p regs hd
  obtain ⟨nl,rl,hl,el⟩ := labels_eval p rp hrows (planList_valid p hd hcount)
  obtain ⟨nt,rt,ht,et⟩ := types_eval p rl
  have e := ep.seq (el.seq (et.seq (.base (.skip _))))
  refine ⟨np+(nl+(nt+0)),rt,?_,e⟩
  dsimp [Params.bound]
  omega

def program := compiled PackingProgram.frontend 40 26

theorem program_trace (p : Params) (regs : Fin 16 → Bool)
    (hd : ∀ v : Fin p.D, IncidencePlanSpec.degree p.scopes v.val ≤ p.Δ)
    (hrows : ∀ row ∈ p.rows, row.length=p.width.length)
    (hcount : p.rows.length=p.scopes.length+(p.Δ+1)*p.D) :
    ∃ (n : ℕ) (rf : Fin 16 → Bool), n ≤ p.bound+1 ∧
      Trace program n ((PackingProgram.inputState p.input regs).withPC (some program.entry))
        ((PackingProgram.frontendOutputState p.input p.labelStream p.typeStream rf).withPC none) := by
  obtain ⟨n,rf,hn,he⟩ := frontend_eval p regs hd hrows hcount
  exact ⟨n+1,rf,by omega,compiled_halt_trace he 40 26⟩

theorem program_primitive (p : Params) (regs : Fin 16 → Bool)
    (hd : ∀ v : Fin p.D, IncidencePlanSpec.degree p.scopes v.val ≤ p.Δ)
    (hrows : ∀ row ∈ p.rows, row.length=p.width.length)
    (hcount : p.rows.length=p.scopes.length+(p.Δ+1)*p.D) :
    ∃ rf, Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * (p.bound+1))
      (BitProgram.primitiveCfg program
        ((PackingProgram.inputState p.input regs).withPC (some program.entry)))
      (BitProgram.primitiveCfg program
        ((PackingProgram.frontendOutputState p.input p.labelStream p.typeStream rf).withPC none)) := by
  obtain ⟨n,rf,hn,he⟩ := program_trace p regs hd hrows hcount
  exact ⟨rf,BitProgram.primitive_execution program ⟨n,hn,he⟩⟩

theorem canonical_typeStream (p : Params) (r Q : ℕ)
    (ha : p.alphabet=AssignmentAlphabetSemantics.wordBytes r Q) :
    p.typeStream = ProgramEncoding.encodeRecords (TypeEnumeration.universalBytes r Q p.Δ) := by
  simp only [Params.typeStream,Params.typeRows,ha,TypeEnumeration.universalBytes]

end SubexponentialSAT.Subexp.PackingFrontend

end OAI.Algorithms
