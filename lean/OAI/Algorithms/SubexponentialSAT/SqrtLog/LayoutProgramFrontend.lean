import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingFrontend

namespace OAI.Algorithms

/-! The physical label/type frontend for arbitrary runtime incidence plans.
The plans have already been produced by the native incidence scan. This
frontend gathers their actual words and generates the complete type alphabet;
it does not accept label records or block metadata as input. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.NativeFrontend

open SubexponentialSAT.Subexp SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.PackingProgramSupport

structure Params where
  D : ℕ
  Δ : ℕ
  rows : List (List Bool)
  width : List Bool
  alphabet : List (List Bool)
  planList : List (List ℕ)
  plans_count : planList.length = D

namespace Params

def base (p : Params) : PackingFrontend.Params :=
  ⟨p.D,p.Δ,[],p.rows,p.width,p.alphabet⟩
def input (p : Params) : PackingProgram.Input := p.base.input

def planStream (p : Params) : List Bool :=
  ProgramEncoding.encodeRecords (p.planList.map PackingVertexLabels.planPayload)
def labelStream (p : Params) : List Bool :=
  BucketProgram.encodeRecords (PackingVertexLabels.labelRecords p.rows p.planList 0).reverse
def typeRows (p : Params) : List (List Bool) :=
  TupleProgram.powerRows p.alphabet (p.Δ+1) [[]]
def typeStream (p : Params) : List Bool := ProgramEncoding.encodeRecords p.typeRows
@[simp] theorem planList_length (p : Params) : p.planList.length = p.D := p.plans_count
theorem planStream_eq (p : Params) :
    p.planStream = ProgramEncoding.encodeRecords (p.planList.map PackingVertexLabels.planPayload) := rfl

def labelsBound (p : Params) : ℕ :=
  PackingVertexLabels.traceCost p.width.length p.planList 0+
    9*p.rows.flatten.length+9*p.width.length+6*p.planStream.length+6*p.labelStream.length+2*p.D+31
def typesBound (p : Params) : ℕ :=
  UniversalTypeProgram.budget p.alphabet p.Δ+
    9*(ProgramEncoding.encodeRecords p.alphabet).length+7*p.Δ+6*p.typeStream.length+24

end Params

def plansState (p : Params) (regs : Fin 16 → Bool) : Data :=
  ⟨regs,fun i => if i=25 then p.planStream else (PackingProgram.inputState p.input regs).stacks i⟩

def labelsState (p : Params) (regs : Fin 16 → Bool) : Data :=
  ⟨regs,fun i => if i=26 then p.labelStream else (PackingProgram.inputState p.input regs).stacks i⟩

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
    PackingProgram.inputState,PackingVertexLabels.state,plansState,Params.input,Params.base,PackingFrontend.Params.input,Params.base,PackingFrontend.Params.input]

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
    UniversalTypeProgram.outputState,labelsState,Params.input,Params.base,PackingFrontend.Params.input,Params.typeStream]

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
      Params.input,Params.base,PackingFrontend.Params.input,StackRoutines.copyStacks,StackRoutines.transferStacks]
    ring
  rw [hsetupCost] at hsetup
  have hproject : project (by decide : 8 ≤ 16) (by decide : 15 ≤ 48) b =
      PackingVertexLabels.state (b.regs ∘ registers (by decide)) p.rows.flatten [] p.width []
        p.planStream [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [b,a,stackPorts,PackingPlumbing.run,PackingPlumbing.Op.next,
      PackingProgram.labelsSetup,PackingPlumbing.move,StackRoutines.copyStacks,StackRoutines.transferStacks,
      PackingProgram.inputState,plansState,Params.input,Params.base,PackingFrontend.Params.input]
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
      PackingProgram.typesSetup,a,labelsState,PackingProgram.inputState,Params.input,Params.base,PackingFrontend.Params.input,StackRoutines.copyStacks]
    ring
  rw [hsetupCost] at hsetup
  have hproject : project (by decide : 10 ≤ 16) (by decide : 9 ≤ 48) b =
      UniversalTypeProgram.inputState p.alphabet (List.replicate p.Δ true)
        (b.regs ∘ registers (by decide)) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [b,a,stackPorts,PackingPlumbing.run,PackingPlumbing.Op.next,
      PackingProgram.typesSetup,StackRoutines.copyStacks,PackingProgram.inputState,labelsState,
      Params.input,Params.base,PackingFrontend.Params.input]
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


abbrev command : Cmd 16 48 := .seq PackingProgram.labels PackingProgram.types
def program := compiled command 25 26

theorem program_trace (p : Params) (regs : Fin 16 → Bool)
    (hrows : ∀ row ∈ p.rows, row.length = p.width.length)
    (hplans : ∀ plan ∈ p.planList, ∀ i ∈ plan, i < p.rows.length) :
    ∃ steps ≤ p.labelsBound+p.typesBound+1, ∃ rf,
      Trace program steps ((plansState p regs).withPC (some program.entry))
        ((PackingProgram.frontendOutputState p.input p.labelStream p.typeStream rf).withPC none) := by
  obtain ⟨nl,rl,hl,el⟩ := labels_eval p regs hrows hplans
  obtain ⟨nt,rt,ht,et⟩ := types_eval p rl
  exact ⟨nl+nt+1,by omega,rt,compiled_halt_trace (el.seq et) 25 26⟩

end SubexponentialSAT.SqrtLog.LayoutProgram.NativeFrontend

end OAI.Algorithms
