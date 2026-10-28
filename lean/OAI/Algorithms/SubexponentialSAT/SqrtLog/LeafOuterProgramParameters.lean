import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramBase
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramStage

namespace OAI.Algorithms

/-! The actual outer-leaf parameter stage: input copies, native arithmetic,
output copies, and complete worker cleanup, with every command charged. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls BinaryArithmetic
open LeafParametersProgram.Bank

/-- All 768 reusable worker stacks are empty. -/
def WorkerEmpty (a : Data) : Prop := ∀ i : Fin 768, a.stacks (workerStack i) = []

def binaryMetadataPort (j : Fin 7) : Fin 896 := ⟨801+j.val, by omega⟩
def unaryMetadataPort (j : Fin 7) : Fin 896 := ⟨808+j.val, by omega⟩

/-- Persisted search metadata. The seven indexed values are D,t,tD,d,r,rD,N. -/
structure Metadata (m B : ℕ) (a : Data) : Prop where
  q : BinaryArithmetic.toNat (a.stacks 800) = SparseCode.gapDenom m B
  binary : ∀ j, BinaryArithmetic.toNat (a.stacks (binaryMetadataPort j)) = CodeParametersProgram.parameterValues m B j
  unary : ∀ j, a.stacks (unaryMetadataPort j) =
    List.replicate (CodeParametersProgram.parameterValues m B j) true

private def inputWords (a : Data) : Words :=
  fun i => if i=0 then a.stacks 782 else if i=1 then a.stacks 786 else []

private theorem input_projection (a : Data) (he : WorkerEmpty a) :
    projectState regs8 stacks77 (routesState parameterInputs a) =
      state ((projectState regs8 stacks77 (routesState parameterInputs a)).regs) (inputWords a) := by
  apply CounterForPrograms.data_ext
    (a := projectState regs8 stacks77 (routesState parameterInputs a))
    (b := state ((projectState regs8 stacks77 (routesState parameterInputs a)).regs) (inputWords a)) rfl
  funext i
  have hemp : a.stacks (stacks77 i) = [] := he ⟨i.val, by omega⟩
  by_cases h0 : i.val=0
  · have hi : i=0 := Fin.ext h0
    subst i
    simp [projectState,parameterInputs,routesState,routed,stacks77,state,inputWords]
  by_cases h1 : i.val=1
  · have hi : i=1 := Fin.ext h1
    subst i
    simp [projectState,parameterInputs,routesState,routed,stacks77,state,inputWords]
  have hn0 : stacks77 i ≠ 0 := by intro h; apply h0; exact congrArg Fin.val h
  have hn1 : stacks77 i ≠ 1 := by intro h; apply h1; exact congrArg Fin.val h
  change (routesState parameterInputs a).stacks (stacks77 i) = _
  rw [routes_frame parameterInputs a (stacks77 i) (by
    intro p hp
    simp only [parameterInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl
    · exact Ne.symm hn0
    · exact Ne.symm hn1)]
  rw [hemp]
  by_cases h64 : i.val < 64
  · have hz : (⟨i.val,h64⟩ : Fin 64) ≠ 0 := by
      intro h; apply h0; exact congrArg Fin.val h
    have ho : (⟨i.val,h64⟩ : Fin 64) ≠ 1 := by
      intro h; apply h1; exact congrArg Fin.val h
    simp only [state,dite_eq_left h64,inputWords,ite_eq_right hz,ite_eq_right ho]
  · simp only [state,dite_eq_right h64]

private theorem input_shape (a : Data) {m B : ℕ}
    (hm : BinaryArithmetic.toNat (a.stacks 782)=m) (hB : BinaryArithmetic.toNat (a.stacks 786)=B) :
    LeafParametersProgram.Circuit.Shape
      (CodeParametersProgram.initialModel m B (a.stacks 782).length (a.stacks 786).length)
      (inputWords a) := by
  constructor <;> intro i <;> by_cases h0 : i=0 <;> by_cases h1 : i=1 <;>
    simp [inputWords,CodeParametersProgram.initialModel,h0,h1,hm,hB]

private theorem saved_parameter (a : Data) (out : State 8 77) (p : Route)
    (hp : p ∈ parameterOutputs) :
    (routesState parameterOutputs (stageReturned parameterInputs regs8 stacks77 a out)).stacks p.2 =
      (stageReturned parameterInputs regs8 stacks77 a out).stacks p.1 := by
  simp only [parameterOutputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [parameterOutputs,routesState,routed]

private theorem result_parameter (a : Data) (r : Regs) (w : Words)
    (src : Fin 64) (dst : Fin 896) (hdst : 768 ≤ dst.val)
    (hp : (stacks77 (port src),dst) ∈ parameterOutputs) :
    (stageResult parameterInputs parameterOutputs regs8 stacks77 a (state r w)).stacks dst = w src := by
  rw [stageResult,clearWorker_frame _ dst hdst]
  change (routesState parameterOutputs (stageReturned parameterInputs regs8 stacks77 a (state r w))).stacks dst = _
  rw [saved_parameter a (state r w) _ hp]
  exact (embedState_stack regs8 stacks77 (routesState parameterInputs a) (state r w)
    (Fin.castAdd_injective 77 819) (port src)).trans (state_port r w src)

private theorem result_q (a : Data) (r : Regs) (w : Words) :
    (stageResult parameterInputs parameterOutputs regs8 stacks77 a (state r w)).stacks 800 = w 5 :=
  result_parameter a r w 5 800 (by decide) (by decide)

private theorem result_binary (a : Data) (r : Regs) (w : Words) (j : Fin 7) :
    (stageResult parameterInputs parameterOutputs regs8 stacks77 a (state r w)).stacks
      (binaryMetadataPort j) = w (CodeParametersProgram.binaryPorts j) := by
  apply result_parameter a r w (CodeParametersProgram.binaryPorts j) (binaryMetadataPort j)
  · simp only [binaryMetadataPort]; omega
  · fin_cases j <;> decide

private theorem result_unary (a : Data) (r : Regs) (w : Words) (j : Fin 7) :
    (stageResult parameterInputs parameterOutputs regs8 stacks77 a (state r w)).stacks
      (unaryMetadataPort j) = w (CodeParametersProgram.unaryPorts j) := by
  apply result_parameter a r w (CodeParametersProgram.unaryPorts j) (unaryMetadataPort j)
  · simp only [unaryMetadataPort]; omega
  · fin_cases j <;> decide

private theorem result_frame (a : Data) (out : State 8 77) (i : Fin 896)
    (hi : 768 ≤ i.val) (hout : i.val < 800 ∨ 814 < i.val) :
    (stageResult parameterInputs parameterOutputs regs8 stacks77 a out).stacks i = a.stacks i := by
  apply stageResult_frame _ _ _ _ _ _ i hi
  · intro p hp
    simp only [parameterInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl <;> intro h <;> have := congrArg Fin.val h <;> simp at this <;> omega
  · intro p hp
    have hb : 800 ≤ p.2.val ∧ p.2.val ≤ 814 := by
      simp only [parameterOutputs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    intro h
    have hv := congrArg Fin.val h
    omega
  · intro j h
    have hv := congrArg Fin.val h
    simp only [stacks77,Fin.val_castAdd] at hv
    omega

/-- Native parameter preparation on the actual outer-leaf machine. Its bound
includes input copies, arithmetic and unary generation, output copies, and
clearing every worker stack and register. No prepared-metadata premise occurs. -/
theorem parameters_eval (a : Data) {m B L : ℕ} (hm : 0 < m) (hB : 0 < B)
    (he : WorkerEmpty a) (hmv : BinaryArithmetic.toNat (a.stacks 782)=m) (hBv : BinaryArithmetic.toNat (a.stacks 786)=B)
    (hL : SubexpSetupStorage.WordBound L a) :
    ∃ n ≤ 10000*(L+CodeParametersProgram.fullBudget m B
      (a.stacks 782).length (a.stacks 786).length+2), ∃ b,
      Eval parameters n a b ∧ WorkerEmpty b ∧ (∀ i, b.regs i=false) ∧ Metadata m B b ∧
      (b.stacks 800).length ≤ (a.stacks 782).length+(a.stacks 786).length+11 ∧
      (b.stacks 801).length ≤ 4*(a.stacks 782).length+2*(a.stacks 786).length+30 ∧
      (∀ i : Fin 896, 768 ≤ i.val → (i.val < 800 ∨ 814 < i.val) → b.stacks i=a.stacks i) := by
  let r := (projectState regs8 stacks77 (routesState parameterInputs a)).regs
  obtain ⟨rf,w,hrun,_,hq,hbin,hun,hql,hDl⟩ :=
    CodeParametersProgram.program_runs_with_lengths hm hB
      (a.stacks 782).length (a.stacks 786).length r (inputWords a) (input_shape a hmv hBv)
  have hrun' : RunsIn CodeParametersProgram.program
      (CodeParametersProgram.fullBudget m B (a.stacks 782).length (a.stacks 786).length+1)
      ((projectState regs8 stacks77 (routesState parameterInputs a)).withPC
        (some CodeParametersProgram.program.entry)) ((state rf w).withPC none) := by
    rw [input_projection a he]
    exact hrun
  have ht : a.stacks 767=[] := he 767
  obtain ⟨n,hn,hnative⟩ := stage_bounded_eval parameterInputs parameterOutputs
    CodeParametersProgram.program regs8 stacks77 (Fin.castAdd_injective 8 32)
    (Fin.castAdd_injective 77 819) (by
      intro i h
      have hv := congrArg Fin.val h
      simp only [stacks77,Fin.val_castAdd] at hv
      have := i.isLt
      omega)
    parameterInputs_valid parameterOutputs_valid (by decide) (by decide)
    a L hL ht (state rf w) _ hrun'
  refine ⟨n,by omega,stageResult parameterInputs parameterOutputs regs8 stacks77 a (state rf w),
    hnative,?_,?_,?_,?_,?_,?_⟩
  · exact stageResult_empty _ _ _ _ _ _
  · intro i
    exact embedState_register id workerStack _ LeafProgram.Cleanup.Wide.blank Function.injective_id i
  · constructor
    · simpa only [result_q] using hq
    · intro j; simpa only [result_binary] using hbin j
    · intro j; simpa only [result_unary] using hun j
  · simpa only [result_q] using hql
  · have h := result_binary a rf w 0
    change (stageResult parameterInputs parameterOutputs regs8 stacks77 a (state rf w)).stacks 801 = w 9 at h
    rw [h]
    exact hDl
  · exact result_frame a (state rf w)

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
