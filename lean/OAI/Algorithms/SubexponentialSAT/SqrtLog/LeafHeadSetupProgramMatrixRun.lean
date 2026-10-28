import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramHead
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramSource

namespace OAI.Algorithms

/-! The all-row entry cache is physically copied into the complete matrix
bank, and the actual controller table is copied out as the next head alphabet. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def matrixBase (a : Data) : Fin 288 → List Bool := fun i =>
  if i=0 then a.stacks 141 else if i=17 then a.stacks 650 else if i=18 then a.stacks 128 else
  if i=23 then a.stacks 651 else if i=225 then a.stacks 135 else if i=226 then a.stacks 136 else
  if i=227 then a.stacks 640 else if i=228 then a.stacks 641 else if i=229 then a.stacks 140 else
  if i=230 then a.stacks 642 else if i=231 then a.stacks 138 else if i=232 then a.stacks 139 else
  if i=233 then a.stacks 130 else if i=234 then a.stacks 131 else if i=235 then a.stacks 307 else
  if i=236 then a.stacks 132 else []

theorem matrix_prepared (a : Data) (D : ℕ) (hD : a.stacks 647=List.replicate D true) :
    projectState id (workPort (by decide)) (prepared (by decide) matrixInputs a)=
      LayoutMatrixProgram.initialState (matrixBase a) (prepared (by decide) matrixInputs a).regs D := by
  apply prepared_eq id (by decide) matrixInputs a _ matrixInputs_protected (by decide)
  · intro j; rfl
  · intro p hp
    simp only [matrixInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [LayoutMatrixProgram.initialState,LayoutMatrixProgram.state,matrixBase,hD]
  · intro j hj
    simp only [matrixInputs,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] at hj
    rcases hj with ⟨h0,h17,h18,h23,h225,h226,h227,h228,h229,h230,h231,h232,h233,h234,h235,h236,h281⟩
    simp [LayoutMatrixProgram.initialState,LayoutMatrixProgram.state,matrixBase, *]


abbrev MatrixExecution (entry : Cmd 16 256) (a : Data) (D n : ℕ) (js : List ℕ)
    (T B : ℕ) (rows : List (List LayoutMatrixProgram.Pair))
    (ys : List (List (List Bool))) (b : State 16 288) : Prop :=
  RunsIn (Matrix.program entry)
    (LayoutMatrixProgram.commandCost T B D n js+BucketProgram.preMatrixCost (a.stacks 141) rows+
      BucketProgram.Controller.cost (a.stacks 141) ys js n js.length+3)
    ((LayoutMatrixProgram.initialState (matrixBase a)
      (prepared (by decide) matrixInputs a).regs D).withPC (some (Matrix.program entry).entry))
    (b.withPC none)

theorem matrixBuckets_eval (entry : Cmd 16 256) (a : Data) (D n : ℕ) (js : List ℕ)
    (hD : a.stacks 647=List.replicate D true)
    (hn : a.stacks 128=List.replicate n true)
    (hi : a.stacks 650=HeadScatterProgram.indices js)
    (hh : a.stacks 651=List.replicate js.length false)
    (hjs : ∀ v∈js,v < n)
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop) (T B : ℕ)
    (hc : LayoutMatrixProgram.EntryContract entry (matrixBase a) Valid Rel T B)
    (hv : ∀ j < D,∀ v∈js,Valid j v) :
    ∃ rows ys b t e,
      LayoutMatrixProgram.MatrixRel Rel B D js rows ∧
      List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (a.stacks 141))) rows ys ∧
      t ≤ stageCost id (by decide) matrixInputs matrixOutputs a b
        (LayoutMatrixProgram.commandCost T B D n js+BucketProgram.preMatrixCost (a.stacks 141) rows+
          BucketProgram.Controller.cost (a.stacks 141) ys js n js.length+3) ∧
      Eval (matrixBuckets entry) t a e ∧
      e=returned id (by decide) matrixInputs matrixOutputs a b ∧
      e.stacks 669=BucketTupleProgram.Table.tableBits
        (BucketTupleProgram.actualBuckets (a.stacks 141) ys js n js.length) ∧
      (∀ i,Protected i→i≠669→e.stacks i=a.stacks i) ∧
      MatrixExecution entry a D n js T B rows ys b := by
  let regs := (prepared (by decide) matrixInputs a).regs
  have hb : ∀ i : Fin 25,matrixBase a (LayoutMatrixProgram.controllerPorts i)=
      (BucketProgram.Controller.signedInitial (regs ∘ LayoutMatrixProgram.controllerRegs)
        (a.stacks 141) [] js n js.length).stacks i := by
    intro i
    fin_cases i <;> simp [matrixBase,LayoutMatrixProgram.controllerPorts,
      BucketProgram.Controller.signedInitial,BucketProgram.Controller.wideState,
      HeadScatterProgram.unary,hn,hi,hh,SubexponentialSAT.Subexp.MatrixProgramSupport.words]
  obtain ⟨rows,ys,b,hr,hy,⟨t,ht,he⟩,hout⟩ := Matrix.program_runsIn entry (matrixBase a)
    (by simp [matrixBase]) (by simp [matrixBase]) Valid Rel T B hc D n js
    (by simpa [matrixBase,LayoutMatrixProgram.ids_eq_indices] using hi)
    hv hjs regs (a.stacks 141) hb
  have hs := stage_eval (Matrix.program entry) id Function.injective_id (by decide)
    matrixInputs matrixOutputs a _ b matrixInputs_protected matrixOutputs_protected
    (matrix_prepared a D hD) he
  let e := returned id (by decide) matrixInputs matrixOutputs a b
  have ho : e.stacks 669=b.stacks 21 := returned_word id (by decide)
    matrixInputs matrixOutputs a b matrixOutputs_protected (by decide) (21,669) (by simp [matrixOutputs])
  refine ⟨rows,ys,b,_,e,hr,hy,?_,hs,rfl,?_,?_,?_⟩
  · unfold stageCost
    omega
  · rw [ho,hout,BucketTupleProgram.actualBuckets_bytes]
  · intro i hi hn
    apply returned_frame id (by decide) matrixInputs matrixOutputs a b i hi
    intro p hp
    simp only [matrixOutputs,List.mem_singleton] at hp
    subst p
    exact hn

  · exact ⟨t,ht,he⟩

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end
end OAI.Algorithms
