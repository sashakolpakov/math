import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramStorage
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramExpand
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramFinalize

namespace OAI.Algorithms

/-! The attained-bucket Cartesian table is a physical persistent stream.
Each append and the final nested moments serialization is a real paid call. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def tupleInit : Code :=
  .seq (SubexponentialSAT.Subexp.TupleProgram.pushConst 660 0 false)
  (.seq (SubexponentialSAT.Subexp.TupleProgram.pushConst 660 0 false)
  (.seq (SubexponentialSAT.Subexp.TupleProgram.pushConst 660 0 true)
        (SubexponentialSAT.Subexp.TupleProgram.pushConst 665 0 false)))

def tupleInitialized (a : Data) : Data :=
  ⟨Function.update a.regs 0 false,
    Function.update (Function.update a.stacks 660 ([true,false,false]++a.stacks 660))
      665 (false::a.stacks 665)⟩

theorem tupleInit_eval (a : Data) : Eval tupleInit 8 a (tupleInitialized a) := by
  let b := SubexponentialSAT.Subexp.TupleProgram.pushedState (660 : Fin 768) (0 : Fin 16) false a
  let c := SubexponentialSAT.Subexp.TupleProgram.pushedState (660 : Fin 768) (0 : Fin 16) false b
  let d := SubexponentialSAT.Subexp.TupleProgram.pushedState (660 : Fin 768) (0 : Fin 16) true c
  have h := (SubexponentialSAT.Subexp.TupleProgram.pushConst_eval (660 : Fin 768) (0 : Fin 16) false a).seq
    ((SubexponentialSAT.Subexp.TupleProgram.pushConst_eval (660 : Fin 768) (0 : Fin 16) false b).seq
    ((SubexponentialSAT.Subexp.TupleProgram.pushConst_eval (660 : Fin 768) (0 : Fin 16) true c).seq
      (SubexponentialSAT.Subexp.TupleProgram.pushConst_eval (665 : Fin 768) (0 : Fin 16) false d)))
  convert h using 1
  · rfl
  · apply congrArg₂ StructuredProgram.State.mk
    · simp [d,c,b]
    · funext i
      by_cases h660 : i=660 <;> by_cases h665 : i=665 <;>
        simp_all [d,c,b,SubexponentialSAT.Subexp.TupleProgram.pushedState]

def tupleRegs : Fin 10 → Fin 16 := Fin.castAdd 6
def tupleInputs : List (Fin 768 × Fin 16) := [(660,0),(665,5),(669,9),(670,10),(671,11)]
def tupleOutputs : List (Fin 16 × Fin 768) := [(0,660)]
def appendHead : Code := stage BucketTupleProgram.Expand.program tupleRegs (by decide)
  tupleInputs tupleOutputs
theorem tupleInputs_protected : ∀ p∈tupleInputs,Protected p.1 := by simp [tupleInputs,Protected,temporary]
theorem tupleOutputs_protected : ∀ p∈tupleOutputs,Protected p.2 := by simp [tupleOutputs,Protected,temporary]

def tupleResult (a : Data) (regs : Fin 10 → Bool) (rows : List (List Bool))
    (mask context : List Bool) (bs : List BucketTupleProgram.Table.Bucket) : Data :=
  returned tupleRegs (by decide) tupleInputs tupleOutputs a
    (BucketTupleProgram.Expand.state regs (BucketTupleProgram.Expand.nextRows rows mask context bs)
      mask context [] [])
def tupleCost (a : Data) (regs : Fin 10 → Bool) (rows : List (List Bool))
    (mask context : List Bool) (bs : List BucketTupleProgram.Table.Bucket) : ℕ :=
  stageCost tupleRegs (by decide) tupleInputs tupleOutputs a
    (BucketTupleProgram.Expand.state regs (BucketTupleProgram.Expand.nextRows rows mask context bs)
      mask context [] []) (BucketTupleProgram.Expand.cost rows mask context bs+1)

theorem appendHead_eval (a : Data) (rows : List (List Bool))
    (mask context : List Bool) (bs : List BucketTupleProgram.Table.Bucket)
    (hr : a.stacks 660=ProgramEncoding.encodeRecords rows) (hmarker : a.stacks 665=[false])
    (ht : a.stacks 669=BucketTupleProgram.Table.tableBits bs)
    (hm : a.stacks 670=mask) (hc : a.stacks 671=context) :
    ∃ regs t,t ≤ tupleCost a regs rows mask context bs ∧
      Eval appendHead t a (tupleResult a regs rows mask context bs) := by
  let regs := (prepared (by decide) tupleInputs a).regs ∘ tupleRegs
  have hp : projectState tupleRegs (workPort (by decide)) (prepared (by decide) tupleInputs a)=
      BucketTupleProgram.Expand.state regs rows mask context (BucketTupleProgram.Table.tableBits bs) [] := by
    apply prepared_eq tupleRegs (by decide) tupleInputs a _ tupleInputs_protected (by decide)
    · intro j; rfl
    · intro p hp
      simp only [tupleInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl <;>
        simp [BucketTupleProgram.Expand.state,hr,hmarker,ht,hm,hc]
    · intro j hj
      have h0 : j≠0 := hj (660,0) (by simp [tupleInputs])
      have h5 : j≠5 := hj (665,5) (by simp [tupleInputs])
      have h9 : j≠9 := hj (669,9) (by simp [tupleInputs])
      have h10 : j≠10 := hj (670,10) (by simp [tupleInputs])
      have h11 : j≠11 := hj (671,11) (by simp [tupleInputs])
      fin_cases j <;> simp_all [BucketTupleProgram.Expand.state]
  obtain ⟨rf,t,htime,he⟩ := BucketTupleProgram.Expand.program_runsIn regs rows mask context bs
  have h := stage_eval BucketTupleProgram.Expand.program tupleRegs (Fin.castAdd_injective _ _)
    (by decide) tupleInputs tupleOutputs a _ _ tupleInputs_protected tupleOutputs_protected hp he
  refine ⟨rf,_,?_,h⟩
  unfold tupleCost stageCost
  omega

theorem tupleResult_value (a : Data) (regs : Fin 10 → Bool) (rows : List (List Bool))
    (mask context : List Bool) (bs : List BucketTupleProgram.Table.Bucket) :
    (tupleResult a regs rows mask context bs).stacks 660=ProgramEncoding.encodeRecords
      (BucketTupleProgram.Expand.nextRows rows mask context bs) :=
  returned_word tupleRegs (by decide) tupleInputs tupleOutputs a _ tupleOutputs_protected
    (by decide) (0,660) (by simp [tupleOutputs])

theorem tupleResult_frame (a : Data) (regs : Fin 10 → Bool) (rows : List (List Bool))
    (mask context : List Bool) (bs : List BucketTupleProgram.Table.Bucket)
    (i : Fin 768) (hi : Protected i) (h660 : i≠660) :
    (tupleResult a regs rows mask context bs).stacks i=a.stacks i := by
  apply returned_frame tupleRegs (by decide) tupleInputs tupleOutputs a _ i hi
  intro p hp
  simp only [tupleOutputs,List.mem_singleton] at hp
  subst p
  exact h660

def finalRegs : Fin 8 → Fin 16 := Fin.castAdd 8
def finalInputs : List (Fin 768 × Fin 20) := [(660,0),(128,16)]
def finalOutputs : List (Fin 20 × Fin 768) := [(8,163)]
def finalize : Code := stage BucketTupleProgram.Representative.program finalRegs (by decide)
  finalInputs finalOutputs
theorem finalInputs_protected : ∀ p∈finalInputs,Protected p.1 := by simp [finalInputs,Protected,temporary]
theorem finalOutputs_protected : ∀ p∈finalOutputs,Protected p.2 := by simp [finalOutputs,Protected,temporary]

def finalResult (a : Data) (regs : Fin 8 → Bool) (width : List Bool)
    (tuples : BucketTupleProgram.Representative.Tuples) : Data :=
  returned finalRegs (by decide) finalInputs finalOutputs a
    (BucketTupleProgram.Representative.state regs width [] [] [] []
      (MomentsAssembly.bucketsInput
        ((tuples.map (BucketTupleProgram.Representative.bucket width.length)).reverse)))
def finalCost (a : Data) (regs : Fin 8 → Bool) (width : List Bool)
    (tuples : BucketTupleProgram.Representative.Tuples) : ℕ :=
  stageCost finalRegs (by decide) finalInputs finalOutputs a
    (BucketTupleProgram.Representative.state regs width [] [] [] []
      (MomentsAssembly.bucketsInput
        ((tuples.map (BucketTupleProgram.Representative.bucket width.length)).reverse)))
    (BucketTupleProgram.Representative.cost width tuples+1)

theorem finalize_eval (a : Data) (width : List Bool)
    (tuples : BucketTupleProgram.Representative.Tuples)
    (ht : a.stacks 660=BucketTupleProgram.Representative.tuplesBits tuples)
    (hw : a.stacks 128=width)
    (hv : ∀ heads∈tuples,∀ h∈heads,BucketTupleProgram.Representative.Valid width.length h) :
    ∃ regs t,t ≤ finalCost a regs width tuples ∧ Eval finalize t a (finalResult a regs width tuples) := by
  let regs := (prepared (by decide) finalInputs a).regs ∘ finalRegs
  have hp : projectState finalRegs (workPort (by decide)) (prepared (by decide) finalInputs a)=
      BucketTupleProgram.Representative.zeroStart regs width
        (BucketTupleProgram.Representative.tuplesBits tuples) [] := by
    apply prepared_eq finalRegs (by decide) finalInputs a _ finalInputs_protected (by decide)
    · intro j; rfl
    · intro p hp
      simp only [finalInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl <;> simp [BucketTupleProgram.Representative.zeroStart,ht,hw]
    · intro j hj
      have h0 : j≠0 := hj (660,0) (by simp [finalInputs])
      have h16 : j≠16 := hj (128,16) (by simp [finalInputs])
      fin_cases j <;> simp_all [BucketTupleProgram.Representative.zeroStart]
  obtain ⟨rf,t,htime,he⟩ := BucketTupleProgram.Representative.program_runsIn regs width tuples hv
  have h := stage_eval BucketTupleProgram.Representative.program finalRegs (Fin.castAdd_injective _ _)
    (by decide) finalInputs finalOutputs a _ _ finalInputs_protected finalOutputs_protected hp he
  refine ⟨rf,_,?_,h⟩
  unfold finalCost stageCost
  omega

theorem finalResult_value (a : Data) (regs : Fin 8 → Bool) (width : List Bool)
    (tuples : BucketTupleProgram.Representative.Tuples) :
    (finalResult a regs width tuples).stacks 163=MomentsAssembly.bucketsInput
      ((tuples.map (BucketTupleProgram.Representative.bucket width.length)).reverse) :=
  returned_word finalRegs (by decide) finalInputs finalOutputs a _ finalOutputs_protected
    (by decide) (8,163) (by simp [finalOutputs])


theorem finalResult_frame (a : Data) (regs : Fin 8 → Bool) (width : List Bool)
    (tuples : BucketTupleProgram.Representative.Tuples)
    (i : Fin 768) (hi : Protected i) (h163 : i≠163) :
    (finalResult a regs width tuples).stacks i=a.stacks i := by
  apply returned_frame finalRegs (by decide) finalInputs finalOutputs a _ i hi
  intro p hp
  simp only [finalOutputs,List.mem_singleton] at hp
  subst p
  exact h163

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
