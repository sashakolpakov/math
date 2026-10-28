import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingProgramAuxiliary
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketSemantics

namespace OAI.Algorithms

/-! Actual all-key bucketing in the final 16-register controller. -/

namespace SubexponentialSAT.Subexp.PackingProgram

open BitProgram StructuredCalls PackingProgramSupport

def bucketsOutputState (input : Input) (table count : List Bool) (regs : Fin 16 → Bool) : Data :=
  ⟨regs, fun i => if i = 15 then table else if i = 16 then count
    else (inputState input regs).stacks i⟩

def bucketsBudget (records : List BucketProgram.Record) (keys : List (List Bool)) (D : ℕ) : ℕ :=
  8 * (BucketProgram.encodeRecords records.reverse).length +
  6 * (ProgramEncoding.encodeRecords keys).length + 7 * D +
  6 * (ProgramEncoding.encodeRecords (PackingBucketTable.table records keys)).length +
  6 * PackingBucketTable.minimum records keys D + 32 + PackingBucketTable.budget records keys

private theorem bucket_call_stacks (input : Input) (records : List BucketProgram.Record)
    (keys : List (List Bool)) (D : ℕ) (regs : Fin 16 → Bool) (rb : Fin 8 → Bool) :
    (install (by decide : 8 ≤ 16) (by decide : 15 ≤ 48)
      (PackingPlumbing.run bucketsSetup
        (frontendOutputState input (BucketProgram.encodeRecords records.reverse)
          (ProgramEncoding.encodeRecords keys) regs))
      (PackingBucketTable.outputState records keys D [] rb)).stacks = fun i =>
        if i = 5 then ProgramEncoding.encodeRecords (PackingBucketTable.table records keys)
        else if i = 6 then BucketProgram.encodeRecords records.reverse
        else if i = 10 then List.replicate (PackingBucketTable.minimum records keys D) true
        else (inputState input regs).stacks i := by
  funext i
  fin_cases i <;>
    simp [install, PackingPlumbing.run, bucketsSetup, PackingPlumbing.move, PackingPlumbing.Op.next,
      frontendOutputState, inputState, PackingBucketTable.outputState, PackingBucketCalls.state,
      StackRoutines.copyStacks, StackRoutines.transferStacks, Fin.coe_ofNat_eq_mod]

private theorem bucket_save_stacks (input : Input) (records : List BucketProgram.Record)
    (keys : List (List Bool)) (D : ℕ) (regs : Fin 16 → Bool) (c : Data)
    (hc : c.stacks = fun i =>
      if i = 5 then ProgramEncoding.encodeRecords (PackingBucketTable.table records keys)
      else if i = 6 then BucketProgram.encodeRecords records.reverse
      else if i = 10 then List.replicate (PackingBucketTable.minimum records keys D) true
      else (inputState input regs).stacks i) :
    (PackingPlumbing.run bucketsSave c).stacks =
      (bucketsOutputState input (ProgramEncoding.encodeRecords (PackingBucketTable.table records keys))
        (List.replicate (PackingBucketTable.minimum records keys D) true) regs).stacks := by
  funext i
  fin_cases i <;>
    simp [PackingPlumbing.run, bucketsSave, PackingPlumbing.move, PackingPlumbing.Op.next,
      hc, inputState, bucketsOutputState, StackRoutines.transferStacks,
      StackRoutines.clearStacks]

theorem buckets_eval (input : Input) (records : List BucketProgram.Record)
    (keys : List (List Bool)) (D : ℕ) (hD : input.dimension = List.replicate D true)
    (hcount : D ≤ records.length) (regs : Fin 16 → Bool) :
    ∃ n ≤ bucketsBudget records keys D, ∃ rf,
      Eval buckets n
        (frontendOutputState input (BucketProgram.encodeRecords records.reverse)
          (ProgramEncoding.encodeRecords keys) regs)
        (bucketsOutputState input
          (ProgramEncoding.encodeRecords (PackingBucketTable.table records keys))
          (List.replicate (PackingBucketTable.minimum records keys D) true) rf) := by
  let a := frontendOutputState input (BucketProgram.encodeRecords records.reverse)
    (ProgramEncoding.encodeRecords keys) regs
  have hv : PackingPlumbing.Valid bucketsSetup a := by
    simp [PackingPlumbing.Valid, PackingPlumbing.Op.Valid, bucketsSetup,
      PackingPlumbing.move, PackingPlumbing.Op.next, a, frontendOutputState, inputState,
 StackRoutines.transferStacks]
  let b := PackingPlumbing.run bucketsSetup a
  have hp : project (by decide : 8 ≤ 16) (by decide : 15 ≤ 48) b =
      PackingBucketTable.inputState records keys D []
        (project (by decide : 8 ≤ 16) (by decide : 15 ≤ 48) b).regs := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;>
      simp [ stackPorts, b, PackingPlumbing.run, bucketsSetup,
        PackingPlumbing.move, PackingPlumbing.Op.next, a, frontendOutputState, inputState,
        StackRoutines.copyStacks, StackRoutines.transferStacks,
 hD]
  obtain ⟨nb, hnb, rb, hbt⟩ := PackingBucketTable.program_trace records keys D hcount []
    (project (by decide : 8 ≤ 16) (by decide : 15 ≤ 48) b).regs
  let c := install (by decide : 8 ≤ 16) (by decide : 15 ≤ 48) b
    (PackingBucketTable.outputState records keys D [] rb)
  have hcall : Eval bucketsCall nb b c := by
    apply lowCall_eval
    rw [hp]
    exact hbt
  have hc : c.stacks = fun i =>
      if i = 5 then ProgramEncoding.encodeRecords (PackingBucketTable.table records keys)
      else if i = 6 then BucketProgram.encodeRecords records.reverse
      else if i = 10 then List.replicate (PackingBucketTable.minimum records keys D) true
      else (inputState input regs).stacks i := bucket_call_stacks input records keys D regs rb
  have hw : PackingPlumbing.Valid bucketsSave c := by
    simp [PackingPlumbing.Valid, PackingPlumbing.Op.Valid, bucketsSave,
      PackingPlumbing.move
]
  let d := PackingPlumbing.run bucketsSave c
  have hd : d = bucketsOutputState input
      (ProgramEncoding.encodeRecords (PackingBucketTable.table records keys))
      (List.replicate (PackingBucketTable.minimum records keys D) true) d.regs := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    exact bucket_save_stacks input records keys D regs c hc
  have hc1 : PackingPlumbing.cost bucketsSetup a =
      6 * (BucketProgram.encodeRecords records.reverse).length +
      6 * (ProgramEncoding.encodeRecords keys).length + 7 * D + 17 := by
    simp [PackingPlumbing.cost, PackingPlumbing.Op.cost, bucketsSetup, PackingPlumbing.move,
      PackingPlumbing.Op.next, a, frontendOutputState, inputState,
 StackRoutines.transferStacks, hD]
    omega
  have hc2 : PackingPlumbing.cost bucketsSave c =
      2 * (BucketProgram.encodeRecords records.reverse).length +
      6 * (ProgramEncoding.encodeRecords (PackingBucketTable.table records keys)).length +
      6 * PackingBucketTable.minimum records keys D + 15 := by
    simp [PackingPlumbing.cost, PackingPlumbing.Op.cost, bucketsSave, PackingPlumbing.move,
      PackingPlumbing.Op.next, hc, inputState, StackRoutines.clearStacks, StackRoutines.transferStacks]
    omega
  have he := (PackingPlumbing.eval bucketsSetup a hv).seq
    (hcall.seq (PackingPlumbing.eval bucketsSave c hw))
  refine ⟨PackingPlumbing.cost bucketsSetup a + (nb + PackingPlumbing.cost bucketsSave c),
    ?_, d.regs, ?_⟩
  · rw [hc1, hc2]
    unfold bucketsBudget
    omega
  · change Eval buckets _ a d at he
    rw [hd] at he
    exact he

end SubexponentialSAT.Subexp.PackingProgram

end OAI.Algorithms
