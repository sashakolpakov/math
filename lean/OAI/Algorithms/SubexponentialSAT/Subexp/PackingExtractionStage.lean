import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketStage
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingExtractionSemantics

namespace OAI.Algorithms

/-! Exact relocation of complete-block extraction in the final controller. -/

namespace SubexponentialSAT.Subexp.PackingProgram

open BitProgram StructuredCalls PackingProgramSupport

def initialExtraction (entries : List PackingExtraction.Entry) (n : ℕ) : PackingExtraction.Context :=
  ⟨[], [], [], [], [], [], [], ProgramEncoding.encodeRecords (entries.map PackingExtraction.entryWord),
    List.replicate n true⟩

def extracted (entries : List PackingExtraction.Entry) (n : ℕ) : PackingExtraction.Context :=
  PackingExtraction.advanceMany entries n 0 (initialExtraction entries n)

def extractionOutputState (input : Input) (n : ℕ) (c : PackingExtraction.Context)
    (regs : Fin 16 → Bool) : Data :=
  ⟨regs, fun i => if i = 6 then c.metadata else if i = 11 then c.address else
    if i = 12 then c.storage else if i = 13 then c.metadata else if i = 14 then c.addresses else
    if i = 30 then List.replicate n true else (inputState input regs).stacks i⟩

def extractionBudget (entries : List PackingExtraction.Entry) (n : ℕ) : ℕ :=
  PackingExtraction.loopBudget entries n 0 (initialExtraction entries n) + 6 * n +
    2 * (ProgramEncoding.encodeRecords (entries.map PackingExtraction.entryWord)).length +
    7 * (extracted entries n).metadata.length + 16

private theorem extraction_call_stacks (input : Input) (entries : List PackingExtraction.Entry)
    (n : ℕ) (regs : Fin 16 → Bool) (re : Fin 8 → Bool)
    (hb : (extracted entries n).block = List.replicate n true)
    (hr : (extracted entries n).remaining = [])
    (ht : (extracted entries n).buckets =
      ProgramEncoding.encodeRecords (entries.map PackingExtraction.entryWord)) :
    (install (by decide : 8 ≤ 16) (by decide : 19 ≤ 48)
      (bucketsOutputState input (ProgramEncoding.encodeRecords (entries.map PackingExtraction.entryWord))
        (List.replicate n true) regs)
      (PackingExtraction.base re (extracted entries n))).stacks = fun i =>
      if i = 10 then List.replicate n true else if i = 11 then (extracted entries n).address
      else if i = 12 then (extracted entries n).storage else if i = 13 then (extracted entries n).metadata
      else if i = 14 then (extracted entries n).addresses
      else if i = 15 then ProgramEncoding.encodeRecords (entries.map PackingExtraction.entryWord)
      else (inputState input regs).stacks i := by
  funext i
  fin_cases i <;>
    simp [install, PackingExtraction.base, PackingExtraction.ready, PackingExtraction.state,
      bucketsOutputState, inputState, hb, hr, ht, Fin.coe_ofNat_eq_mod]

theorem extraction_eval (input : Input) (entries : List PackingExtraction.Entry) (n : ℕ)
    (hentries : ∀ e ∈ entries, n ≤ e.2.length) (regs : Fin 16 → Bool) :
    ∃ steps ≤ extractionBudget entries n, ∃ rf,
      Eval extraction steps
        (bucketsOutputState input
          (ProgramEncoding.encodeRecords (entries.map PackingExtraction.entryWord))
          (List.replicate n true) regs)
        (extractionOutputState input n (extracted entries n) rf) := by
  let a := bucketsOutputState input
    (ProgramEncoding.encodeRecords (entries.map PackingExtraction.entryWord)) (List.replicate n true) regs
  have hp : project (by decide : 8 ≤ 16) (by decide : 19 ≤ 48) a =
      PackingExtraction.base (project (by decide : 8 ≤ 16) (by decide : 19 ≤ 48) a).regs
        (initialExtraction entries n) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;>
      simp [ stackPorts, a, bucketsOutputState, inputState,
 initialExtraction]
  obtain ⟨ne, hne, re, he⟩ := PackingExtraction.program_trace entries n
    (initialExtraction entries n) rfl rfl rfl hentries
    (project (by decide : 8 ≤ 16) (by decide : 19 ≤ 48) a).regs
  let b := install (by decide : 8 ≤ 16) (by decide : 19 ≤ 48) a
    (PackingExtraction.base re (extracted entries n))
  have hcall : Eval extractionCall ne a b := by
    apply lowCall_eval
    rw [hp]
    exact he
  obtain ⟨hblock, hremaining, hbuckets⟩ := PackingExtraction.advanceMany_static entries n 0
    (initialExtraction entries n) rfl rfl
  have hb : (extracted entries n).block = List.replicate n true := by
    simpa [extracted, PackingMetadata.unary] using hblock
  have hr : (extracted entries n).remaining = [] := hremaining
  have ht : (extracted entries n).buckets =
      ProgramEncoding.encodeRecords (entries.map PackingExtraction.entryWord) := hbuckets
  have hd : b.stacks = fun i =>
      if i = 10 then List.replicate n true else if i = 11 then (extracted entries n).address
      else if i = 12 then (extracted entries n).storage else if i = 13 then (extracted entries n).metadata
      else if i = 14 then (extracted entries n).addresses
      else if i = 15 then ProgramEncoding.encodeRecords (entries.map PackingExtraction.entryWord)
      else (inputState input regs).stacks i := extraction_call_stacks input entries n regs re hb hr ht
  have hv : PackingPlumbing.Valid extractionSave b := by
    simp [PackingPlumbing.Valid, PackingPlumbing.Op.Valid, extractionSave,
      PackingPlumbing.move, PackingPlumbing.Op.next, hd,
      inputState, StackRoutines.transferStacks, StackRoutines.clearStacks]
  let c := PackingPlumbing.run extractionSave b
  have hc : c = extractionOutputState input n (extracted entries n) c.regs := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;>
      simp [c, PackingPlumbing.run, extractionSave, PackingPlumbing.move, PackingPlumbing.Op.next,
        hd, inputState,
        StackRoutines.copyStacks, StackRoutines.transferStacks, StackRoutines.clearStacks]
  have hcost : PackingPlumbing.cost extractionSave b = 6 * n +
      2 * (ProgramEncoding.encodeRecords (entries.map PackingExtraction.entryWord)).length +
      7 * (extracted entries n).metadata.length + 14 := by
    simp [PackingPlumbing.cost, PackingPlumbing.Op.cost, extractionSave, PackingPlumbing.move,
      PackingPlumbing.Op.next, hd, inputState, StackRoutines.transferStacks, StackRoutines.clearStacks]
    omega
  have hrun := hcall.seq (PackingPlumbing.eval extractionSave b hv)
  refine ⟨ne + PackingPlumbing.cost extractionSave b, ?_, c.regs, ?_⟩
  · rw [hcost]
    unfold extractionBudget
    omega
  · change Eval extraction _ a c at hrun
    rw [hc] at hrun
    exact hrun

end SubexponentialSAT.Subexp.PackingProgram

end OAI.Algorithms
