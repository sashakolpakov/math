import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorArithmeticFrames
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly

/-! Static register frames for the concrete tuple visitor. The frame follows
from the actual instructions and embeddings, including the ambient overlay.
The retained tuple-controller flags require no save stack. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorFrames

open OAI BitProgram StructuredCalls
open CommandRegisterFrames QueryTupleVisitor

private theorem not_mem_union_iff {R : Type} [DecidableEq R]
    {i : R} {left right : Finset R} :
    i ∉ left ∪ right ↔ i ∉ left ∧ i ∉ right := by
  simp only [Finset.mem_union, not_or]

private theorem not_mem_empty {R : Type} [DecidableEq R] (i : R) :
    i ∉ (∅ : Finset R) := by
  simp

private theorem high_ne (i : Fin 40) (hi : 16 ≤ i.val)
    (j : Fin 40) (hj : j.val < 16) : i ≠ j := by
  intro h
  subst i
  omega

private theorem outside16 (i : Fin 40) (hi : 16 ≤ i.val) :
    ¬ ∃ j : Fin 16, j.castAdd 24 = i := by
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  simp only [Fin.val_castAdd] at hv
  omega

private theorem copy_not_mem_writes (src dst tmp : Fin 896)
    (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes (SignatureTupleProgram.copyWord src dst tmp) :=
  not_mem_copyProgram src dst tmp 0 1 i
    (high_ne i hi 0 (by decide)) (high_ne i hi 1 (by decide))

theorem overwrite_not_mem_writes (src dst : Fin 896)
    (i : Fin 40) (hi : 16 ≤ i.val) : i ∉ writes (overwrite src dst) :=
  not_mem_union_iff.mpr ⟨not_mem_clearProgram dst 0 1 i
    (high_ne i hi 0 (by decide)) (high_ne i hi 1 (by decide)),
    copy_not_mem_writes src dst 841 i hi⟩

theorem restart_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes restart :=
  not_mem_union_iff.mpr ⟨overwrite_not_mem_writes 837 840 i hi,
    overwrite_not_mem_writes 845 843 i hi⟩

theorem readHead_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes readHead := by
  have hp : i ∉ writes (SignatureTupleProgram.popWordCommand 840 838 (by decide)) := by
    apply not_mem_liftProgram
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    omega
  have h0 := high_ne i hi 0 (by decide)
  have h1 := high_ne i hi 1 (by decide)
  simpa [readHead, writes, baseWrites, StructuredProgram.Atom.instr,
    ProgramLogic.registerWrites, h0, h1] using hp

private theorem testFrames_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes testFrames := by
  simp [testFrames, writes, baseWrites, StructuredProgram.Atom.instr,
    ProgramLogic.registerWrites, high_ne i hi 0 (by decide), high_ne i hi 1 (by decide)]

theorem finishHead_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes finishHead :=
  not_mem_union_iff.mpr ⟨not_mem_clearProgram 838 0 1 i
    (high_ne i hi 0 (by decide)) (high_ne i hi 1 (by decide)),
    testFrames_not_mem_writes i hi⟩

theorem install_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes installRepresentative :=
  not_mem_union_iff.mpr ⟨overwrite_not_mem_writes 838 859 i hi,
    not_mem_union_iff.mpr ⟨not_mem_compiled _ _ _ i
      (HeadSumAssembly.overlay_not_mem_writes i hi),
      not_mem_union_iff.mpr ⟨overwrite_not_mem_writes 145 869 i hi,
        not_mem_clearProgram 859 0 1 i
          (high_ne i hi 0 (by decide)) (high_ne i hi 1 (by decide))⟩⟩⟩

theorem clearMany_not_mem_writes (ports : List (Fin 896))
    (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes (NodeReadoutSpace.clearMany ports) := by
  induction ports with
  | nil => exact not_mem_empty i
  | cons p ps ih =>
      exact not_mem_union_iff.mpr ⟨not_mem_clearProgram p 0 1 i
        (high_ne i hi 0 (by decide)) (high_ne i hi 1 (by decide)), ih⟩

theorem clearPair_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes QueryAssembler.clearPair :=
  not_mem_liftCommand _ _ _ _ _ i (outside16 i hi)

theorem bootstrap_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes FactorEnvironment.bootstrap :=
  not_mem_liftProgram _ _ _ i (outside16 i hi)

theorem prepareMultiply_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes QueryAssembler.TupleMultiply.prepare :=
  not_mem_union_iff.mpr ⟨clearMany_not_mem_writes [61,70] i hi,
    not_mem_union_iff.mpr ⟨clearPair_not_mem_writes i hi,
      bootstrap_not_mem_writes i hi⟩⟩

/-- Replay overwrites both retained traversal copies on every pass. -/
theorem replay_not_mem_writes (work : Cmd 40 896) (i : Fin 40) (hi : 16 ≤ i.val)
    (hw : i ∉ writes work) : i ∉ writes (QueryExecution.replay work) :=
  not_mem_union_iff.mpr ⟨restart_not_mem_writes i hi,
    not_mem_union_iff.mpr ⟨testFrames_not_mem_writes i hi,
      not_mem_union_iff.mpr ⟨readHead_not_mem_writes i hi,
        not_mem_union_iff.mpr ⟨hw, finishHead_not_mem_writes i hi⟩⟩⟩⟩

/-- The original multiplication runs inside its actual low-register map. -/
theorem tupleMultiply_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes QueryAssembler.TupleMultiply.command := by
  have hm : i ∉ writes QueryAssembler.TupleMultiply.multiply := by
    apply not_mem_liftCommand_of
    intro j hj
    change j = i at hj
    subst j
    exact FactorArithmeticFrames.accumulate_not_mem_writes i hi
  exact not_mem_union_iff.mpr ⟨prepareMultiply_not_mem_writes i hi,
    not_mem_union_iff.mpr ⟨hm, clearPair_not_mem_writes i hi⟩⟩

private theorem tupleSum_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes QueryTupleSum.command := by
  have hc (src dst : Fin 896) : i ∉ writes (NodeAppendSpace.copy src dst) :=
    not_mem_copyProgram src dst 89 0 1 i
      (high_ne i hi 0 (by decide)) (high_ne i hi 1 (by decide))
  have hp : i ∉ writes NodeAppendSpace.prepare :=
    not_mem_union_iff.mpr ⟨clearMany_not_mem_writes [89,5,12,39] i hi,
      not_mem_union_iff.mpr ⟨hc 194 5, not_mem_union_iff.mpr ⟨hc 202 12, hc 204 39⟩⟩⟩
  have hl : i ∉ programWrites (ProgramLinking.liftProgram
      OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.program QueryTupleSum.registers QueryTupleSum.ports) := by
    apply not_mem_liftProgram
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    omega
  exact not_mem_union_iff.mpr ⟨not_mem_union_iff.mpr
    ⟨hp, clearMany_not_mem_writes _ i hi⟩, hl⟩

theorem tupleEnd_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes QueryExecution.TupleEnd.command :=
  not_mem_union_iff.mpr ⟨tupleSum_not_mem_writes i hi,
    not_mem_liftCommand _ _ _ _ _ i (outside16 i hi)⟩

/-- Every source prefix of the actual multiplier retains the caller flags. -/
theorem tupleMultiply_register_frame {steps : ℕ}
    {a b : Cfg 40 896 (size QueryAssembler.TupleMultiply.command + 1)}
    (he : Trace QueryAssembler.TupleMultiply.program steps a b)
    (i : Fin 40) (hi : 16 ≤ i.val) : b.regs i = a.regs i :=
  compiled_trace_register_frame _ _ _ he i (tupleMultiply_not_mem_writes i hi)

theorem tupleEnd_register_frame {steps : ℕ}
    {a b : Cfg 40 896 (size QueryExecution.TupleEnd.command + 1)}
    (he : Trace QueryExecution.TupleEnd.program steps a b)
    (i : Fin 40) (hi : 16 ≤ i.val) : b.regs i = a.regs i :=
  compiled_trace_register_frame _ _ _ he i (tupleEnd_not_mem_writes i hi)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorFrames
