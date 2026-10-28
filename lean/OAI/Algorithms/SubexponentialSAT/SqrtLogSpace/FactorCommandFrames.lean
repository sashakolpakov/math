import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorArithmeticFrames
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandStackFrames
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram

/-! The actual accepted-assignment implementation writes only the lower sixteen
Boolean registers. This is a static fact about every concrete called table,
including the original factor dispatcher, parser and native arithmetic. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorCommandFrames

open OAI BitProgram StructuredCalls SqrtLog.LeafProgram
open CommandRegisterFrames

private theorem not_mem_union_iff {R : Type} [DecidableEq R]
    {i : R} {left right : Finset R} :
    i ∉ left ∪ right ↔ i ∉ left ∧ i ∉ right := by
  simp only [Finset.mem_union, not_or]

private theorem not_mem_empty {R : Type} [DecidableEq R] (i : R) :
    i ∉ (∅ : Finset R) := by
  simp

private theorem high_ne (i : Fin 40) (hi : 16 ≤ i.val) (j : Fin 40) (hj : j.val < 16) : i ≠ j := by
  intro he
  subst i
  omega

private theorem outside8 (i : Fin 40) (hi : 16 ≤ i.val) :
    ¬ ∃ j : Fin 8, j.castAdd 32 = i := by
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  simp only [Fin.val_castAdd] at hv
  omega

private theorem outside16 (i : Fin 40) (hi : 16 ≤ i.val) :
    ¬ ∃ j : Fin 16, j.castAdd 24 = i := by
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  simp only [Fin.val_castAdd] at hv
  omega

private theorem liftLow_safe (c : Cmd 40 768) (input output : Fin 768)
    (i : Fin 40) (hc : i ∉ writes c) :
    i ∉ writes (FactorAssignmentProgram.liftLow c input output) := by
  apply not_mem_liftCommand_of
  intro j hj
  change j = i at hj
  subst j
  exact hc

private theorem hashArithmetic_safe (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes FactorEvaluationSpace.hashArithmetic := by
  have hp : i ∉ programWrites (ProgramLinking.liftProgram
      Indicator.program Factor.nativeRegisters Factor.indicatorStacks) :=
    not_mem_liftProgram _ _ _ i (outside8 i hi)
  have h0 := high_ne i hi 0 (by decide)
  have h1 := high_ne i hi 1 (by decide)
  have h2 := high_ne i hi 2 (by decide)
  have hready : i ∉ writes Factor.indicatorReady := by
    unfold Factor.indicatorReady
    refine not_mem_union_iff.mpr ⟨?_, not_mem_union_iff.mpr ⟨?_, ?_⟩⟩
    · simpa [writes, baseWrites, StructuredProgram.Atom.instr,
        ProgramLogic.registerWrites] using h0
    · simpa [writes, baseWrites, StructuredProgram.Atom.instr,
        ProgramLogic.registerWrites] using h1
    · simpa [writes, baseWrites, StructuredProgram.Atom.instr,
        ProgramLogic.registerWrites] using h2
  have hind : i ∉ writes Factor.indicator := by
    unfold Factor.indicator
    exact not_mem_union_iff.mpr ⟨hready, hp⟩
  unfold FactorEvaluationSpace.hashArithmetic
  exact not_mem_union_iff.mpr ⟨hind, not_mem_union_iff.mpr
    ⟨FactorArithmeticFrames.clear_not_mem_writes _ i hi, not_mem_union_iff.mpr
      ⟨FactorArithmeticFrames.clear_not_mem_writes _ i hi,
        FactorArithmeticFrames.accumulate_not_mem_writes i hi⟩⟩⟩

private theorem markedArithmetic_safe (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes FactorEvaluationSpace.markedArithmetic := by
  have hc : i ∉ writes Clause.caller := not_mem_liftProgram _ _ _ i (outside8 i hi)
  unfold FactorEvaluationSpace.markedArithmetic
  exact not_mem_union_iff.mpr ⟨hc, not_mem_union_iff.mpr
    ⟨FactorArithmeticFrames.clear_not_mem_writes _ i hi,
      FactorArithmeticFrames.accumulate_not_mem_writes i hi⟩⟩

private theorem expansion_safe (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes Expansion.forwardCommand := by
  have hc : i ∉ writes Expansion.command := not_mem_liftProgram _ _ _ i (outside8 i hi)
  have hr : i ∉ writes Expansion.reverseInput := not_mem_reverseProgram 154 358 359 0 1 i
    (high_ne i hi 0 (by decide)) (high_ne i hi 1 (by decide))
  exact not_mem_union_iff.mpr ⟨hr, hc⟩

private theorem factorID_safe (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes FactorID.command := by
  have h0 := high_ne i hi 0 (by decide)
  have h1 := high_ne i hi 1 (by decide)
  have hc := not_mem_copyProgram (149 : Fin 768) 556 359 0 1 i h0 h1
  unfold FactorID.command
  refine not_mem_union_iff.mpr ⟨hc, ?_⟩
  simpa [writes, baseWrites, StructuredProgram.Atom.instr,
    ProgramLogic.registerWrites] using And.intro h0 h1

private theorem dispatch_safe (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes FactorDispatch.command := by
  have h0 := high_ne i hi 0 (by decide)
  have h1 := high_ne i hi 1 (by decide)
  have h7 := high_ne i hi 7 (by decide)
  have hc := not_mem_copyProgram (149 : Fin 768) 152 359 0 1 i h0 h1
  have hd : i ∉ writes FactorDispatch.dispatch := not_mem_liftProgram _ _ _ i (outside8 i hi)
  unfold FactorDispatch.command
  refine not_mem_union_iff.mpr ⟨not_mem_union_iff.mpr ⟨hc, ?_⟩, hd⟩
  simpa [writes, baseWrites, StructuredProgram.Atom.instr,
    ProgramLogic.registerWrites] using And.intro h7 h0

private theorem prepareIncidence_safe (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes FactorAssignmentProgram.prepareIncidence := by
  have hc : i ∉ writes FactorTableProgram.caller :=
    not_mem_liftProgram _ _ _ i (outside16 i hi)
  exact not_mem_union_iff.mpr ⟨liftLow_safe _ _ _ i (factorID_safe i hi), hc⟩

private theorem choose_safe (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes FactorAssignmentProgram.choose := by
  have hh : i ∉ writes FactorAssignmentProgram.hashFactor := by
    exact not_mem_union_iff.mpr ⟨prepareIncidence_safe i hi,
      liftLow_safe _ _ _ i (not_mem_union_iff.mpr
        ⟨expansion_safe i hi, hashArithmetic_safe i hi⟩)⟩
  have hm : i ∉ writes FactorAssignmentProgram.markedFactor := by
    exact not_mem_union_iff.mpr ⟨prepareIncidence_safe i hi,
      liftLow_safe _ _ _ i (not_mem_union_iff.mpr
        ⟨FactorArithmeticFrames.move_not_mem_writes _ _ i hi, markedArithmetic_safe i hi⟩)⟩
  simp only [FactorAssignmentProgram.choose, writes, baseWrites, not_mem_union_iff,
    not_mem_empty]
  exact ⟨hh, hm, by simp⟩

private theorem assignment_clear (src : Fin 896) (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes (FactorAssignmentProgram.clear src) :=
  not_mem_clearProgram src 0 1 i (high_ne i hi 0 (by decide)) (high_ne i hi 1 (by decide))

private theorem assignment_copy (src dst : Fin 896) (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes (FactorAssignmentProgram.copy src dst) :=
  not_mem_copyProgram src dst 159 0 1 i (high_ne i hi 0 (by decide)) (high_ne i hi 1 (by decide))

private theorem callback_safe (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes FactorAssignmentProgram.callback := by
  have hclear : i ∉ writes FactorAssignmentProgram.clearCallback :=
    not_mem_liftCommand _ _ _ _ _ i (outside16 i hi)
  have hreturn : i ∉ writes FactorAssignmentProgram.returnToRecords := by
    simp [FactorAssignmentProgram.returnToRecords, writes, baseWrites,
      StructuredProgram.Atom.instr, ProgramLogic.registerWrites,
      high_ne i hi 13 (by decide), high_ne i hi 14 (by decide), high_ne i hi 15 (by decide)]
  simp only [FactorAssignmentProgram.callback, writes, not_mem_union_iff]
  exact ⟨hclear, liftLow_safe _ _ _ i (dispatch_safe i hi), choose_safe i hi,
    assignment_clear _ i hi, hreturn⟩

/-- This fact inspects the actual accepted-assignment syntax and actual called
program maps. There is no semantic frame hypothesis for a callback. -/
theorem assignment_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes FactorAssignmentProgram.assignment := by
  have hinit : i ∉ writes FactorAssignmentProgram.initialize :=
    not_mem_liftCommand _ _ _ _ _ i (outside16 i hi)
  have hsetup : i ∉ writes FactorAssignmentProgram.setup :=
    not_mem_liftCommand _ _ _ _ _ i (outside16 i hi)
  have hloop : i ∉ writes FactorAssignmentProgram.loop :=
    not_mem_record_iterate FactorAssignmentProgram.ports _ i (callback_safe i hi)
      (high_ne i hi 13 (by decide)) (high_ne i hi 14 (by decide)) (high_ne i hi 15 (by decide))
  simp only [FactorAssignmentProgram.assignment, FactorAssignmentProgram.product,
    FactorAssignmentProgram.move, writes, not_mem_union_iff]
  exact ⟨hinit, hsetup, assignment_copy _ _ i hi, assignment_copy _ _ i hi,
    hloop, assignment_copy _ _ i hi, assignment_clear _ i hi⟩

theorem assignment_register_frame {steps : ℕ} {a b : State 40 896}
    (ht : Eval FactorAssignmentProgram.assignment steps a b)
    (i : Fin 40) (hi : 16 ≤ i.val) : b.regs i = a.regs i :=
  eval_register_frame ht i (assignment_not_mem_writes i hi)

/-- All actual source prefixes, including the compiled halt, preserve the
outer loop control registers36–39 (and every other register at least16). -/
theorem assignment_trace_register_frame {steps : ℕ}
    {a b : Cfg 40 896 (StructuredCalls.size FactorAssignmentProgram.assignment + 1)}
    (ht : Trace FactorAssignmentProgram.program steps a b)
    (i : Fin 40) (hi : 16 ≤ i.val) : b.regs i = a.regs i :=
  compiled_trace_register_frame _ _ _ ht i (assignment_not_mem_writes i hi)

private theorem lowStack_not_851 :
    ¬ ∃ j, FactorAssignmentProgram.lowStack j = (851 : Fin 896) := by
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  change j.val=851 at hv
  omega

private theorem liftLow_not_851 (c : Cmd 40 768) (input output : Fin 768) :
    (851 : Fin 896) ∉ CommandStackFrames.writes
      (FactorAssignmentProgram.liftLow c input output) :=
  CommandStackFrames.not_mem_liftCommand _ _ _ _ _ _ lowStack_not_851

private theorem entryScratch_not_851 :
    (851 : Fin 896) ∉ FactorAssignmentProgram.entryScratch := by
  have ht : (851 : Fin 896) ∉ FactorTableProgram.entryPorts := by
    simp only [FactorTableProgram.entryPorts,List.mem_append]
    rintro (h|h)
    · obtain ⟨j,_,hj⟩ := List.mem_map.mp h
      exact FactorTableProgram.basePort_outside 851 (Or.inr (by decide)) ⟨j,hj⟩
    · norm_num at h
  have hc : (851 : Fin 896) ∉
      FactorAssignmentProgram.callbackScratch.map FactorAssignmentProgram.lowStack := by
    rintro h
    obtain ⟨j,_,hj⟩ := List.mem_map.mp h
    exact lowStack_not_851 ⟨j,hj⟩
  simp [FactorAssignmentProgram.entryScratch,hc,ht]

private theorem prepareIncidence_not_851 :
    (851 : Fin 896) ∉ CommandStackFrames.writes FactorAssignmentProgram.prepareIncidence :=
  not_mem_union_iff.mpr
    ⟨liftLow_not_851 _ _ _,FactorTableProgram.caller_not_mem_851⟩

private theorem choose_not_851 :
    (851 : Fin 896) ∉ CommandStackFrames.writes FactorAssignmentProgram.choose := by
  have hh : (851 : Fin 896) ∉ CommandStackFrames.writes FactorAssignmentProgram.hashFactor :=
    not_mem_union_iff.mpr ⟨prepareIncidence_not_851,liftLow_not_851 _ _ _⟩
  have hm : (851 : Fin 896) ∉ CommandStackFrames.writes FactorAssignmentProgram.markedFactor :=
    not_mem_union_iff.mpr ⟨prepareIncidence_not_851,liftLow_not_851 _ _ _⟩
  simp [FactorAssignmentProgram.choose,CommandStackFrames.writes,
    CommandStackFrames.baseWrites,hh,hm]

private theorem callback_not_851 :
    (851 : Fin 896) ∉ CommandStackFrames.writes FactorAssignmentProgram.callback := by
  have hc : (851 : Fin 896) ∉ CommandStackFrames.writes FactorAssignmentProgram.clearCallback :=
    CommandStackFrames.not_mem_liftCommand _ _ _ _ _ _ lowStack_not_851
  have he : (851 : Fin 896) ∉ CommandStackFrames.writes (FactorAssignmentProgram.clear 149) :=
    CommandStackFrames.not_mem_clearProgram _ _ _ _ (by decide)
  have hr : (851 : Fin 896) ∉ CommandStackFrames.writes FactorAssignmentProgram.returnToRecords := by
    simp [FactorAssignmentProgram.returnToRecords,CommandStackFrames.writes,
      CommandStackFrames.baseWrites,StructuredProgram.Atom.instr,ProgramLogic.stackWrites]
  simp only [FactorAssignmentProgram.callback, CommandStackFrames.writes,
    not_mem_union_iff]
  exact ⟨hc,liftLow_not_851 _ _ _,choose_not_851,he,hr⟩

/-- The pair accumulator is never popped or pushed by the actual assignment
program. This stronger prefix frame is not asserted for copied input masters. -/
theorem assignment_not_mem_851 :
    (851 : Fin 896) ∉ CommandStackFrames.writes FactorAssignmentProgram.assignment := by
  have hi : (851 : Fin 896) ∉ CommandStackFrames.writes FactorAssignmentProgram.initialize := by
    apply CommandStackFrames.not_mem_liftCommand_of
    intro j hj
    change j=851 at hj
    subst j
    exact CommandStackFrames.not_mem_clearMany _ _ entryScratch_not_851
  have hs : (851 : Fin 896) ∉ CommandStackFrames.writes FactorAssignmentProgram.setup :=
    CommandStackFrames.not_mem_liftCommand _ _ _ _ _ _ lowStack_not_851
  have hl : (851 : Fin 896) ∉ CommandStackFrames.writes FactorAssignmentProgram.loop :=
    CommandStackFrames.not_mem_record_iterate FactorAssignmentProgram.ports _ _
      callback_not_851 (by decide) (by decide)
  have copy_safe (src dst : Fin 896) (hsrc : (851 : Fin 896)≠src)
      (hdst : (851 : Fin 896)≠dst) :
      (851 : Fin 896) ∉ CommandStackFrames.writes (FactorAssignmentProgram.copy src dst) :=
    CommandStackFrames.not_mem_copyProgram _ _ _ _ _ _ hsrc hdst (by decide)
  have hc : (851 : Fin 896) ∉ CommandStackFrames.writes (FactorAssignmentProgram.clear 151) :=
    CommandStackFrames.not_mem_clearProgram _ _ _ _ (by decide)
  simp only [FactorAssignmentProgram.assignment,FactorAssignmentProgram.product,
    FactorAssignmentProgram.move, CommandStackFrames.writes, not_mem_union_iff]
  exact ⟨hi,hs,copy_safe _ _ (by decide) (by decide),copy_safe _ _ (by decide) (by decide),
    hl,copy_safe _ _ (by decide) (by decide),hc⟩

theorem assignment_trace_pair_frame {steps : ℕ}
    {a b : Cfg 40 896 (StructuredCalls.size FactorAssignmentProgram.assignment+1)}
    (ht : Trace FactorAssignmentProgram.program steps a b) : b.stacks 851=a.stacks 851 :=
  CommandStackFrames.compiled_trace_stack_frame _ _ _ ht _ assignment_not_mem_851

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorCommandFrames
