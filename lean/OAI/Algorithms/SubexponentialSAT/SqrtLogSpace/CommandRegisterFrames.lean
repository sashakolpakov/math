import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.StackRoutines
import OAI.Algorithms.SubexponentialSAT.RecordPrograms

/-! Register frames derived from the actual finite instruction tables and
structured command syntax. These footprints describe code, not an assumed
semantic behavior of a callback. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandRegisterFrames

open OAI BitProgram ProgramLogic

/-- All register destinations in a concrete finite instruction table. -/
def programWrites {r s l : ℕ} (p : Program r s l) : Finset (Fin r) :=
  Finset.univ.biUnion (fun label => registerWrites (p.code label))

@[simp] theorem mem_programWrites {r s l : ℕ} (p : Program r s l) (i : Fin r) :
    i ∈ programWrites p ↔ ∃ label, i ∈ registerWrites (p.code label) := by
  simp [programWrites]

/-- Base-command footprint uses the original concrete instruction for atoms. -/
def baseWrites {r s : ℕ} : StructuredProgram.Cmd r s → Finset (Fin r)
  | .skip => ∅
  | .atom atom => registerWrites (atom.instr (0 : Fin 1))
  | .seq first second => baseWrites first ∪ baseWrites second
  | .ite _ yes no => baseWrites yes ∪ baseWrites no
  | .while _ body => baseWrites body

/-- Calls contribute their actual finite table; guards only read registers. -/
def writes {r s : ℕ} : StructuredCalls.Cmd r s → Finset (Fin r)
  | .base c => baseWrites c
  | .call p => programWrites p
  | .seq first second => writes first ∪ writes second
  | .ite _ yes no => writes yes ∪ writes no
  | .while _ body => writes body

@[simp] theorem not_mem_programWrites {r s l : ℕ} (p : Program r s l) (i : Fin r) :
    i ∉ programWrites p ↔ ∀ label, i ∉ registerWrites (p.code label) := by
  simp only [mem_programWrites, not_exists]

theorem trace_register_frame {r s l : ℕ} (p : Program r s l)
    {steps : ℕ} {a b : Cfg r s l} (ht : Trace p steps a b)
    (i : Fin r) (hi : i ∉ programWrites p) : b.regs i = a.regs i := by
  apply ProgramLogic.frame_trace (fun c : Cfg r s l => c.regs i) ?_ ht
  intro a b hs
  exact step_register_frame p i (fun label _ => (not_mem_programWrites p i).mp hi label) hs

theorem base_eval_register_frame {r s : ℕ} {c : StructuredProgram.Cmd r s}
    {steps : ℕ} {a b : StructuredProgram.State r s}
    (ht : StructuredProgram.Eval c steps a b) (i : Fin r)
    (hi : i ∉ baseWrites c) : b.regs i = a.regs i := by
  induction ht with
  | skip => rfl
  | atom atom a => exact execInstr_register_frame (atom.instr (0 : Fin 1)) (a.withPC none) i hi
  | @seq first second _ _ _ _ _ hf hs ihf ihs =>
      have hi' : i ∉ baseWrites first ∧ i ∉ baseWrites second := by
        simpa only [baseWrites, Finset.mem_union, not_or] using hi
      exact (ihs hi'.2).trans (ihf hi'.1)
  | @ite_true test yes no n a b ht he ih =>
      have hi' : i ∉ baseWrites yes ∧ i ∉ baseWrites no := by
        simpa only [baseWrites, Finset.mem_union, not_or] using hi
      exact ih hi'.1
  | @ite_false test yes no n a b ht he ih =>
      have hi' : i ∉ baseWrites yes ∧ i ∉ baseWrites no := by
        simpa only [baseWrites, Finset.mem_union, not_or] using hi
      exact ih hi'.2
  | while_false => rfl
  | while_true _ _ _ ihb ihw => exact (ihw hi).trans (ihb hi)

/-- Every actual execution preserves each register outside the static writes. -/
theorem eval_register_frame {r s : ℕ} {c : StructuredCalls.Cmd r s}
    {steps : ℕ} {a b : StructuredCalls.State r s}
    (ht : StructuredCalls.Eval c steps a b) (i : Fin r)
    (hi : i ∉ writes c) : b.regs i = a.regs i := by
  induction ht with
  | base he => exact base_eval_register_frame he i hi
  | call p ht => exact trace_register_frame p ht i hi
  | @seq first second _ _ _ _ _ hf hs ihf ihs =>
      have hi' : i ∉ writes first ∧ i ∉ writes second := by
        simpa only [writes, Finset.mem_union, not_or] using hi
      exact (ihs hi'.2).trans (ihf hi'.1)
  | @ite_true test yes no n a b ht he ih =>
      have hi' : i ∉ writes yes ∧ i ∉ writes no := by
        simpa only [writes, Finset.mem_union, not_or] using hi
      exact ih hi'.1
  | @ite_false test yes no n a b ht he ih =>
      have hi' : i ∉ writes yes ∧ i ∉ writes no := by
        simpa only [writes, Finset.mem_union, not_or] using hi
      exact ih hi'.2
  | while_false => rfl
  | while_true _ _ _ ihb ihw => exact (ihw hi).trans (ihb hi)

/-- Relocation changes every destination by precisely the declared register map. -/
theorem relocate_writes {r s l R S L : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S) (label : Fin l → Fin L)
    (returnPc : Option (Fin L)) (instr : Instr r s l) :
    registerWrites (ProgramLinking.relocateInstr register stack label returnPc instr) =
      (registerWrites instr).image register := by
  cases instr <;> cases returnPc <;> simp [ProgramLinking.relocateInstr, registerWrites]

theorem not_mem_liftProgram {r s l R S : ℕ} (p : Program r s l)
    (register : Fin r → Fin R) (stack : Fin s → Fin S) (i : Fin R)
    (hi : ¬ ∃ j, register j = i) :
    i ∉ programWrites (ProgramLinking.liftProgram p register stack) := by
  rw [not_mem_programWrites]
  intro label
  simp only [relocate_writes, Finset.mem_image, not_exists]
  intro j hj
  exact hi ⟨j, hj.2⟩


theorem base_code_writes {r s : ℕ} (c : StructuredProgram.Cmd r s)
    {l : ℕ} (embed : StructuredProgram.Site c → Fin l) (exit : Fin l)
    (q : StructuredProgram.Site c) :
    registerWrites (StructuredProgram.code c embed exit q) ⊆ baseWrites c := by
  induction c generalizing l with
  | skip => exact q.elim
  | atom atom => cases atom <;> simp [StructuredProgram.code, StructuredProgram.Atom.instr,
      registerWrites, baseWrites]
  | seq first second ihf ihs =>
      cases q with
      | inl q => exact (ihf _ _ q).trans Finset.subset_union_left
      | inr q => exact (ihs _ _ q).trans Finset.subset_union_right
  | ite test yes no ihy ihn =>
      cases q with
      | none => simp [registerWrites]
      | some q =>
          cases q with
          | inl q => exact (ihy _ _ q).trans Finset.subset_union_left
          | inr q => exact (ihn _ _ q).trans Finset.subset_union_right
  | «while» test body ih =>
      cases q with
      | none => simp [registerWrites]
      | some q => exact ih _ _ q

theorem code_writes {r s : ℕ} (c : StructuredCalls.Cmd r s)
    {l : ℕ} (embed : StructuredCalls.Site c → Fin l) (exit : Fin l)
    (q : StructuredCalls.Site c) :
    registerWrites (StructuredCalls.code c embed exit q) ⊆ writes c := by
  induction c generalizing l with
  | base c => exact base_code_writes c embed exit q
  | call p =>
      simp only [StructuredCalls.code, relocate_writes, Finset.image_id, writes]
      intro i hi
      exact (mem_programWrites p i).mpr ⟨q, hi⟩
  | seq first second ihf ihs =>
      cases q with
      | inl q => exact (ihf _ _ q).trans Finset.subset_union_left
      | inr q => exact (ihs _ _ q).trans Finset.subset_union_right
  | ite test yes no ihy ihn =>
      cases q with
      | none => simp [registerWrites]
      | some q =>
          cases q with
          | inl q => exact (ihy _ _ q).trans Finset.subset_union_left
          | inr q => exact (ihn _ _ q).trans Finset.subset_union_right
  | «while» test body ih =>
      cases q with
      | none => simp [registerWrites]
      | some q => exact ih _ _ q

/-- Compiling guards, sequencing and return jumps introduces no register writes. -/
theorem compiled_writes {r s : ℕ} (c : StructuredCalls.Cmd r s)
    (input output : Fin s) :
    programWrites (StructuredCalls.compiled c input output) ⊆ writes c := by
  intro i hi
  obtain ⟨label, hl⟩ := (mem_programWrites _ i).mp hi
  obtain ⟨q, rfl⟩ := (StructuredCalls.labelEquiv c).surjective label
  cases q with
  | none =>
      change i ∈ registerWrites ((StructuredCalls.compiled c input output).code
        (StructuredCalls.exitAddress c)) at hl
      rw [StructuredCalls.compiled_exit] at hl
      simp [registerWrites] at hl
  | some q =>
      change i ∈ registerWrites ((StructuredCalls.compiled c input output).code
        (StructuredCalls.siteAddress c q)) at hl
      rw [StructuredCalls.compiled_site] at hl
      apply code_writes c _ _ q
      exact hl

theorem not_mem_compiled {r s : ℕ} (c : StructuredCalls.Cmd r s)
    (input output : Fin s) (i : Fin r) (hi : i ∉ writes c) :
    i ∉ programWrites (StructuredCalls.compiled c input output) :=
  fun hm => hi (compiled_writes c input output hm)

theorem compiled_trace_register_frame {r s : ℕ} (c : StructuredCalls.Cmd r s)
    (input output : Fin s) {steps : ℕ}
    {a b : Cfg r s (StructuredCalls.size c + 1)}
    (ht : Trace (StructuredCalls.compiled c input output) steps a b)
    (i : Fin r) (hi : i ∉ writes c) : b.regs i = a.regs i :=
  trace_register_frame _ ht i (not_mem_compiled c input output i hi)

theorem not_mem_liftCommand {r s R S : ℕ} (c : StructuredCalls.Cmd r s)
    (input output : Fin s) (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (i : Fin R) (hi : ¬ ∃ j, register j = i) :
    i ∉ writes (StructuredCalls.liftCommand c input output register stack) :=
  not_mem_liftProgram _ register stack i hi

/-- These primitive loops can only write their explicit value/presence registers. -/
theorem not_mem_clearProgram {r s : ℕ} (src : Fin s) (value present i : Fin r)
    (hv : i ≠ value) (hp : i ≠ present) :
    i ∉ programWrites (StackRoutines.clearProgram src value present) := by
  rw [not_mem_programWrites]
  intro label
  fin_cases label <;> simp [registerWrites, hv, hp]

theorem not_mem_copyProgram {r s : ℕ} (src dst tmp : Fin s) (value present i : Fin r)
    (hv : i ≠ value) (hp : i ≠ present) :
    i ∉ programWrites (StackRoutines.copyProgram src dst tmp value present) := by
  rw [not_mem_programWrites]
  intro label
  fin_cases label <;> simp [registerWrites, hv, hp]

theorem not_mem_transferProgram {r s : ℕ} (src dst : Fin s) (value present i : Fin r)
    (hv : i ≠ value) (hp : i ≠ present) :
    i ∉ programWrites (StackRoutines.transferProgram src dst value present) := by
  rw [not_mem_programWrites]
  intro label
  fin_cases label <;> simp [registerWrites, hv, hp]



theorem liftProgram_writes {r s l R S : ℕ} (p : Program r s l)
    (register : Fin r → Fin R) (stack : Fin s → Fin S) :
    programWrites (ProgramLinking.liftProgram p register stack) =
      (programWrites p).image register := by
  ext i
  simp only [mem_programWrites, ProgramLinking.liftProgram, relocate_writes,
    Finset.mem_image]
  constructor
  · rintro ⟨label, j, hj, hji⟩
    exact ⟨j, ⟨label, hj⟩, hji⟩
  · rintro ⟨j, ⟨label, hj⟩, hji⟩
    exact ⟨label, j, hj, hji⟩

theorem not_mem_liftCommand_of {r s R S : ℕ} (c : StructuredCalls.Cmd r s)
    (input output : Fin s) (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (i : Fin R) (hi : ∀ j, register j = i → j ∉ writes c) :
    i ∉ writes (StructuredCalls.liftCommand c input output register stack) := by
  change i ∉ programWrites (ProgramLinking.liftProgram _ register stack)
  rw [liftProgram_writes]
  rintro hm
  obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hm
  exact hi j hji (compiled_writes c input output hj)

theorem not_mem_reverseProgram {r s : ℕ} (src tmp₁ tmp₂ : Fin s) (value present i : Fin r)
    (hv : i ≠ value) (hp : i ≠ present) :
    i ∉ programWrites (StackRoutines.reverseProgram src tmp₁ tmp₂ value present) := by
  rw [not_mem_programWrites]
  intro label
  fin_cases label <;> simp [registerWrites, hv, hp]

theorem not_mem_record_reader {r s : ℕ} (p : RecordPrograms.Ports r s) (i : Fin r)
    (ht : i ≠ p.tag) (hp : i ≠ p.present) :
    i ∉ writes (RecordPrograms.reader p) := by
  apply not_mem_liftProgram
  rintro ⟨j, hj⟩
  unfold RecordPrograms.registerMap at hj
  split_ifs at hj
  · exact ht hj.symm
  · exact hp hj.symm

theorem not_mem_record_iterate {r s : ℕ} (p : RecordPrograms.Ports r s)
    (callback : StructuredCalls.Cmd r s) (i : Fin r)
    (hc : i ∉ writes callback)
    (ht : i ≠ p.tag) (hp : i ≠ p.present) (hf : i ≠ p.found) :
    i ∉ writes (RecordPrograms.iterate p callback) := by
  have hr := not_mem_record_reader p i ht hp
  simp only [writes, baseWrites, StructuredProgram.Atom.instr, registerWrites,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨hf, ⟨⟨ht, hp⟩, ⟨hr, ⟨hc, ⟨ht, ⟨ht, hp⟩⟩⟩⟩⟩⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandRegisterFrames
