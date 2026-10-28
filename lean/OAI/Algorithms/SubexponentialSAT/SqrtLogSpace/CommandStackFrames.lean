import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.StackRoutines
import OAI.Algorithms.SubexponentialSAT.RecordPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms

/-! Stack frames derived from the actual finite instruction tables and
structured command syntax. These footprints describe code, not an assumed
semantic behavior of a callback. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandStackFrames

open OAI BitProgram ProgramLogic

private theorem not_mem_union {α : Type*} [DecidableEq α]
    {a : α} {s t : Finset α} : a ∉ s ∪ t ↔ a ∉ s ∧ a ∉ t := by
  simp only [Finset.mem_union, not_or]

/-- All stack destinations in a concrete finite instruction table. -/
def programWrites {r s l : ℕ} (p : Program r s l) : Finset (Fin s) :=
  Finset.univ.biUnion (fun label => stackWrites (p.code label))

@[simp] theorem mem_programWrites {r s l : ℕ} (p : Program r s l) (i : Fin s) :
    i ∈ programWrites p ↔ ∃ label, i ∈ stackWrites (p.code label) := by
  simp [programWrites]

/-- Base-command footprint uses the original concrete instruction for atoms. -/
def baseWrites {r s : ℕ} : StructuredProgram.Cmd r s → Finset (Fin s)
  | .skip => ∅
  | .atom atom => stackWrites (atom.instr (0 : Fin 1))
  | .seq first second => baseWrites first ∪ baseWrites second
  | .ite _ yes no => baseWrites yes ∪ baseWrites no
  | .while _ body => baseWrites body

/-- Calls contribute their actual finite table; guards only read registers. -/
def writes {r s : ℕ} : StructuredCalls.Cmd r s → Finset (Fin s)
  | .base c => baseWrites c
  | .call p => programWrites p
  | .seq first second => writes first ∪ writes second
  | .ite _ yes no => writes yes ∪ writes no
  | .while _ body => writes body

@[simp] theorem not_mem_programWrites {r s l : ℕ} (p : Program r s l) (i : Fin s) :
    i ∉ programWrites p ↔ ∀ label, i ∉ stackWrites (p.code label) := by
  simp only [mem_programWrites, not_exists]

theorem trace_stack_frame {r s l : ℕ} (p : Program r s l)
    {steps : ℕ} {a b : Cfg r s l} (ht : Trace p steps a b)
    (i : Fin s) (hi : i ∉ programWrites p) : b.stacks i = a.stacks i := by
  apply ProgramLogic.frame_trace (fun c : Cfg r s l => c.stacks i) ?_ ht
  intro a b hs
  exact step_stack_frame p i (fun label _ => (not_mem_programWrites p i).mp hi label) hs

theorem base_eval_stack_frame {r s : ℕ} {c : StructuredProgram.Cmd r s}
    {steps : ℕ} {a b : StructuredProgram.State r s}
    (ht : StructuredProgram.Eval c steps a b) (i : Fin s)
    (hi : i ∉ baseWrites c) : b.stacks i = a.stacks i := by
  induction ht with
  | skip => rfl
  | atom atom a => exact execInstr_stack_frame (atom.instr (0 : Fin 1)) (a.withPC none) i hi
  | seq hf hs ihf ihs =>
      exact (ihs (not_mem_union.mp hi).2).trans (ihf (not_mem_union.mp hi).1)
  | ite_true _ _ ih => exact ih (not_mem_union.mp hi).1
  | ite_false _ _ ih => exact ih (not_mem_union.mp hi).2
  | while_false => rfl
  | while_true _ _ _ ihb ihw => exact (ihw hi).trans (ihb hi)

/-- Every actual execution preserves each stack outside the static writes. -/
theorem eval_stack_frame {r s : ℕ} {c : StructuredCalls.Cmd r s}
    {steps : ℕ} {a b : StructuredCalls.State r s}
    (ht : StructuredCalls.Eval c steps a b) (i : Fin s)
    (hi : i ∉ writes c) : b.stacks i = a.stacks i := by
  induction ht with
  | base he => exact base_eval_stack_frame he i hi
  | call p ht => exact trace_stack_frame p ht i hi
  | seq hf hs ihf ihs =>
      exact (ihs (not_mem_union.mp hi).2).trans (ihf (not_mem_union.mp hi).1)
  | ite_true _ _ ih => exact ih (not_mem_union.mp hi).1
  | ite_false _ _ ih => exact ih (not_mem_union.mp hi).2
  | while_false => rfl
  | while_true _ _ _ ihb ihw => exact (ihw hi).trans (ihb hi)

/-- Relocation changes every destination by precisely the declared stack map. -/
theorem relocate_writes {r s l R S L : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S) (label : Fin l → Fin L)
    (returnPc : Option (Fin L)) (instr : Instr r s l) :
    stackWrites (ProgramLinking.relocateInstr register stack label returnPc instr) =
      (stackWrites instr).image stack := by
  cases instr <;> cases returnPc <;> simp [ProgramLinking.relocateInstr, stackWrites]

theorem not_mem_liftProgram {r s l R S : ℕ} (p : Program r s l)
    (register : Fin r → Fin R) (stack : Fin s → Fin S) (i : Fin S)
    (hi : ¬ ∃ j, stack j = i) :
    i ∉ programWrites (ProgramLinking.liftProgram p register stack) := by
  rw [not_mem_programWrites]
  intro label
  simp only [relocate_writes, Finset.mem_image, not_exists]
  intro j hj
  exact hi ⟨j, hj.2⟩


theorem base_code_writes {r s : ℕ} (c : StructuredProgram.Cmd r s)
    {l : ℕ} (embed : StructuredProgram.Site c → Fin l) (exit : Fin l)
    (q : StructuredProgram.Site c) :
    stackWrites (StructuredProgram.code c embed exit q) ⊆ baseWrites c := by
  induction c generalizing l with
  | skip => exact q.elim
  | atom atom => cases atom <;> simp [StructuredProgram.code, StructuredProgram.Atom.instr,
      stackWrites, baseWrites]
  | seq first second ihf ihs =>
      cases q with
      | inl q => exact (ihf _ _ q).trans Finset.subset_union_left
      | inr q => exact (ihs _ _ q).trans Finset.subset_union_right
  | ite test yes no ihy ihn =>
      cases q with
      | none => simp [stackWrites]
      | some q =>
          cases q with
          | inl q => exact (ihy _ _ q).trans Finset.subset_union_left
          | inr q => exact (ihn _ _ q).trans Finset.subset_union_right
  | «while» test body ih =>
      cases q with
      | none => simp [stackWrites]
      | some q => exact ih _ _ q

theorem code_writes {r s : ℕ} (c : StructuredCalls.Cmd r s)
    {l : ℕ} (embed : StructuredCalls.Site c → Fin l) (exit : Fin l)
    (q : StructuredCalls.Site c) :
    stackWrites (StructuredCalls.code c embed exit q) ⊆ writes c := by
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
      | none => simp [stackWrites]
      | some q =>
          cases q with
          | inl q => exact (ihy _ _ q).trans Finset.subset_union_left
          | inr q => exact (ihn _ _ q).trans Finset.subset_union_right
  | «while» test body ih =>
      cases q with
      | none => simp [stackWrites]
      | some q => exact ih _ _ q

/-- Compiling guards, sequencing and return jumps introduces no stack writes. -/
theorem compiled_writes {r s : ℕ} (c : StructuredCalls.Cmd r s)
    (input output : Fin s) :
    programWrites (StructuredCalls.compiled c input output) ⊆ writes c := by
  intro i hi
  obtain ⟨label, hl⟩ := (mem_programWrites _ i).mp hi
  change i ∈ stackWrites (match (StructuredCalls.labelEquiv c).symm label with
    | none => .halt | some q => StructuredCalls.code c (StructuredCalls.siteAddress c)
        (StructuredCalls.exitAddress c) q) at hl
  cases hq : (StructuredCalls.labelEquiv c).symm label with
  | none =>
      rw [hq] at hl
      simp [stackWrites] at hl
  | some q =>
      rw [hq] at hl
      exact code_writes c _ _ q hl

theorem not_mem_compiled {r s : ℕ} (c : StructuredCalls.Cmd r s)
    (input output : Fin s) (i : Fin s) (hi : i ∉ writes c) :
    i ∉ programWrites (StructuredCalls.compiled c input output) :=
  fun hm => hi (compiled_writes c input output hm)

theorem compiled_trace_stack_frame {r s : ℕ} (c : StructuredCalls.Cmd r s)
    (input output : Fin s) {steps : ℕ}
    {a b : Cfg r s (StructuredCalls.size c + 1)}
    (ht : Trace (StructuredCalls.compiled c input output) steps a b)
    (i : Fin s) (hi : i ∉ writes c) : b.stacks i = a.stacks i :=
  trace_stack_frame _ ht i (not_mem_compiled c input output i hi)

theorem not_mem_liftCommand {r s R S : ℕ} (c : StructuredCalls.Cmd r s)
    (input output : Fin s) (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (i : Fin S) (hi : ¬ ∃ j, stack j = i) :
    i ∉ writes (StructuredCalls.liftCommand c input output register stack) :=
  not_mem_liftProgram _ register stack i hi

theorem liftProgram_writes {r s l R S : ℕ} (p : Program r s l)
    (register : Fin r → Fin R) (stack : Fin s → Fin S) :
    programWrites (ProgramLinking.liftProgram p register stack) =
      (programWrites p).image stack := by
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
    (i : Fin S) (hi : ∀ j, stack j = i → j ∉ writes c) :
    i ∉ writes (StructuredCalls.liftCommand c input output register stack) := by
  change i ∉ programWrites (ProgramLinking.liftProgram _ register stack)
  rw [liftProgram_writes]
  rintro hm
  obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hm
  exact hi j hji (compiled_writes c input output hj)

/-- Copying temporarily pops its source, so all three ports are written. -/
theorem not_mem_copyProgram {r s : ℕ} (src dst tmp : Fin s) (value present : Fin r)
    (i : Fin s) (hs : i ≠ src) (hd : i ≠ dst) (ht : i ≠ tmp) :
    i ∉ programWrites (StackRoutines.copyProgram src dst tmp value present) := by
  rw [not_mem_programWrites]
  intro label
  fin_cases label <;> simp [stackWrites, hs, hd, ht]

theorem not_mem_clearProgram {r s : ℕ} (src : Fin s) (value present : Fin r)
    (i : Fin s) (hi : i ≠ src) :
    i ∉ programWrites (StackRoutines.clearProgram src value present) := by
  rw [not_mem_programWrites]
  intro label
  fin_cases label <;> simp [stackWrites, hi]

theorem not_mem_transferProgram {r s : ℕ} (src dst : Fin s) (value present : Fin r)
    (i : Fin s) (hs : i ≠ src) (hd : i ≠ dst) :
    i ∉ programWrites (StackRoutines.transferProgram src dst value present) := by
  rw [not_mem_programWrites]
  intro label
  fin_cases label <;> simp [stackWrites, hs, hd]

theorem not_mem_reverseProgram {r s : ℕ} (src tmp₁ tmp₂ : Fin s) (value present : Fin r)
    (i : Fin s) (hs : i ≠ src) (h1 : i ≠ tmp₁) (h2 : i ≠ tmp₂) :
    i ∉ programWrites (StackRoutines.reverseProgram src tmp₁ tmp₂ value present) := by
  rw [not_mem_programWrites]
  intro label
  fin_cases label <;> simp [stackWrites, hs, h1, h2]

theorem not_mem_clearMany {s : ℕ} (ports : List (Fin s)) (i : Fin s)
    (hi : i ∉ ports) : i ∉ writes (SubexpSetupStorage.clearMany ports) := by
  induction ports with
  | nil => simp [SubexpSetupStorage.clearMany,writes,baseWrites]
  | cons port ports ih =>
      have hn : i ≠ port ∧ i ∉ ports := by simpa only [List.mem_cons,not_or] using hi
      exact not_mem_union.mpr
        ⟨not_mem_clearProgram port 0 1 i hn.1,ih hn.2⟩

theorem not_mem_unaryFor {r s : ℕ} (p : UnaryForPrograms.Ports r s)
    (body : StructuredCalls.Cmd r s) (i : Fin s)
    (hc : i ≠ p.counter) (hb : i ∉ writes body) :
    i ∉ writes (UnaryForPrograms.forCmd p body) := by
  simp [writes, baseWrites, StructuredProgram.Atom.instr, stackWrites, hc, hb]

theorem not_mem_record_reader {r s : ℕ} (p : RecordPrograms.Ports r s) (i : Fin s)
    (hs : i ≠ p.source) (hp : i ≠ p.payload) :
    i ∉ writes (RecordPrograms.reader p) := by
  apply not_mem_liftProgram
  rintro ⟨j,hj⟩
  unfold RecordPrograms.stackMap at hj
  split_ifs at hj
  · exact hs hj.symm
  · exact hp hj.symm

theorem not_mem_record_iterate {r s : ℕ} (p : RecordPrograms.Ports r s)
    (callback : StructuredCalls.Cmd r s) (i : Fin s)
    (hc : i ∉ writes callback) (hs : i ≠ p.source) (hp : i ≠ p.payload) :
    i ∉ writes (RecordPrograms.iterate p callback) := by
  have hr := not_mem_record_reader p i hs hp
  have hsetFound : i ∉ baseWrites (.atom (.set p.found false)) := by
    simp [baseWrites, StructuredProgram.Atom.instr, stackWrites]
  have hpopSource : i ∉ baseWrites (.atom (.pop p.source p.tag p.present)) := by
    simpa [baseWrites, StructuredProgram.Atom.instr, stackWrites] using hs
  have hsetTag : i ∉ baseWrites (.atom (.set p.tag false)) := by
    simp [baseWrites, StructuredProgram.Atom.instr, stackWrites]
  change i ∉ baseWrites (.atom (.set p.found false)) ∪
    (baseWrites (.atom (.pop p.source p.tag p.present)) ∪
      (writes (RecordPrograms.reader p) ∪
        (writes callback ∪
          (baseWrites (.atom (.set p.tag false)) ∪
            baseWrites (.atom (.pop p.source p.tag p.present))))))
  exact not_mem_union.mpr ⟨hsetFound, not_mem_union.mpr ⟨hpopSource,
    not_mem_union.mpr ⟨hr, not_mem_union.mpr ⟨hc,
      not_mem_union.mpr ⟨hsetTag, hpopSource⟩⟩⟩⟩⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandStackFrames
