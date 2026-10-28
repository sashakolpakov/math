import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.RecordPrograms
import OAI.Algorithms.SubexponentialSAT.ExecCNFRecords

namespace OAI.Algorithms

/-! Concrete frame-reader and stack-cleaning calls for serialized weight data.
All calls below are fixed finite programs. Data-dependent lists occur only in
their execution specifications, never in instruction-table construction. -/

namespace SubexponentialSAT.SubexpWeightRecords

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := SubexponentialSAT.StructuredProgram.State 8 12

def fieldPorts (dst : Fin 12) (h : (11 : Fin 12) ≠ dst) : RecordPrograms.Ports 8 12 where
  tag := 0
  present := 1
  found := 2
  source := 11
  payload := dst
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := h

abbrev readField (dst : Fin 12) (h : (11 : Fin 12) ≠ dst) : Cmd 8 12 :=
  RecordPrograms.reader (fieldPorts dst h)

theorem readField_execute (dst : Fin 12) (h : (11 : Fin 12) ≠ dst)
    (d : Data) (bits tail : List Bool)
    (hsource : d.stacks 11 = Encoding.frame bits ++ tail) (hempty : d.stacks dst = []) :
    ∃ e, Eval (readField dst h) (6 * bits.length + 4) d e ∧
      e.stacks = Function.update (Function.update d.stacks 11 tail) dst bits.reverse := by
  let p := fieldPorts dst h
  let e := RecordPrograms.state p d false true (d.regs 2) tail bits.reverse
  have hstart : RecordPrograms.state p d (d.regs 0) (d.regs 1) (d.regs 2)
      (Encoding.frame bits ++ tail) [] = d :=
    RecordPrograms.state_eq_self p d _ _ _ _ _ rfl rfl rfl hsource hempty
  have ht := RecordPrograms.reader_eval p d bits tail [] (d.regs 0) (d.regs 1) (d.regs 2)
  rw [hstart] at ht
  refine ⟨e, ?_, rfl⟩
  simpa only [List.append_nil] using ht

def smallRegs (i : Fin 3) : Fin 8 := ⟨i.val, by omega⟩

theorem smallRegs_injective : Function.Injective smallRegs := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 8 => k.val) h

def sourcePort (_ : Fin 1) : Fin 12 := 11

theorem sourcePort_injective : Function.Injective sourcePort := by
  intro i j _
  exact Subsingleton.elim i j

abbrev skipFrameProgram : Program 3 1 11 := { ExecCNFRecords.skipProgram with entry := 4 }

abbrev skipField : Cmd 8 12 :=
  .call (ProgramLinking.liftProgram skipFrameProgram smallRegs sourcePort)

private theorem extend_restrict {A B C : Type*} (f : A → B) (g : B → C) :
    Function.extend f (g ∘ f) g = g := by
  classical
  funext b
  by_cases h : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := h
    exact Function.FactorsThrough.extend_apply (fun _ _ h => congrArg g h) g a
  · exact Function.extend_apply' _ _ _ h

private theorem embed_restrict {r s R S : ℕ} (rmap : Fin r → Fin R)
    (smap : Fin s → Fin S) (d : State R S) :
    embedState rmap smap d ⟨d.regs ∘ rmap, d.stacks ∘ smap⟩ = d := by
  cases d
  simp only [embedState, extend_restrict]

theorem skipField_execute (d : Data) (bits tail : List Bool)
    (hsource : d.stacks 11 = Encoding.frame bits ++ tail) :
    ∃ e, Eval skipField (5 * bits.length + 4) d e ∧
      e.stacks = Function.update d.stacks 11 tail := by
  let a : State 3 1 := ⟨ExecCNFRecords.regs (d.regs 0) (d.regs 1) (d.regs 2),
    fun _ => Encoding.frame bits ++ tail⟩
  let b : State 3 1 := ⟨ExecCNFRecords.regs false true (d.regs 2), fun _ => tail⟩
  have ha : a = ⟨d.regs ∘ smallRegs, d.stacks ∘ sourcePort⟩ := by
    apply congrArg₂ SubexponentialSAT.StructuredProgram.State.mk
    · funext i
      fin_cases i <;> rfl
    · funext i
      exact hsource.symm
  have ht : Trace skipFrameProgram (5 * bits.length + 4)
      (a.withPC (some skipFrameProgram.entry)) (b.withPC none) :=
    ExecCNFRecords.frame_trace bits tail (d.regs 0) (d.regs 1) (d.regs 2)
  have he := eval_call_lifted skipFrameProgram smallRegs sourcePort d
    smallRegs_injective sourcePort_injective ht
  rw [ha, embed_restrict] at he
  refine ⟨embedState smallRegs sourcePort d b, he, ?_⟩
  funext j
  by_cases hj : j = 11
  · subst j
    exact (embedState_stack _ _ _ _ sourcePort_injective 0).trans (by simp [b])
  · rw [embedState_stack_frame _ _ _ _ j (by
      rintro ⟨i, hi⟩
      exact hj hi.symm)]
    simp [hj]

abbrev clearField (src : Fin 12) : Cmd 8 12 := .call (StackRoutines.clearProgram src 0 1)

theorem clearField_execute (src : Fin 12) (d : Data) :
    ∃ e, Eval (clearField src) (2 * (d.stacks src).length + 3) d e ∧
      e.stacks = Function.update d.stacks src [] := by
  have ht := StackRoutines.clearProgram_trace src (0 : Fin 8) 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace (StackRoutines.clearProgram src 0 1) ht 2 rfl rfl
  refine ⟨⟨readRegs d.regs 0 1 none, Function.update d.stacks src []⟩, .call _ ?_, rfl⟩
  simpa [StackRoutines.clearResult, StackRoutines.clearStacks, Nat.add_assoc] using hh

abbrev readTag : Cmd 8 12 := .base (.atom (.pop 11 7 6))

theorem readTag_execute (d : Data) (bit : Bool) (tail : List Bool)
    (hsource : d.stacks 11 = bit :: tail) :
    ∃ e, Eval readTag 1 d e ∧ e.stacks = Function.update d.stacks 11 tail ∧
      e.regs 7 = bit := by
  let e := (SubexponentialSAT.StructuredProgram.Atom.pop 11 7 6).eval d
  refine ⟨e, .base (.atom _ _), ?_, ?_⟩
  · simp [e, SubexponentialSAT.StructuredProgram.Atom.eval, SubexponentialSAT.StructuredProgram.Atom.instr,
      SubexponentialSAT.StructuredProgram.State.ofCfg, execInstr, hsource]
  · simp [e, SubexponentialSAT.StructuredProgram.Atom.eval, SubexponentialSAT.StructuredProgram.Atom.instr,
      SubexponentialSAT.StructuredProgram.State.ofCfg, execInstr,
      hsource, readRegs]

end SubexponentialSAT.SubexpWeightRecords

end OAI.Algorithms
