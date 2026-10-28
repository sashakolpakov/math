import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.StructuredProgram
import OAI.Algorithms.SubexponentialSAT.ProgramLinking

namespace OAI.Algorithms

/-!
# Structured invocation of existing finite bit programs

A call contains a fixed finite instruction table. Its execution premise is an
actual trace of that table, rather than a semantic or cost oracle. Compilation
relocates all its instructions and replaces each halt by a return jump. Thus
arbitrary cyclic subroutines can occur inside structured loops without manually
assigning global labels.
-/

namespace SubexponentialSAT.StructuredCalls

open SubexponentialSAT.BitProgram

abbrev State := StructuredProgram.State

inductive Cmd (r s : ℕ) where
  | base (c : StructuredProgram.Cmd r s)
  | call {labels : ℕ} (program : Program r s labels)
  | seq (first second : Cmd r s)
  | ite (test : Fin r) (yes no : Cmd r s)
  | while (test : Fin r) (body : Cmd r s)

/-- A call's cost is its actual instruction-trace length, including the source
halt which becomes the compiled return jump. -/
inductive Eval {r s : ℕ} : Cmd r s → ℕ → State r s → State r s → Prop
  | base {c n a b} : StructuredProgram.Eval c n a b → Eval (.base c) n a b
  | call {labels} (p : Program r s labels) {n a b} :
      Trace p n (a.withPC (some p.entry)) (b.withPC none) → Eval (.call p) n a b
  | seq {first second n m a b c} : Eval first n a b → Eval second m b c →
      Eval (.seq first second) (n + m) a c
  | ite_true {test yes no n a b} : a.regs test = true → Eval yes n a b →
      Eval (.ite test yes no) (n + 1) a b
  | ite_false {test yes no n a b} : a.regs test = false → Eval no n a b →
      Eval (.ite test yes no) (n + 1) a b
  | while_false {test body a} : a.regs test = false → Eval (.while test body) 1 a a
  | while_true {test body n m a b c} : a.regs test = true → Eval body n a b →
      Eval (.while test body) m b c → Eval (.while test body) (n + m + 1) a c

abbrev Site {r s : ℕ} : Cmd r s → Type
  | .base c => StructuredProgram.Site c
  | @Cmd.call _ _ labels _ => Fin labels
  | .seq first second => Site first ⊕ Site second
  | .ite _ yes no => Option (Site yes ⊕ Site no)
  | .while _ body => Option (Site body)

abbrev size {r s : ℕ} : Cmd r s → ℕ
  | .base c => StructuredProgram.size c
  | @Cmd.call _ _ labels _ => labels
  | .seq first second => size first + size second
  | .ite _ yes no => size yes + size no + 1
  | .while _ body => size body + 1

/-- Finite control enumeration is computed directly from the fixed syntax. -/
abbrev siteEquiv {r s : ℕ} : (c : Cmd r s) → Site c ≃ Fin (size c)
  | .base c => StructuredProgram.siteEquiv c
  | .call _ => Equiv.refl _
  | .seq first second =>
      ((siteEquiv first).sumCongr (siteEquiv second)).trans finSumFinEquiv
  | .ite _ yes no =>
      (((siteEquiv yes).sumCongr (siteEquiv no)).trans finSumFinEquiv).optionCongr.trans
        (finSuccEquiv _).symm
  | .while _ body => (siteEquiv body).optionCongr.trans (finSuccEquiv _).symm

abbrev entry {r s l : ℕ} (c : Cmd r s) (embed : Site c → Fin l) (exit : Fin l) : Fin l :=
  match c with
  | .base c => StructuredProgram.entry c embed exit
  | .call p => embed p.entry
  | .seq first second =>
      entry first (embed ∘ Sum.inl) (entry second (embed ∘ Sum.inr) exit)
  | .ite _ _ _ => embed none
  | .while _ _ => embed none

/-- Calls use the proved concrete instruction relocation, including every
internal branch and each return instruction. -/
abbrev code {r s l : ℕ} (c : Cmd r s) (embed : Site c → Fin l) (exit : Fin l) :
    Site c → Instr r s l :=
  match c with
  | .base c => StructuredProgram.code c embed exit
  | .call p => fun q => ProgramLinking.relocateInstr id id embed (some exit) (p.code q)
  | .seq first second => fun q => match q with
      | .inl x => code first (embed ∘ Sum.inl) (entry second (embed ∘ Sum.inr) exit) x
      | .inr x => code second (embed ∘ Sum.inr) exit x
  | .ite test yes no => fun q => match q with
      | none => .branch test (entry yes (fun x => embed (some (.inl x))) exit)
          (entry no (fun x => embed (some (.inr x))) exit)
      | some (.inl x) => code yes (fun x => embed (some (.inl x))) exit x
      | some (.inr x) => code no (fun x => embed (some (.inr x))) exit x
  | .while test body => fun q => match q with
      | none => .branch test (entry body (embed ∘ some) (embed none)) exit
      | some x => code body (embed ∘ some) (embed none) x

/-- Exact execution preservation, proved with the concrete subroutine linker
in the call case. -/
theorem eval_trace {r s : ℕ} {c : Cmd r s} {n : ℕ} {a b : State r s}
    (h : Eval c n a b) :
    ∀ {l : ℕ} (p : Program r s l) (embed : Site c → Fin l) (exit : Fin l),
    (∀ q, p.code (embed q) = code c embed exit q) →
    Trace p n (a.withPC (some (entry c embed exit))) (b.withPC (some exit)) := by
  induction h with
  | base he =>
      intro l p embed exit hcode
      exact StructuredProgram.eval_trace he p embed exit hcode
  | @call labels routine n a b ht =>
      intro l p embed exit hcode
      have hrun := ProgramLinking.relocate_trace routine p id id embed (some exit)
        (a.withPC (some (embed routine.entry))) Function.injective_id Function.injective_id
        hcode ht
      simpa [ProgramLinking.embedCfg, ProgramLinking.relocatePc,
        StructuredProgram.State.withPC, entry] using hrun
  | @seq first second n m a b c hf hs ihf ihs =>
      intro l p embed exit hcode
      exact (ihf p (embed ∘ Sum.inl) (entry second (embed ∘ Sum.inr) exit)
        (fun q => hcode (.inl q))).trans
        (ihs p (embed ∘ Sum.inr) exit (fun q => hcode (.inr q)))
  | @ite_true test yes no n a b ht he ih =>
      intro l p embed exit hcode
      apply SubexponentialSAT.Computation.Trace.cons _
        (ih p (fun q => embed (some (.inl q))) exit (fun q => hcode (some (.inl q))))
      simp [step, StructuredProgram.State.withPC, entry, hcode none, code, execInstr, ht]
  | @ite_false test yes no n a b ht he ih =>
      intro l p embed exit hcode
      apply SubexponentialSAT.Computation.Trace.cons _
        (ih p (fun q => embed (some (.inr q))) exit (fun q => hcode (some (.inr q))))
      simp [step, StructuredProgram.State.withPC, entry, hcode none, code, execInstr, ht]
  | @while_false test body a ht =>
      intro l p embed exit hcode
      refine .cons ?_ (.refl _)
      simp [step, StructuredProgram.State.withPC, entry, hcode none, code, execInstr, ht]
  | @while_true test body n m a b c ht hb hw ihb ihw =>
      intro l p embed exit hcode
      apply SubexponentialSAT.Computation.Trace.cons _
        ((ihb p (embed ∘ some) (embed none) (fun q => hcode (some q))).trans
          (ihw p embed exit hcode))
      simp [step, StructuredProgram.State.withPC, entry, hcode none, code, execInstr, ht]

abbrev labelEquiv {r s : ℕ} (c : Cmd r s) : Option (Site c) ≃ Fin (size c + 1) :=
  (siteEquiv c).optionCongr.trans (finSuccEquiv _).symm

abbrev siteAddress {r s : ℕ} (c : Cmd r s) (q : Site c) : Fin (size c + 1) :=
  labelEquiv c (some q)

abbrev exitAddress {r s : ℕ} (c : Cmd r s) : Fin (size c + 1) := labelEquiv c none

/-- The full finite instruction table is computably generated from the fixed
syntax and finite subroutine tables. No runtime stack data is inspected. -/
def compiled {r s : ℕ} (c : Cmd r s) (inputStack outputStack : Fin s) :
    Program r s (size c + 1) where
  inputStack := inputStack
  outputStack := outputStack
  entry := entry c (siteAddress c) (exitAddress c)
  code label := match (labelEquiv c).symm label with
    | none => .halt
    | some q => code c (siteAddress c) (exitAddress c) q

@[simp] theorem compiled_site {r s : ℕ} (c : Cmd r s)
    (inputStack outputStack : Fin s) (q : Site c) :
    (compiled c inputStack outputStack).code (siteAddress c q) =
      code c (siteAddress c) (exitAddress c) q := by
  change (match ((siteEquiv c).optionCongr).symm
      (((siteEquiv c).optionCongr) (some q)) with
    | none => Instr.halt
    | some q => code c (siteAddress c) (exitAddress c) q) = _
  rw [Equiv.symm_apply_apply]

@[simp] theorem compiled_exit {r s : ℕ} (c : Cmd r s)
    (inputStack outputStack : Fin s) :
    (compiled c inputStack outputStack).code (exitAddress c) = Instr.halt := by
  change (match ((siteEquiv c).optionCongr).symm
      (((siteEquiv c).optionCongr) none) with
    | none => Instr.halt
    | some q => code c (siteAddress c) (exitAddress c) q) = _
  rw [Equiv.symm_apply_apply]

theorem compiled_trace {r s : ℕ} {c : Cmd r s} {n : ℕ} {a b : State r s}
    (h : Eval c n a b) (inputStack outputStack : Fin s) :
    Trace (compiled c inputStack outputStack) n
      (a.withPC (some (compiled c inputStack outputStack).entry))
      (b.withPC (some (exitAddress c))) :=
  eval_trace h _ _ _ (compiled_site c inputStack outputStack)

theorem compiled_halt_trace {r s : ℕ} {c : Cmd r s} {n : ℕ} {a b : State r s}
    (h : Eval c n a b) (inputStack outputStack : Fin s) :
    Trace (compiled c inputStack outputStack) (n + 1)
      (a.withPC (some (compiled c inputStack outputStack).entry)) (b.withPC none) := by
  apply (compiled_trace h inputStack outputStack).trans
  refine .cons ?_ (.refl _)
  rw [step]
  simp only [StructuredProgram.State.withPC, Option.map_some]
  rw [compiled_exit]
  rfl

theorem compiled_io_trace {r s : ℕ} {c : Cmd r s} {n : ℕ}
    (inputStack outputStack : Fin s) {input output : List Bool}
    (h : Eval c n (StructuredProgram.ioState inputStack input)
      (StructuredProgram.ioState outputStack output)) :
    Trace (compiled c inputStack outputStack) (n + 1)
      (initial (compiled c inputStack outputStack) input)
      (terminal (compiled c inputStack outputStack) output) :=
  compiled_halt_trace h inputStack outputStack

theorem primitive_execution {r s : ℕ} {c : Cmd r s} {n : ℕ} {a b : State r s}
    (h : Eval c n a b) (inputStack outputStack : Fin s) :
    let p := compiled c inputStack outputStack
    Computation.RunsIn (BitProgram.primitive p).step
      (BitProgram.primitiveOverhead p * (n + 1))
      (BitProgram.primitiveCfg p (a.withPC (some p.entry)))
      (BitProgram.primitiveCfg p (b.withPC none)) :=
  BitProgram.primitive_trace _ (compiled_halt_trace h inputStack outputStack)

theorem primitive_outputs {r s : ℕ} {c : Cmd r s} {n : ℕ}
    (inputStack outputStack : Fin s) {input : List Bool} {answer : Bool}
    (h : Eval c n (StructuredProgram.ioState inputStack input)
      (StructuredProgram.ioState outputStack [answer])) :
    let p := compiled c inputStack outputStack
    (BitProgram.primitive p).OutputsInTime input answer
      (BitProgram.primitiveOverhead p * (n + 1)) :=
  BitProgram.primitive_outputs _ ⟨n + 1, le_rfl, compiled_io_trace inputStack outputStack h⟩

/-- Mathematical data embedding for a subroutine's assigned ports. The finite
compiled instructions use the port maps directly; they never execute this
Function.extend expression. -/
noncomputable def embedState {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : State R S) (d : State r s) : State R S :=
  ⟨Function.extend register d.regs frame.regs, Function.extend stack d.stacks frame.stacks⟩

theorem embedState_register {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : State R S) (d : State r s)
    (hinj : Function.Injective register) (i : Fin r) :
    (embedState register stack frame d).regs (register i) = d.regs i :=
  hinj.extend_apply _ _ _

theorem embedState_stack {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : State R S) (d : State r s)
    (hinj : Function.Injective stack) (i : Fin s) :
    (embedState register stack frame d).stacks (stack i) = d.stacks i :=
  hinj.extend_apply _ _ _

theorem embedState_register_frame {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : State R S) (d : State r s) (i : Fin R)
    (hi : ¬ ∃ j, register j = i) :
    (embedState register stack frame d).regs i = frame.regs i :=
  Function.extend_apply' _ _ _ hi

theorem embedState_stack_frame {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : State R S) (d : State r s) (i : Fin S)
    (hi : ¬ ∃ j, stack j = i) :
    (embedState register stack frame d).stacks i = frame.stacks i :=
  Function.extend_apply' _ _ _ hi

/-- Invoke an existing smaller program using fixed injective port assignments.
Its exact trace count is retained, and all unassigned caller data is framed. -/
theorem eval_call_lifted {r s l R S : ℕ} (p : Program r s l)
    (register : Fin r → Fin R) (stack : Fin s → Fin S) (frame : State R S)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    {n : ℕ} {a b : State r s}
    (h : Trace p n (a.withPC (some p.entry)) (b.withPC none)) :
    Eval (.call (ProgramLinking.liftProgram p register stack)) n
      (embedState register stack frame a) (embedState register stack frame b) := by
  apply Eval.call
  simpa [ProgramLinking.embedCfg, ProgramLinking.relocatePc, embedState,
    StructuredProgram.State.withPC, ProgramLinking.liftProgram] using
    ProgramLinking.liftProgram_trace p register stack (frame.withPC none) hregister hstack h

end SubexponentialSAT.StructuredCalls

end OAI.Algorithms
