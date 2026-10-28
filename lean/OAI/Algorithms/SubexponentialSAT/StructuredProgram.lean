import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ProgramLogic
import OAI.Algorithms.SubexponentialSAT.BitProgramCompile

namespace OAI.Algorithms

/-!
# Structured programs compiled to finite bit instruction tables

The syntax has no unbounded natural-number registers or semantic-function
instructions. All data operations are the concrete Boolean-register and stack
instructions of BitProgram. Loops inspect a Boolean register, and changing data
never changes the finite generated instruction table.
-/

namespace SubexponentialSAT.StructuredProgram

open SubexponentialSAT.BitProgram

/-- Data separate from the finite program counter. -/
structure State (r s : ℕ) where
  regs : Fin r → Bool
  «stacks» : Fin s → List Bool

namespace State

abbrev withPC {r s l : ℕ} (d : State r s) (pc : Option (Fin l)) : Cfg r s l :=
  ⟨pc, d.regs, d.stacks⟩

def ofCfg {r s l : ℕ} (c : Cfg r s l) : State r s := ⟨c.regs, c.stacks⟩

@[simp] theorem ofCfg_withPC {r s l : ℕ} (d : State r s) (pc : Option (Fin l)) :
    ofCfg (d.withPC pc) = d := rfl

end State

/-- Every atom is a single existing instruction with its continuation omitted. -/
inductive Atom (r s : ℕ) where
  | set (dst : Fin r) (value : Bool)
  | copy (dst src : Fin r)
  | bnot (dst src : Fin r)
  | band (dst left right : Fin r)
  | bor (dst left right : Fin r)
  | bxor (dst left right : Fin r)
  | push (stack : Fin s) (src : Fin r)
  | peek (stack : Fin s) (value present : Fin r)
  | pop (stack : Fin s) (value present : Fin r)
  deriving DecidableEq, Fintype

namespace Atom

def instr {r s l : ℕ} (a : Atom r s) (next : Fin l) : Instr r s l :=
  match a with
  | .set dst value => .set dst value next
  | .copy dst src => .copy dst src next
  | .bnot dst src => .bnot dst src next
  | .band dst left right => .band dst left right next
  | .bor dst left right => .bor dst left right next
  | .bxor dst left right => .bxor dst left right next
  | .push stack src => .push stack src next
  | .peek stack value present => .peek stack value present next
  | .pop stack value present => .pop stack value present next

/-- Atom evaluation uses the existing instruction evaluator itself. -/
def eval {r s : ℕ} (a : Atom r s) (d : State r s) : State r s :=
  State.ofCfg (execInstr (a.instr (0 : Fin 1)) (d.withPC none))

theorem exec_instr {r s l : ℕ} (a : Atom r s) (d : State r s)
    (pc : Option (Fin l)) (next : Fin l) :
    execInstr (a.instr next) (d.withPC pc) = (a.eval d).withPC (some next) := by
  cases a <;> rfl

end Atom

inductive Cmd (r s : ℕ) where
  | skip
  | atom (a : Atom r s)
  | seq (first second : Cmd r s)
  | ite (test : Fin r) (yes no : Cmd r s)
  | while (test : Fin r) (body : Cmd r s)

/-- Finite executions count exactly the atom and Boolean-test instructions. -/
inductive Eval {r s : ℕ} : Cmd r s → ℕ → State r s → State r s → Prop
  | skip (d) : Eval .skip 0 d d
  | atom (a) (d) : Eval (.atom a) 1 d (a.eval d)
  | seq {first second n m a b c} : Eval first n a b → Eval second m b c →
      Eval (.seq first second) (n + m) a c
  | ite_true {test yes no n a b} : a.regs test = true → Eval yes n a b →
      Eval (.ite test yes no) (n + 1) a b
  | ite_false {test yes no n a b} : a.regs test = false → Eval no n a b →
      Eval (.ite test yes no) (n + 1) a b
  | while_false {test body a} : a.regs test = false → Eval (.while test body) 1 a a
  | while_true {test body n m a b c} : a.regs test = true → Eval body n a b →
      Eval (.while test body) m b c → Eval (.while test body) (n + m + 1) a c

/-- One static site per atom or guard; sequencing introduces no instruction. -/
abbrev Site {r s : ℕ} : Cmd r s → Type
  | .skip => Empty
  | .atom _ => Unit
  | .seq first second => Site first ⊕ Site second
  | .ite _ yes no => Option (Site yes ⊕ Site no)
  | .while _ body => Option (Site body)

instance siteFintype {r s : ℕ} : (c : Cmd r s) → Fintype (Site c)
  | .skip => inferInstanceAs (Fintype Empty)
  | .atom _ => inferInstanceAs (Fintype Unit)
  | .seq first second => by
      letI := siteFintype first
      letI := siteFintype second
      exact inferInstanceAs (Fintype (Site first ⊕ Site second))
  | .ite _ yes no => by
      letI := siteFintype yes
      letI := siteFintype no
      exact inferInstanceAs (Fintype (Option (Site yes ⊕ Site no)))
  | .while _ body => by
      letI := siteFintype body
      exact inferInstanceAs (Fintype (Option (Site body)))

/-- Entry address when the command's continuation is a given address. -/
abbrev entry {r s l : ℕ} (c : Cmd r s) (embed : Site c → Fin l) (exit : Fin l) : Fin l :=
  match c with
  | .skip => exit
  | .atom _ => embed ()
  | .seq first second =>
      entry first (embed ∘ Sum.inl) (entry second (embed ∘ Sum.inr) exit)
  | .ite _ _ _ => embed none
  | .while _ _ => embed none

/-- Actual instruction at each static site. While bodies return to their guard. -/
abbrev code {r s l : ℕ} (c : Cmd r s) (embed : Site c → Fin l) (exit : Fin l) :
    Site c → Instr r s l :=
  match c with
  | .skip => fun q => nomatch q
  | .atom a => fun _ => a.instr exit
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

/-- The compiler correctness statement is about the actual BitProgram step.
The local table-agreement premise is discharged by the whole-program compiler. -/
theorem eval_trace {r s : ℕ} {c : Cmd r s} {n : ℕ} {a b : State r s}
    (h : Eval c n a b) :
    ∀ {l : ℕ} (p : Program r s l) (embed : Site c → Fin l) (exit : Fin l),
    (∀ q, p.code (embed q) = code c embed exit q) →
    Trace p n (a.withPC (some (entry c embed exit))) (b.withPC (some exit)) := by
  induction h with
  | skip d =>
      intro l p embed exit hcode
      exact .refl _
  | atom op d =>
      intro l p embed exit hcode
      refine .cons ?_ (.refl _)
      rw [← Atom.exec_instr op d (some (entry (.atom op) embed exit)) exit]
      exact step_code p _ (embed ()) (op.instr exit) rfl (hcode ())
  | @seq first second n m a b c hf hs ihf ihs =>
      intro l p embed exit hcode
      exact (ihf p (embed ∘ Sum.inl) (entry second (embed ∘ Sum.inr) exit)
        (fun q => hcode (.inl q))).trans
        (ihs p (embed ∘ Sum.inr) exit (fun q => hcode (.inr q)))
  | @ite_true test yes no n a b ht he ih =>
      intro l p embed exit hcode
      apply SubexponentialSAT.Computation.Trace.cons _
        (ih p (fun q => embed (some (.inl q))) exit (fun q => hcode (some (.inl q))))
      simp [step, State.withPC, entry, hcode none, code, execInstr, ht]
  | @ite_false test yes no n a b ht he ih =>
      intro l p embed exit hcode
      apply SubexponentialSAT.Computation.Trace.cons _
        (ih p (fun q => embed (some (.inr q))) exit (fun q => hcode (some (.inr q))))
      simp [step, State.withPC, entry, hcode none, code, execInstr, ht]
  | @while_false test body a ht =>
      intro l p embed exit hcode
      refine .cons ?_ (.refl _)
      simp [step, State.withPC, entry, hcode none, code, execInstr, ht]
  | @while_true test body n m a b c ht hb hw ihb ihw =>
      intro l p embed exit hcode
      apply SubexponentialSAT.Computation.Trace.cons _
        ((ihb p (embed ∘ some) (embed none) (fun q => hcode (some q))).trans
          (ihw p embed exit hcode))
      simp [step, State.withPC, entry, hcode none, code, execInstr, ht]

/-- Syntactic control size, independent of all runtime stack lengths. -/
abbrev size {r s : ℕ} : Cmd r s → ℕ
  | .skip => 0
  | .atom _ => 1
  | .seq first second => size first + size second
  | .ite _ yes no => size yes + size no + 1
  | .while _ body => size body + 1

/-- An explicit computable enumeration of control sites; no finite-choice
oracle is used to construct the generated instruction table. -/
abbrev siteEquiv {r s : ℕ} : (c : Cmd r s) → Site c ≃ Fin (size c)
  | .skip => finZeroEquiv.symm
  | .atom _ => finOneEquiv.symm
  | .seq first second =>
      ((siteEquiv first).sumCongr (siteEquiv second)).trans finSumFinEquiv
  | .ite _ yes no =>
      (((siteEquiv yes).sumCongr (siteEquiv no)).trans finSumFinEquiv).optionCongr.trans
        (finSuccEquiv _).symm
  | .while _ body => (siteEquiv body).optionCongr.trans (finSuccEquiv _).symm

/-- The extra address is the common final halt instruction. -/
abbrev labelEquiv {r s : ℕ} (c : Cmd r s) : Option (Site c) ≃ Fin (size c + 1) :=
  (siteEquiv c).optionCongr.trans (finSuccEquiv _).symm

abbrev siteAddress {r s : ℕ} (c : Cmd r s) (q : Site c) : Fin (size c + 1) :=
  labelEquiv c (some q)

abbrev exitAddress {r s : ℕ} (c : Cmd r s) : Fin (size c + 1) := labelEquiv c none

/-- A concrete, computably generated finite bit program. -/
def compiled {r s : ℕ} (c : Cmd r s) (inputStack outputStack : Fin s) :
    Program r s (size c + 1) where
  inputStack := inputStack
  outputStack := outputStack
  entry := entry c (siteAddress c) (exitAddress c)
  code label := match (labelEquiv c).symm label with
    | none => Instr.halt
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

/-- Whole-program correctness: n structured steps become n actual bit-program
steps to the exit address, with no unresolved compiler-certificate premise. -/
theorem compiled_trace {r s : ℕ} {c : Cmd r s} {n : ℕ} {a b : State r s}
    (h : Eval c n a b) (inputStack outputStack : Fin s) :
    Trace (compiled c inputStack outputStack) n
      (a.withPC (some (compiled c inputStack outputStack).entry))
      (b.withPC (some (exitAddress c))) :=
  eval_trace h _ _ _ (compiled_site c inputStack outputStack)

/-- Executing the generated final halt costs one additional instruction. -/
theorem compiled_halt_trace {r s : ℕ} {c : Cmd r s} {n : ℕ} {a b : State r s}
    (h : Eval c n a b) (inputStack outputStack : Fin s) :
    Trace (compiled c inputStack outputStack) (n + 1)
      (a.withPC (some (compiled c inputStack outputStack).entry)) (b.withPC none) := by
  apply (compiled_trace h inputStack outputStack).trans
  refine .cons ?_ (.refl _)
  rw [step]
  simp only [State.withPC, Option.map_some]
  rw [compiled_exit]
  rfl

/-- Canonical stack input/output data, including all cleared work registers. -/
abbrev ioState {r s : ℕ} (stack : Fin s) (word : List Bool) : State r s :=
  ⟨fun _ => false, fun i => if i = stack then word else []⟩

theorem compiled_io_trace {r s : ℕ} {c : Cmd r s} {n : ℕ}
    (inputStack outputStack : Fin s) {input output : List Bool}
    (h : Eval c n (ioState inputStack input) (ioState outputStack output)) :
    Trace (compiled c inputStack outputStack) (n + 1)
      (initial (compiled c inputStack outputStack) input)
      (terminal (compiled c inputStack outputStack) output) :=
  compiled_halt_trace h inputStack outputStack

/-- The generated structured program executes on the actual primitive tape
machine, at its proved program-fixed overhead times the source step count. -/
theorem primitive_execution {r s : ℕ} {c : Cmd r s} {n : ℕ} {a b : State r s}
    (h : Eval c n a b) (inputStack outputStack : Fin s) :
    let p := compiled c inputStack outputStack
    Computation.RunsIn (BitProgram.primitive p).step
      (BitProgram.primitiveOverhead p * (n + 1))
      (BitProgram.primitiveCfg p (a.withPC (some p.entry)))
      (BitProgram.primitiveCfg p (b.withPC none)) :=
  BitProgram.primitive_trace _ (compiled_halt_trace h inputStack outputStack)

/-- Canonical input and one-bit output connect directly to the strict primitive
machine output convention; all work storage must be cleared in the source proof. -/
theorem primitive_outputs {r s : ℕ} {c : Cmd r s} {n : ℕ}
    (inputStack outputStack : Fin s) {input : List Bool} {answer : Bool}
    (h : Eval c n (ioState inputStack input) (ioState outputStack [answer])) :
    let p := compiled c inputStack outputStack
    (BitProgram.primitive p).OutputsInTime input answer
      (BitProgram.primitiveOverhead p * (n + 1)) :=
  BitProgram.primitive_outputs _ ⟨n + 1, le_rfl, compiled_io_trace inputStack outputStack h⟩

end SubexponentialSAT.StructuredProgram

end OAI.Algorithms
