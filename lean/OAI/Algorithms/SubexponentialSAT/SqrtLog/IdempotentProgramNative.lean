import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramTrace
import OAI.Algorithms.SubexponentialSAT.CounterForPrograms

namespace OAI.Algorithms

/-! Fixed native Newton control, conditional only on explicitly supplied native
array-operation services. Each service hypothesis requires a real `Eval` of a
fixed finite command. The iteration count is stack data, not generated control.
This module does not claim that the array-service obligations are discharged. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpSymbolicCost
open SubexponentialSAT.StructuredCalls

variable {C A : Type*} [CommRing A] {r s : ℕ}

def nativeCode (service : ArithmeticInstruction → Cmd r s) :
    List ArithmeticInstruction → Cmd r s
  | [] => .base .skip
  | i::is => .seq (service i) (nativeCode service is)

def NativeInstructionSpec (ops : RingProgram C)
    (p : CounterForPrograms.Ports r s)
    (service : ArithmeticInstruction → Cmd r s)
    (enc : Registers C → State r s → Prop) (bound : ℕ) : Prop :=
  ∀ i regs d, enc regs d → d.stacks p.scratch = [] →
    ∃ n e, n ≤ bound ∧ Eval (service i) n d e ∧
      enc (instructionRun ops i regs).1 e ∧
      e.stacks p.counter = d.stacks p.counter ∧ e.stacks p.scratch = []

theorem nativeCode_correct (ops : RingProgram C)
    (p : CounterForPrograms.Ports r s)
    (service : ArithmeticInstruction → Cmd r s)
    (enc : Registers C → State r s → Prop) (bound : ℕ)
    (spec : NativeInstructionSpec ops p service enc bound)
    (code : List ArithmeticInstruction) (regs : Registers C) (d : State r s)
    (hd : enc regs d) (hs : d.stacks p.scratch = []) :
    ∃ n e, n ≤ code.length*bound ∧ Eval (nativeCode service code) n d e ∧
      enc (codeRun ops code regs).1 e ∧
      e.stacks p.counter = d.stacks p.counter ∧ e.stacks p.scratch = [] := by
  induction code generalizing regs d with
  | nil => exact ⟨0,d,by simp,.base (.skip d),hd,rfl,hs⟩
  | cons i is ih =>
      obtain ⟨n,e,hn,he,henc,hcounter,hscratch⟩ := spec i regs d hd hs
      obtain ⟨m,f,hm,hf,hencf,hcounterf,hscratchf⟩ :=
        ih (instructionRun ops i regs).1 e henc hscratch
      refine ⟨n+m,f,?_,he.seq hf,hencf,?_,hscratchf⟩
      · simp only [List.length_cons]
        nlinarith
      · exact hcounterf.trans hcounter

/-- This command's finite syntax is independent of `t` and of `clog 2 t`. -/
abbrev nativeNewtonLoop (p : CounterForPrograms.Ports r s)
    (service : ArithmeticInstruction → Cmd r s) : Cmd r s :=
  CounterForPrograms.forCmd p (nativeCode service newtonCode)

private theorem constant_budget (bound start fuel : ℕ) :
    CounterForPrograms.budgetSum (fun _ => bound) start fuel = fuel*bound := by
  induction fuel generalizing start with
  | zero => simp [CounterForPrograms.budgetSum]
  | succ fuel ih => simp [CounterForPrograms.budgetSum, ih]; ring

/-- Once the three array services and source-preserving register copies have
native proofs, all Newton iteration/control work is already a genuine native
trace with an explicit bit-counter overhead. -/
theorem nativeNewtonLoop_correct (ops : RepresentedRing C A)
    (p : CounterForPrograms.Ports r s)
    (service : ArithmeticInstruction → Cmd r s)
    (enc : Registers C → State r s → Prop) (bound : ℕ)
    (spec : NativeInstructionSpec ops.program p service enc bound)
    (frame : ∀ regs d e, CounterForPrograms.OutsideEq p d e → enc regs d → enc regs e)
    (regs : Registers C) (d : State r s) (hd : enc regs d)
    (hs : d.stacks p.scratch = []) :
    ∃ n e finalRegs,
      Eval (nativeNewtonLoop p service) n d e ∧ enc finalRegs e ∧
      ops.decode (finalRegs 0) = Idempotent.iterate (ops.decode (regs 0))
        (CounterPrograms.value (d.stacks p.counter)) ∧
      e.stacks p.scratch = [] ∧ CounterPrograms.value (e.stacks p.counter) = 0 ∧
      n ≤ 7*CounterPrograms.value (d.stacks p.counter)*bound +
        (CounterPrograms.value (d.stacks p.counter)+1)*
          (16*(d.stacks p.counter).length+16) := by
  let I : ℕ → State r s → Prop := fun i e =>
    ∃ rs, enc rs e ∧ ops.decode (rs 0) = Idempotent.iterate (ops.decode (regs 0)) i
  have stable : CounterForPrograms.FrameStable p I := by
    intro i a b hab ha
    obtain ⟨rs,hrs,hval⟩ := ha
    exact ⟨rs,frame rs a b hab hrs,hval⟩
  have body : CounterForPrograms.BodySpec p (nativeCode service newtonCode) I (fun _ => 7*bound) := by
    intro i a ha hscratch _
    obtain ⟨rs,hrs,hval⟩ := ha
    obtain ⟨n,b,hn,hb,henc,hcounter,hscratch⟩ :=
      nativeCode_correct ops.program p service enc bound spec newtonCode rs a hrs hscratch
    refine ⟨n,b,by simpa only [newtonCode_length] using hn,hb,hcounter,hscratch,?_⟩
    refine ⟨(codeRun ops.program newtonCode rs).1,henc,?_⟩
    rw [newtonCode_correct, hval]
    rfl
  obtain ⟨n,e,he,hi,hzero,hwidth,hscratch,hn⟩ :=
    CounterForPrograms.for_correct p (nativeCode service newtonCode) I (fun _ => 7*bound)
      stable body d hs ⟨regs,hd,rfl⟩
  obtain ⟨finalRegs,henc,hval⟩ := hi
  refine ⟨n,e,finalRegs,he,henc,hval,hscratch,hzero,?_⟩
  rw [constant_budget] at hn
  simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hn

/-- Compiling the fixed loop adds one actual halt instruction. -/
theorem nativeNewtonLoop_runs (ops : RepresentedRing C A)
    (p : CounterForPrograms.Ports r s)
    (service : ArithmeticInstruction → Cmd r s)
    (enc : Registers C → State r s → Prop) (bound : ℕ)
    (spec : NativeInstructionSpec ops.program p service enc bound)
    (frame : ∀ regs d e, CounterForPrograms.OutsideEq p d e → enc regs d → enc regs e)
    (regs : Registers C) (d : State r s) (hd : enc regs d)
    (hs : d.stacks p.scratch = []) (input output : Fin s) :
    ∃ e finalRegs,
      BitProgram.RunsIn (compiled (nativeNewtonLoop p service) input output)
        (7*CounterPrograms.value (d.stacks p.counter)*bound +
          (CounterPrograms.value (d.stacks p.counter)+1)*
            (16*(d.stacks p.counter).length+16)+1)
        (d.withPC (some (compiled (nativeNewtonLoop p service) input output).entry))
        (e.withPC none) ∧ enc finalRegs e ∧
      ops.decode (finalRegs 0) = Idempotent.iterate (ops.decode (regs 0))
        (CounterPrograms.value (d.stacks p.counter)) := by
  obtain ⟨n,e,rs,he,henc,hval,_,_,hn⟩ :=
    nativeNewtonLoop_correct ops p service enc bound spec frame regs d hd hs
  exact ⟨e,rs,⟨n+1,by omega,compiled_halt_trace he input output⟩,henc,hval⟩

end SubexponentialSAT.SqrtLog.IdempotentProgram

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.StructuredCalls

variable {C : Type*} {r s : ℕ}

/-- Strong form: the fixed native loop implements the exact functional array
state, not only its image under a semantic decoder. -/
theorem nativeNewtonLoop_exact (ops : RingProgram C)
    (p : CounterForPrograms.Ports r s)
    (service : ArithmeticInstruction → Cmd r s)
    (enc : Registers C → State r s → Prop) (bound : ℕ)
    (spec : NativeInstructionSpec ops p service enc bound)
    (frame : ∀ regs d e, CounterForPrograms.OutsideEq p d e → enc regs d → enc regs e)
    (regs : Registers C) (d : State r s) (hd : enc regs d)
    (hs : d.stacks p.scratch = []) :
    ∃ n e, Eval (nativeNewtonLoop p service) n d e ∧
      enc (codeRun ops (liftCode (CounterPrograms.value (d.stacks p.counter))) regs).1 e ∧
      n ≤ 7*CounterPrograms.value (d.stacks p.counter)*bound +
        (CounterPrograms.value (d.stacks p.counter)+1)*
          (16*(d.stacks p.counter).length+16) := by
  let I : ℕ → State r s → Prop := fun i e => enc (codeRun ops (liftCode i) regs).1 e
  have stable : CounterForPrograms.FrameStable p I := by
    intro i a b hab ha
    exact frame _ a b hab ha
  have body : CounterForPrograms.BodySpec p (nativeCode service newtonCode) I (fun _ => 7*bound) := by
    intro i a ha hscratch _
    obtain ⟨n,b,hn,hb,henc,hcounter,hscratch⟩ :=
      nativeCode_correct ops p service enc bound spec newtonCode
        (codeRun ops (liftCode i) regs).1 a ha hscratch
    refine ⟨n,b,by simpa only [newtonCode_length] using hn,hb,hcounter,hscratch,?_⟩
    change enc (codeRun ops (liftCode (i+1)) regs).1 b
    simpa only [liftCode, codeRun_append] using henc
  obtain ⟨n,e,he,hi,_,_,_,hn⟩ :=
    CounterForPrograms.for_correct p (nativeCode service newtonCode) I (fun _ => 7*bound)
      stable body d hs hd
  refine ⟨n,e,he,hi,?_⟩
  rw [constant_budget] at hn
  simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hn

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
