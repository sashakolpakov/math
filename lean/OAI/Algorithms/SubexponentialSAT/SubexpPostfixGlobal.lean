import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPostfixInterpreter

namespace OAI.Algorithms

/-!
# Shared-machine port adapter for the concrete postfix interpreter

The shared machine uses code/depth/operand/scratch stacks 26/28/27/29.
A fixed permutation installs the proved interpreter there while accepting
arithmetic service tables already written for the shared 16-register,
128-stack machine. Port renaming adds no machine transitions.
-/

namespace SubexponentialSAT.SubexpPostfixGlobal

open BitProgram
open SubexpPostfixInterpreter

/-- Four disjoint swaps; all other physical stack indices are unchanged. -/
def ports : Equiv.Perm (Fin 128) :=
  ((Equiv.swap 0 26).trans (Equiv.swap 1 28)).trans
    ((Equiv.swap 2 27).trans (Equiv.swap 3 29))

@[simp] theorem ports_zero : ports 0 = 26 := by decide
@[simp] theorem ports_one : ports 1 = 28 := by decide
@[simp] theorem ports_two : ports 2 = 27 := by decide
@[simp] theorem ports_three : ports 3 = 29 := by decide
@[simp] theorem ports_symm_26 : ports.symm 26 = 0 := by decide
@[simp] theorem ports_symm_28 : ports.symm 28 = 1 := by decide
@[simp] theorem ports_symm_27 : ports.symm 27 = 2 := by decide
@[simp] theorem ports_symm_29 : ports.symm 29 = 3 := by decide

/-- Reindex physical stacks without changing their contents or control state. -/
def reindexCfg {r s l : ℕ} (e : Equiv.Perm (Fin s)) (c : Cfg r s l) : Cfg r s l where
  pc := c.pc
  regs := c.regs
  «stacks» := fun i => c.stacks (e.symm i)

@[simp] theorem reindexCfg_symm {r s l : ℕ} (e : Equiv.Perm (Fin s)) (c : Cfg r s l) :
    reindexCfg e.symm (reindexCfg e c) = c := by
  cases c
  simp [reindexCfg]

theorem embedCfg_reindex {r s l : ℕ} (e : Equiv.Perm (Fin s))
    (frame c : Cfg r s l) :
    ProgramLinking.embedCfg id e id none frame c = reindexCfg e c := by
  cases c with
  | mk pc regs stk =>
    have hs : Function.extend e stk frame.stacks = fun i => stk (e.symm i) := by
      funext i
      rw [← e.apply_symm_apply i, e.injective.extend_apply]
      simp
    cases pc <;> simp [ProgramLinking.embedCfg, ProgramLinking.relocatePc, reindexCfg, hs]

theorem reindex_runsIn {r s l n : ℕ} (p : Program r s l) (e : Equiv.Perm (Fin s))
    {c d : Cfg r s l} (h : RunsIn p n c d) :
    RunsIn (ProgramLinking.liftProgram p id e) n (reindexCfg e c) (reindexCfg e d) := by
  have hl := ProgramLinking.liftProgram_runsIn p id e (reindexCfg e c)
    Function.injective_id e.injective h
  simpa only [embedCfg_reindex] using hl

def physicalCfg {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin 124 → List Bool) : Cfg 16 128 l :=
  reindexCfg ports (cfg (r := 13) (s := 124) pc v p op code depth operands context)

@[simp] theorem physicalCfg_code {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin 124 → List Bool) :
    (physicalCfg pc v p op code depth operands context).stacks 26 = code := by
  simp [physicalCfg, reindexCfg, cfg]
  rfl

@[simp] theorem physicalCfg_depth {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin 124 → List Bool) :
    (physicalCfg pc v p op code depth operands context).stacks 28 = depth := by
  simp [physicalCfg, reindexCfg, cfg]
  rfl

@[simp] theorem physicalCfg_operands {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin 124 → List Bool) :
    (physicalCfg pc v p op code depth operands context).stacks 27 = operands := by
  simp [physicalCfg, reindexCfg, cfg]
  rfl

@[simp] theorem physicalCfg_scratch {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin 124 → List Bool) :
    (physicalCfg pc v p op code depth operands context).stacks 29 = [] := by
  simp [physicalCfg, reindexCfg, cfg]
  rfl

@[simp] theorem physicalCfg_context {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin 124 → List Bool) (i : Fin 124) :
    (physicalCfg pc v p op code depth operands context).stacks
      (ports (Fin.natAdd 4 i)) = context i := by
  simp [physicalCfg, reindexCfg, cfg]

/-- The input arithmetic table already uses shared physical ports. -/
abbrev localService {l : ℕ} (p : Program 16 128 l) : Program 16 128 l :=
  ProgramLinking.liftProgram p id ports.symm

abbrev globalProgram {a b : ℕ} (add : Program 16 128 a) (mul : Program 16 128 b) :
    Program 16 128 (37 + (2 + (a + b))) :=
  ProgramLinking.liftProgram
    (program (r := 13) (s := 124) (localService add) (localService mul)) id ports

@[simp] theorem globalProgram_input {a b : ℕ} (add : Program 16 128 a) (mul : Program 16 128 b) :
    (globalProgram add mul).inputStack = 26 := by
  simp [ stack]

@[simp] theorem globalProgram_output {a b : ℕ} (add : Program 16 128 a) (mul : Program 16 128 b) :
    (globalProgram add mul).outputStack = 27 := by
  simp [ stack]

abbrev ImplementsGlobal {R : Type*} {l : ℕ} (encode : R → List Bool)
    (operation : R → R → R) (isMul : Bool)
    (service : Program 16 128 l) (bound : R → R → ℕ)
    (context : Fin 124 → List Bool) : Prop :=
  ∀ (x y : R) (xs : List R) (code depth : List Bool),
    RunsIn service (bound x y)
      (physicalCfg (some service.entry) true true isMul code depth
        (Encoding.encodeList encode (y :: x :: xs)) context)
      (physicalCfg none false false false code depth
        (Encoding.encodeList encode (operation x y :: xs)) context)

theorem localService_implements {R : Type*} {l : ℕ} (encode : R → List Bool)
    (operation : R → R → R) (isMul : Bool)
    (service : Program 16 128 l) (bound : R → R → ℕ) (context : Fin 124 → List Bool)
    (h : ImplementsGlobal encode operation isMul service bound context) :
    Implements (r := 13) (s := 124) encode operation isMul (localService service) bound context := by
  intro x y xs code depth
  have hs := reindex_runsIn service ports.symm (h x y xs code depth)
  simpa only [physicalCfg, reindexCfg_symm, localService, ProgramLinking.liftProgram] using hs

/-- Shared-port execution of the exact serialized compiled expression. The
only arithmetic assumptions are local traces of the supplied finite tables. -/
theorem global_complete_runsIn {R : Type*} [Add R] [Mul R] {a b : ℕ}
    (add : Program 16 128 a) (mul : Program 16 128 b) (encode : R → List Bool)
    (addBound mulBound : R → R → ℕ) (context : Fin 124 → List Bool)
    (ha : ImplementsGlobal encode (· + ·) false add addBound context)
    (hm : ImplementsGlobal encode (· * ·) true mul mulBound context) (e : Algorithm.Expr R) :
    ∃ op, RunsIn (globalProgram add mul) (e.cost (costs encode addBound mulBound) + 5)
      (physicalCfg (some (globalProgram add mul).entry) false false false
        (SubexpPostfixControl.serializeCode encode e.compile) [] [] context)
      (physicalCfg none false false op [] (SubexpPostfixControl.operandDepth [e.eval])
        (Encoding.encodeList encode [e.eval]) context) := by
  have hal := localService_implements encode (· + ·) false add addBound context ha
  have hml := localService_implements encode (· * ·) true mul mulBound context hm
  obtain ⟨op, h⟩ := complete_runsIn (r := 13) (s := 124) (localService add) (localService mul)
    encode addBound mulBound context hal hml e
  refine ⟨op, ?_⟩
  exact reindex_runsIn _ ports h

end SubexponentialSAT.SubexpPostfixGlobal

end OAI.Algorithms
