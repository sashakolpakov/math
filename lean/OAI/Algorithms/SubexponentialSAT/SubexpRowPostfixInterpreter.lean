import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpProjectedExecution
import OAI.Algorithms.SubexponentialSAT.SubexpPostfixGlobal

namespace OAI.Algorithms

/-! The source-row postfix interpreter on the fixed 256-stack workspace.
Only port names change; the checked dispatcher and all service transitions
are retained. Parameters such as R and the field remain encoded data. -/

namespace SubexponentialSAT.SubexpRowPostfixInterpreter

open BitProgram
open SubexpPostfixControl (serializeCode operandDepth)
open SubexpPostfixInterpreter (cfg)
open SubexpPostfixGlobal (reindexCfg reindex_runsIn)
open SubexpProjectedInterpreter (exprCost LoadImplements ImplementsOn Validity)

def ports : Equiv.Perm (Fin 256) :=
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

def physicalCfg {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin 252 → List Bool) : Cfg 16 256 l :=
  reindexCfg ports (cfg (r := 13) (s := 252) pc v p op code depth operands context)

@[simp] theorem physicalCfg_code {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin 252 → List Bool) :
    (physicalCfg pc v p op code depth operands context).stacks 26 = code := by
  simp [physicalCfg, reindexCfg, cfg]
  rfl

@[simp] theorem physicalCfg_depth {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin 252 → List Bool) :
    (physicalCfg pc v p op code depth operands context).stacks 28 = depth := by
  simp [physicalCfg, reindexCfg, cfg]
  rfl

@[simp] theorem physicalCfg_operands {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin 252 → List Bool) :
    (physicalCfg pc v p op code depth operands context).stacks 27 = operands := by
  simp [physicalCfg, reindexCfg, cfg]
  rfl

@[simp] theorem physicalCfg_scratch {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin 252 → List Bool) :
    (physicalCfg pc v p op code depth operands context).stacks 29 = [] := by
  simp [physicalCfg, reindexCfg, cfg]
  rfl

@[simp] theorem physicalCfg_context {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin 252 → List Bool) (i : Fin 252) :
    (physicalCfg pc v p op code depth operands context).stacks
      (ports (Fin.natAdd 4 i)) = context i := by
  simp [physicalCfg, reindexCfg, cfg]

/-- The input arithmetic table already uses shared physical ports. -/
abbrev localService {l : ℕ} (p : Program 16 256 l) : Program 16 256 l :=
  ProgramLinking.liftProgram p id ports.symm

/-- Arithmetic tables act only on values reachable after projection. -/
abbrev ImplementsOnGlobal {R : Type*} {l : ℕ} (valid : R → Prop) (encode : R → List Bool)
    (operation : R → R → R) (isMul : Bool)
    (service : Program 16 256 l) (bound : R → R → ℕ)
    (context : Fin 252 → List Bool) : Prop :=
  ∀ (x y : R), valid x → valid y → ∀ (xs : List R) (code depth : List Bool),
    RunsIn service (bound x y)
      (physicalCfg (some service.entry) true true isMul code depth
        (Encoding.encodeList encode (y :: x :: xs)) context)
      (physicalCfg none false false false code depth
        (Encoding.encodeList encode (operation x y :: xs)) context)

theorem local_binary_implements {R : Type*} {l : ℕ} (valid : R → Prop)
    (encode : R → List Bool) (operation : R → R → R) (isMul : Bool)
    (service : Program 16 256 l) (bound : R → R → ℕ) (context : Fin 252 → List Bool)
    (h : ImplementsOnGlobal valid encode operation isMul service bound context) :
    ImplementsOn (r := 13) (s := 252) valid encode operation isMul (localService service) bound context := by
  intro x y hx hy xs code depth
  have hs := reindex_runsIn service ports.symm (h x y hx hy xs code depth)
  simpa only [physicalCfg, SubexpPostfixGlobal.reindexCfg_symm, localService,
    ProgramLinking.liftProgram] using hs

/-- The actual unary service acts on the newly pushed raw operand. -/
abbrev LoadImplementsGlobal {R : Type*} {l : ℕ} (encode : R → List Bool)
    (project : R → R) (service : Program 16 256 l) (bound : R → ℕ)
    (context : Fin 252 → List Bool) : Prop :=
  ∀ (x : R) (xs : List R) (code depth : List Bool) (op : Bool),
    RunsIn service (bound x)
      (physicalCfg (some service.entry) true false op code depth
        (Encoding.encodeList encode (x :: xs)) context)
      (physicalCfg none false false false code depth
        (Encoding.encodeList encode (project x :: xs)) context)

theorem local_load_implements {R : Type*} {l : ℕ} (encode : R → List Bool)
    (project : R → R) (service : Program 16 256 l) (bound : R → ℕ)
    (context : Fin 252 → List Bool)
    (h : LoadImplementsGlobal encode project service bound context) :
    LoadImplements (r := 13) (s := 252) encode project (localService service) bound context := by
  intro x xs code depth op
  have hs := reindex_runsIn service ports.symm (h x xs code depth op)
  simpa only [physicalCfg, SubexpPostfixGlobal.reindexCfg_symm, localService,
    ProgramLinking.liftProgram] using hs

abbrev globalProgram {a b c : ℕ} (add : Program 16 256 a) (mul : Program 16 256 b)
    (loader : Program 16 256 c) : Program 16 256 (37 + (2 + (a + (b + c)))) :=
  ProgramLinking.liftProgram
    (SubexpProjectedInterpreter.program (r := 13) (s := 252)
      (localService add) (localService mul) (localService loader)) id ports

@[simp] theorem globalProgram_input {a b c : ℕ} (add : Program 16 256 a)
    (mul : Program 16 256 b) (loader : Program 16 256 c) :
    (globalProgram add mul loader).inputStack = 26 := by
  simp [ SubexpProjectedInterpreter.program,
    SubexpPostfixInterpreter.stack]

@[simp] theorem globalProgram_output {a b c : ℕ} (add : Program 16 256 a)
    (mul : Program 16 256 b) (loader : Program 16 256 c) :
    (globalProgram add mul loader).outputStack = 27 := by
  simp [ SubexpProjectedInterpreter.program,
    SubexpPostfixInterpreter.stack]

/-- Execution of original raw-literal source, with a concrete projection call
at every literal. The three hypotheses concern the supplied finite tables. -/
theorem global_complete_runsIn {R : Type*} [Add R] [Mul R] {a b c : ℕ}
    (add : Program 16 256 a) (mul : Program 16 256 b) (loader : Program 16 256 c)
    (encode : R → List Bool) (project : R → R) (valid : R → Prop)
    (addBound mulBound : R → R → ℕ) (loadBound : R → ℕ) (context : Fin 252 → List Bool)
    (ha : ImplementsOnGlobal valid encode (· + ·) false add addBound context)
    (hm : ImplementsOnGlobal valid encode (· * ·) true mul mulBound context)
    (hl : LoadImplementsGlobal encode project loader loadBound context)
    (hvalid : Validity valid project) (e : Algorithm.Expr R) :
    RunsIn (globalProgram add mul loader) (exprCost encode addBound mulBound project loadBound e + 5)
      (physicalCfg (some (globalProgram add mul loader).entry) false false false
        (serializeCode encode e.compile) [] [] context)
      (physicalCfg none false false false [] (operandDepth [(e.map project).eval])
        (Encoding.encodeList encode [(e.map project).eval]) context) := by
  have hal := local_binary_implements valid encode (· + ·) false add addBound context ha
  have hml := local_binary_implements valid encode (· * ·) true mul mulBound context hm
  have hll := local_load_implements encode project loader loadBound context hl
  have h := SubexpProjectedInterpreter.complete_runsIn (r := 13) (s := 252)
    (localService add) (localService mul) (localService loader) encode addBound mulBound
    context valid hal hml project loadBound hll hvalid e
  exact reindex_runsIn _ ports h


end SubexponentialSAT.SubexpRowPostfixInterpreter

end OAI.Algorithms
