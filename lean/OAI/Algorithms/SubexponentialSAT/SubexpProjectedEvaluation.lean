import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpProjectedExecution
import OAI.Algorithms.SubexponentialSAT.SubexpEvaluationProgram
import OAI.Algorithms.SubexponentialSAT.SubexpExecution

namespace OAI.Algorithms

/-!
# Projected source evaluation on the shared Boolean machine

The fixed program calls a literal projection service, evaluates the original
serialized expression, and extracts the single dense result onto physical
stack 15. All twenty-eight caller stacks 100–127 are preserved.
-/

namespace SubexponentialSAT.SubexpProjectedEvaluation

open BitProgram
open SubexpPostfixControl (serializeCode operandDepth)
open SubexpPostfixGlobal (ports reindex_runsIn physicalCfg localService)
open SubexpEvaluationProgram (extractProgram extract_trace ecfg snapshot
  physical_result_ecfg resetProgram reset_trace registers registers_false
  inputCfg contextOf inputCfg_of_stacks)
open SubexpProjectedInterpreter (exprCost LoadImplements ImplementsOn Validity)

/-- Arithmetic tables act only on values reachable after projection. -/
abbrev ImplementsOnGlobal {R : Type*} {l : ℕ} (valid : R → Prop) (encode : R → List Bool)
    (operation : R → R → R) (isMul : Bool)
    (service : Program 16 128 l) (bound : R → R → ℕ)
    (context : Fin 124 → List Bool) : Prop :=
  ∀ (x y : R), valid x → valid y → ∀ (xs : List R) (code depth : List Bool),
    RunsIn service (bound x y)
      (physicalCfg (some service.entry) true true isMul code depth
        (Encoding.encodeList encode (y :: x :: xs)) context)
      (physicalCfg none false false false code depth
        (Encoding.encodeList encode (operation x y :: xs)) context)

theorem local_binary_implements {R : Type*} {l : ℕ} (valid : R → Prop)
    (encode : R → List Bool) (operation : R → R → R) (isMul : Bool)
    (service : Program 16 128 l) (bound : R → R → ℕ) (context : Fin 124 → List Bool)
    (h : ImplementsOnGlobal valid encode operation isMul service bound context) :
    ImplementsOn (r := 13) (s := 124) valid encode operation isMul (localService service) bound context := by
  intro x y hx hy xs code depth
  have hs := reindex_runsIn service ports.symm (h x y hx hy xs code depth)
  simpa only [physicalCfg, SubexpPostfixGlobal.reindexCfg_symm, localService,
    ProgramLinking.liftProgram] using hs

/-- The actual unary service acts on the newly pushed raw operand. -/
abbrev LoadImplementsGlobal {R : Type*} {l : ℕ} (encode : R → List Bool)
    (project : R → R) (service : Program 16 128 l) (bound : R → ℕ)
    (context : Fin 124 → List Bool) : Prop :=
  ∀ (x : R) (xs : List R) (code depth : List Bool) (op : Bool),
    RunsIn service (bound x)
      (physicalCfg (some service.entry) true false op code depth
        (Encoding.encodeList encode (x :: xs)) context)
      (physicalCfg none false false false code depth
        (Encoding.encodeList encode (project x :: xs)) context)

theorem local_load_implements {R : Type*} {l : ℕ} (encode : R → List Bool)
    (project : R → R) (service : Program 16 128 l) (bound : R → ℕ)
    (context : Fin 124 → List Bool)
    (h : LoadImplementsGlobal encode project service bound context) :
    LoadImplements (r := 13) (s := 124) encode project (localService service) bound context := by
  intro x xs code depth op
  have hs := reindex_runsIn service ports.symm (h x xs code depth op)
  simpa only [physicalCfg, SubexpPostfixGlobal.reindexCfg_symm, localService,
    ProgramLinking.liftProgram] using hs

abbrev globalProgram {a b c : ℕ} (add : Program 16 128 a) (mul : Program 16 128 b)
    (loader : Program 16 128 c) : Program 16 128 (37 + (2 + (a + (b + c)))) :=
  ProgramLinking.liftProgram
    (SubexpProjectedInterpreter.program (r := 13) (s := 124)
      (localService add) (localService mul) (localService loader)) id ports

@[simp] theorem globalProgram_input {a b c : ℕ} (add : Program 16 128 a)
    (mul : Program 16 128 b) (loader : Program 16 128 c) :
    (globalProgram add mul loader).inputStack = 26 := by
  simp [SubexpProjectedInterpreter.program, SubexpPostfixInterpreter.stack]

@[simp] theorem globalProgram_output {a b c : ℕ} (add : Program 16 128 a)
    (mul : Program 16 128 b) (loader : Program 16 128 c) :
    (globalProgram add mul loader).outputStack = 27 := by
  simp [SubexpProjectedInterpreter.program, SubexpPostfixInterpreter.stack]

/-- Execution of original raw-literal source, with a concrete projection call
at every literal. The three hypotheses concern the supplied finite tables. -/
theorem global_complete_runsIn {R : Type*} [Add R] [Mul R] {a b c : ℕ}
    (add : Program 16 128 a) (mul : Program 16 128 b) (loader : Program 16 128 c)
    (encode : R → List Bool) (project : R → R) (valid : R → Prop)
    (addBound mulBound : R → R → ℕ) (loadBound : R → ℕ) (context : Fin 124 → List Bool)
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
  have h := SubexpProjectedInterpreter.complete_runsIn (r := 13) (s := 124)
    (localService add) (localService mul) (localService loader) encode addBound mulBound
    context valid hal hml project loadBound hll hvalid e
  exact reindex_runsIn _ ports h

abbrev evaluationProgram {a b c : ℕ} (add : Program 16 128 a) (mul : Program 16 128 b)
    (loader : Program 16 128 c) : Program 16 128 ((37 + (2 + (a + (b + c)))) + 17) :=
  ProgramLinking.link (globalProgram add mul loader) extractProgram

/-- The result is unframed by the checked parser and transfer instructions. -/
theorem evaluation_runsIn {R : Type*} [Add R] [Mul R] {a b c : ℕ}
    (add : Program 16 128 a) (mul : Program 16 128 b) (loader : Program 16 128 c)
    (encode : R → List Bool) (project : R → R) (valid : R → Prop)
    (addBound mulBound : R → R → ℕ) (loadBound : R → ℕ) (context : Fin 124 → List Bool)
    (ha : ImplementsOnGlobal valid encode (· + ·) false add addBound context)
    (hm : ImplementsOnGlobal valid encode (· * ·) true mul mulBound context)
    (hl : LoadImplementsGlobal encode project loader loadBound context)
    (hvalid : Validity valid project) (e : Algorithm.Expr R) :
    RunsIn (evaluationProgram add mul loader)
      (exprCost encode addBound mulBound project loadBound e +
        2 * (context 11).length + 9 * (encode (e.map project).eval).length + 18)
      (physicalCfg (some (evaluationProgram add mul loader).entry) false false false
        (serializeCode encode e.compile) [] [] context)
      (ecfg none false false false (snapshot (encode (e.map project).eval) context)
        [] [] [] (encode (e.map project).eval)) := by
  have he := global_complete_runsIn add mul loader encode project valid addBound mulBound loadBound
    context ha hm hl hvalid e
  have hx : RunsIn extractProgram
      (2 * (context 11).length + 9 * (encode (e.map project).eval).length + 13)
      (ProgramLinking.enter extractProgram
        (physicalCfg (l := 37 + (2 + (a + (b + c)))) none false false false []
          (operandDepth [(e.map project).eval])
          (Encoding.encodeList encode [(e.map project).eval]) context))
      (ecfg none false false false (snapshot (encode (e.map project).eval) context)
        [] [] [] (encode (e.map project).eval)) := by
    refine ⟨_, le_rfl, ?_⟩
    have h := extract_trace (encode (e.map project).eval) (context 11) false false false
      (snapshot (encode (e.map project).eval) context)
    have hp := physical_result_ecfg (l := 17) (some 0) (encode (e.map project).eval) false context
    change Trace extractProgram _
      (physicalCfg (some 0) false false false [] [true]
        (true :: (Encoding.frame (encode (e.map project).eval) ++ [false])) context) _
    rw [hp]
    exact h
  have h := ProgramLinking.link_runsIn (globalProgram add mul loader) extractProgram he rfl hx
  change RunsIn (evaluationProgram add mul loader) _
    (physicalCfg (some (evaluationProgram add mul loader).entry) false false false
      (serializeCode encode e.compile) [] [] context)
    (ecfg none false false false (snapshot (encode (e.map project).eval) context)
      [] [] [] (encode (e.map project).eval)) at h
  convert h using 1
  omega

/-- A fixed register-reset prefix accepts arbitrary live caller flags. -/
abbrev readyEvaluationProgram {a b c : ℕ} (add : Program 16 128 a) (mul : Program 16 128 b)
    (loader : Program 16 128 c) : Program 16 128 (17 + ((37 + (2 + (a + (b + c)))) + 17)) :=
  ProgramLinking.link resetProgram (evaluationProgram add mul loader)

theorem ready_evaluation_runsIn {R : Type*} [Add R] [Mul R] {a b c : ℕ}
    (add : Program 16 128 a) (mul : Program 16 128 b) (loader : Program 16 128 c)
    (encode : R → List Bool) (project : R → R) (valid : R → Prop)
    (addBound mulBound : R → R → ℕ) (loadBound : R → ℕ) (context : Fin 124 → List Bool)
    (ha : ImplementsOnGlobal valid encode (· + ·) false add addBound context)
    (hm : ImplementsOnGlobal valid encode (· * ·) true mul mulBound context)
    (hl : LoadImplementsGlobal encode project loader loadBound context)
    (hvalid : Validity valid project) (e : Algorithm.Expr R) (regs : Fin 16 → Bool) :
    RunsIn (readyEvaluationProgram add mul loader)
      (exprCost encode addBound mulBound project loadBound e +
        2 * (context 11).length + 9 * (encode (e.map project).eval).length + 35)
      (inputCfg (some (readyEvaluationProgram add mul loader).entry) regs
        (serializeCode encode e.compile) context)
      (ecfg none false false false (snapshot (encode (e.map project).eval) context)
        [] [] [] (encode (e.map project).eval)) := by
  let code := serializeCode encode e.compile
  have hr : Trace resetProgram 17
      (inputCfg (some resetProgram.entry) regs code context)
      (physicalCfg none false false false code [] [] context) := by
    change Trace resetProgram 17
      ⟨some resetProgram.entry, regs, _⟩ ⟨none, registers false false false, _⟩
    rw [registers_false]
    exact reset_trace regs _
  have hrr : RunsIn resetProgram 17
      (inputCfg (some resetProgram.entry) regs code context)
      (physicalCfg none false false false code [] [] context) := ⟨17, le_rfl, hr⟩
  have he := evaluation_runsIn add mul loader encode project valid addBound mulBound loadBound context ha hm hl hvalid e
  have h := ProgramLinking.link_runsIn resetProgram (evaluationProgram add mul loader) hrr rfl he
  change RunsIn (readyEvaluationProgram add mul loader) _
    (inputCfg (some (readyEvaluationProgram add mul loader).entry) regs code context)
    (ecfg none false false false (snapshot (encode (e.map project).eval) context)
      [] [] [] (encode (e.map project).eval)) at h
  convert h using 1
  omega

/-- Entry from the actual caller stack function, without a configuration oracle. -/
theorem ready_evaluation_state_runsIn {R : Type*} [Add R] [Mul R] {a b c : ℕ}
    (add : Program 16 128 a) (mul : Program 16 128 b) (loader : Program 16 128 c)
    (encode : R → List Bool) (project : R → R) (valid : R → Prop)
    (addBound mulBound : R → R → ℕ) (loadBound : R → ℕ) (e : Algorithm.Expr R)
    (regs : Fin 16 → Bool) (stk : Fin 128 → List Bool)
    (h26 : stk 26 = serializeCode encode e.compile)
    (h27 : stk 27 = []) (h28 : stk 28 = []) (h29 : stk 29 = [])
    (ha : ImplementsOnGlobal valid encode (· + ·) false add addBound (contextOf stk))
    (hm : ImplementsOnGlobal valid encode (· * ·) true mul mulBound (contextOf stk))
    (hl : LoadImplementsGlobal encode project loader loadBound (contextOf stk))
    (hvalid : Validity valid project) :
    RunsIn (readyEvaluationProgram add mul loader)
      (exprCost encode addBound mulBound project loadBound e +
        2 * ((contextOf stk) 11).length + 9 * (encode (e.map project).eval).length + 35)
      ⟨some (readyEvaluationProgram add mul loader).entry, regs, stk⟩
      (ecfg none false false false (snapshot (encode (e.map project).eval) (contextOf stk))
        [] [] [] (encode (e.map project).eval)) := by
  have h := ready_evaluation_runsIn add mul loader encode project valid addBound mulBound loadBound
    (contextOf stk) ha hm hl hvalid e regs
  rw [inputCfg_of_stacks _ _ _ _ h26 h27 h28 h29] at h
  exact h

/-! ## Operations on represented values

No ring laws or quotient structure are assumed for machine words. These
bridges use the very same load/add/multiply values as the represented evaluator.
-/

section Operations

variable {R : Type*} (ops : SubexpExecution.Operations R R)

@[instance_reducible] def operationAdd : Add R := ⟨fun x y => (ops.add x y).1⟩
@[instance_reducible] def operationMul : Mul R := ⟨fun x y => (ops.mul x y).1⟩

theorem operation_value (e : Algorithm.Expr R) :
    @Algorithm.Expr.eval R (operationAdd ops) (operationMul ops)
      (e.map (fun x => (ops.load x).1)) = (SubexpExecution.evalWithCost ops e).1 := by
  let := operationAdd ops
  let := operationMul ops
  exact (SubexpExecution.evalWithCost_decode ops id (fun x => (ops.load x).1)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) e).symm

/-- A source-recursive bound charging the supplied finite service traces.
This differs from an abstract scalar-operation counter. -/
def operationCost (encode : R → List Bool) (addBound mulBound : R → R → ℕ)
    (loadBound : R → ℕ) : Algorithm.Expr R → ℕ
  | .lit x => 11 * (encode x).length + 17 + loadBound x
  | .add e f => operationCost encode addBound mulBound loadBound e +
      operationCost encode addBound mulBound loadBound f +
      (14 + addBound (SubexpExecution.evalWithCost ops e).1 (SubexpExecution.evalWithCost ops f).1)
  | .mul e f => operationCost encode addBound mulBound loadBound e +
      operationCost encode addBound mulBound loadBound f +
      (14 + mulBound (SubexpExecution.evalWithCost ops e).1 (SubexpExecution.evalWithCost ops f).1)

theorem operation_cost (encode : R → List Bool) (addBound mulBound : R → R → ℕ)
    (loadBound : R → ℕ) (e : Algorithm.Expr R) :
    @exprCost R (operationAdd ops) (operationMul ops) encode addBound mulBound
      (fun x => (ops.load x).1) loadBound e =
      operationCost ops encode addBound mulBound loadBound e := by
  induction e with
  | lit x => rfl
  | add e f he hf => simp only [exprCost, operationCost, he, hf, operation_value]
  | mul e f he hf => simp only [exprCost, operationCost, he, hf, operation_value]

/-- The concrete finite program returns the represented evaluator's exact
value. Each assumption is a local trace of an installed instruction table. -/
theorem ready_operations_state_runsIn {a b c : ℕ}
    (add : Program 16 128 a) (mul : Program 16 128 b) (loader : Program 16 128 c)
    (encode : R → List Bool) (valid : R → Prop)
    (addBound mulBound : R → R → ℕ) (loadBound : R → ℕ)
    (e : Algorithm.Expr R) (regs : Fin 16 → Bool) (stk : Fin 128 → List Bool)
    (h26 : stk 26 = serializeCode encode e.compile)
    (h27 : stk 27 = []) (h28 : stk 28 = []) (h29 : stk 29 = [])
    (ha : ImplementsOnGlobal valid encode (fun x y => (ops.add x y).1) false add addBound (contextOf stk))
    (hm : ImplementsOnGlobal valid encode (fun x y => (ops.mul x y).1) true mul mulBound (contextOf stk))
    (hl : LoadImplementsGlobal encode (fun x => (ops.load x).1) loader loadBound (contextOf stk))
    (hvalid : @Validity R (operationAdd ops) (operationMul ops) valid (fun x => (ops.load x).1)) :
    RunsIn (readyEvaluationProgram add mul loader)
      (operationCost ops encode addBound mulBound loadBound e +
        2 * ((contextOf stk) 11).length +
        9 * (encode (SubexpExecution.evalWithCost ops e).1).length + 35)
      ⟨some (readyEvaluationProgram add mul loader).entry, regs, stk⟩
      (ecfg none false false false (snapshot (encode (SubexpExecution.evalWithCost ops e).1) (contextOf stk))
        [] [] [] (encode (SubexpExecution.evalWithCost ops e).1)) := by
  let := operationAdd ops
  let := operationMul ops
  have h := ready_evaluation_state_runsIn add mul loader encode (fun x => (ops.load x).1) valid
    addBound mulBound loadBound e regs stk h26 h27 h28 h29 ha hm hl hvalid
  simpa only [operation_cost, operation_value] using h

end Operations


/-- A projected coefficient list has only retained keys. Scalar width is
already enforced by the coefficient representation type. -/
def RetainedList {D : ℕ} {C : Type*} (P : SymbolicCost.CoeffList D C) : Prop :=
  ∀ term ∈ P, SymbolicCost.Retained D term.1

theorem programProject_keys {D : ℕ} {C : Type*}
    (ops : SubexpSymbolicCost.RingProgram C) (slots : List (SymbolicCost.RawIndex D))
    (P : SymbolicCost.CoeffList D C) :
    (SubexpSymbolicCost.programProject ops slots P).1.map Prod.fst = slots := by
  induction slots with
  | nil => rfl
  | cons a slots ih => simpa [SubexpSymbolicCost.programProject] using congrArg (List.cons a) ih

theorem programProject_retained {D : ℕ} {C : Type*}
    (ops : SubexpSymbolicCost.RingProgram C) (slots : List (SymbolicCost.RawIndex D))
    (hslots : ∀ a ∈ slots, SymbolicCost.Retained D a) (P : SymbolicCost.CoeffList D C) :
    RetainedList (SubexpSymbolicCost.programProject ops slots P).1 := by
  intro term hterm
  have hkey : term.1 ∈ (SubexpSymbolicCost.programProject ops slots P).1.map Prod.fst :=
    List.mem_map.mpr ⟨term, hterm, rfl⟩
  rw [programProject_keys] at hkey
  exact hslots _ hkey

/-- Direct specialization to the actual raw-coefficient-list evaluator.
Projection establishes the retained-key invariant; both binary operations
preserve it because they project their output to the same slot list. -/
theorem ready_programEval_state_runsIn {D : ℕ} {C : Type*} {a b c : ℕ}
    (ops : SubexpSymbolicCost.RingProgram C) (slots : List (SymbolicCost.RawIndex D))
    (hslots : ∀ k ∈ slots, SymbolicCost.Retained D k)
    (add : Program 16 128 a) (mul : Program 16 128 b) (loader : Program 16 128 c)
    (encode : SymbolicCost.CoeffList D C → List Bool)
    (addBound mulBound : SymbolicCost.CoeffList D C → SymbolicCost.CoeffList D C → ℕ)
    (loadBound : SymbolicCost.CoeffList D C → ℕ) (e : Algorithm.Expr (SymbolicCost.CoeffList D C))
    (regs : Fin 16 → Bool) (stk : Fin 128 → List Bool)
    (h26 : stk 26 = serializeCode encode e.compile)
    (h27 : stk 27 = []) (h28 : stk 28 = []) (h29 : stk 29 = [])
    (ha : ImplementsOnGlobal RetainedList encode
      (fun x y => (SubexpSymbolicCost.programAdd ops slots x y).1)
      false add addBound (contextOf stk))
    (hm : ImplementsOnGlobal RetainedList encode
      (fun x y => (SubexpSymbolicCost.programMul ops slots x y).1)
      true mul mulBound (contextOf stk))
    (hl : LoadImplementsGlobal encode (fun x => (SubexpSymbolicCost.programProject ops slots x).1)
      loader loadBound (contextOf stk)) :
    RunsIn (readyEvaluationProgram add mul loader)
      (operationCost (SubexpExecution.programOperations ops slots) encode addBound mulBound loadBound e +
        2 * ((contextOf stk) 11).length +
        9 * (encode (SubexpExecution.programEval ops slots e).1).length + 35)
      ⟨some (readyEvaluationProgram add mul loader).entry, regs, stk⟩
      (ecfg none false false false
        (snapshot (encode (SubexpExecution.programEval ops slots e).1) (contextOf stk))
        [] [] [] (encode (SubexpExecution.programEval ops slots e).1)) := by
  let : Add (SymbolicCost.CoeffList D C) :=
    ⟨fun x y => (SubexpSymbolicCost.programAdd ops slots x y).1⟩
  let : Mul (SymbolicCost.CoeffList D C) :=
    ⟨fun x y => (SubexpSymbolicCost.programMul ops slots x y).1⟩
  have hv : Validity RetainedList (fun x => (SubexpSymbolicCost.programProject ops slots x).1) := by
    refine ⟨programProject_retained ops slots hslots, ?_, ?_⟩
    · intro x y _ _
      exact programProject_retained ops slots hslots _
    · intro x y _ _
      exact programProject_retained ops slots hslots _
  exact ready_operations_state_runsIn (SubexpExecution.programOperations ops slots)
    add mul loader encode RetainedList addBound mulBound loadBound e regs stk h26 h27 h28 h29 ha hm hl hv

end SubexponentialSAT.SubexpProjectedEvaluation

end OAI.Algorithms
