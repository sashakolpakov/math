import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpProjectedInterpreter

namespace OAI.Algorithms

/-!
# Projected postfix execution

The compiled source contains the original raw literals. Each complete push
calls the finite projection table; the resulting value is therefore
`(e.map project).eval`. The induction tracks the entire remaining source and
operand list, and charges actual service trace bounds at every node.
-/

namespace SubexponentialSAT.SubexpProjectedInterpreter

open BitProgram
open SubexpPostfixControl (serializeCode serializeInstr operandDepth)
open SubexpPostfixInterpreter (cfg Implements)

variable {r s a b c : ℕ}

/-- A unary load is implemented by actual instructions on the top framed
operand. The rest of the operand stack and arithmetic context are preserved. -/
abbrev LoadImplements {R : Type*} {l : ℕ} (encode : R → List Bool)
    (project : R → R) (service : Program (3 + r) (4 + s) l) (bound : R → ℕ)
    (context : Fin s → List Bool) : Prop :=
  ∀ (x : R) (xs : List R) (code depth : List Bool) (op : Bool),
    RunsIn service (bound x)
      (cfg (some service.entry) true false op code depth
        (Encoding.encodeList encode (x :: xs)) context)
      (cfg none false false false code depth
        (Encoding.encodeList encode (project x :: xs)) context)

/-- Binary services are required only on values produced by projection and
previous arithmetic. Raw literal keys need not satisfy this predicate. -/
abbrev ImplementsOn {R : Type*} {l : ℕ} (valid : R → Prop) (encode : R → List Bool)
    (operation : R → R → R) (isMul : Bool)
    (service : Program (3 + r) (4 + s) l) (bound : R → R → ℕ)
    (context : Fin s → List Bool) : Prop :=
  ∀ (x y : R), valid x → valid y → ∀ (xs : List R) (code depth : List Bool),
    RunsIn service (bound x y)
      (cfg (some service.entry) true true isMul code depth
        (Encoding.encodeList encode (y :: x :: xs)) context)
      (cfg none false false false code depth
        (Encoding.encodeList encode (operation x y :: xs)) context)

/-- Pure closure facts for the values accepted by the arithmetic tables. -/
structure Validity {R : Type*} [Add R] [Mul R] (valid : R → Prop) (project : R → R) : Prop where
  load_valid : ∀ x, valid (project x)
  add_valid : ∀ x y, valid x → valid y → valid (x + y)
  mul_valid : ∀ x y, valid x → valid y → valid (x * y)

theorem Validity.eval_valid {R : Type*} [Add R] [Mul R] {valid : R → Prop} {project : R → R}
    (h : Validity valid project) (e : Algorithm.Expr R) : valid (e.map project).eval := by
  induction e with
  | lit x => exact h.load_valid x
  | add e f he hf => exact h.add_valid _ _ he hf
  | mul e f he hf => exact h.mul_valid _ _ he hf

variable (add : Program (3 + r) (4 + s) a) (mul : Program (3 + r) (4 + s) b)
  (loader : Program (3 + r) (4 + s) c)

theorem push_instruction {R : Type*} (encode : R → List Bool) (project : R → R)
    (loadBound : R → ℕ) (context : Fin s → List Bool)
    (hload : LoadImplements encode project loader loadBound context)
    (x : R) (xs : List R) (code depth : List Bool) (v p op : Bool) :
    RunsIn (program add mul loader) (11 * (encode x).length + 17 + loadBound x)
      (cfg (some (baseLabel 0)) v p op (false :: (Encoding.frame (encode x) ++ code)) depth
        (Encoding.encodeList encode xs) context)
      (cfg (some (baseLabel 0)) false false false code (true :: depth)
        (Encoding.encodeList encode (project x :: xs)) context) := by
  obtain ⟨n, hn, ht⟩ := hload x xs code (true :: depth) op
  have hs := ProgramLinking.relocate_trace loader (program add mul loader) id id loadLabel
    (some (baseLabel 0)) (cfg none false false false [] [] [] context)
    Function.injective_id Function.injective_id (program_load_code add mul loader) ht
  simp only [ProgramLinking.embedCfg_id, ProgramLinking.relabelCfg,
    ProgramLinking.relocatePc, cfg] at hs
  have hp := raw_push_trace add mul loader context (encode x) code depth
    (Encoding.encodeList encode xs) v p op
  refine ⟨11 * (encode x).length + 17 + n, by omega, ?_⟩
  exact hp.trans hs

section Execution

variable {R : Type*} [Add R] [Mul R] (encode : R → List Bool)
variable (addBound mulBound : R → R → ℕ) (context : Fin s → List Bool) (valid : R → Prop)
variable (hadd : ImplementsOn valid encode (· + ·) false add addBound context)
variable (hmul : ImplementsOn valid encode (· * ·) true mul mulBound context)

include hadd in
omit [Mul R] in
theorem add_instruction (x y : R) (hx : valid x) (hy : valid y) (xs : List R) (code depth : List Bool) (v p op : Bool) :
    RunsIn (program add mul loader) (14 + addBound x y)
      (cfg (some (baseLabel 0)) v p op (true :: false :: code) (true :: true :: depth)
        (Encoding.encodeList encode (y :: x :: xs)) context)
      (cfg (some (baseLabel 0)) false false false code (true :: depth)
        (Encoding.encodeList encode ((x + y) :: xs)) context) := by
  obtain ⟨n, hn, ht⟩ := hadd x y hx hy xs code (true :: depth)
  have hs := ProgramLinking.relocate_trace add (program add mul loader) id id addLabel
    (some (baseLabel 0)) (cfg none false false false [] [] [] context)
    Function.injective_id Function.injective_id (program_add_code add mul loader) ht
  simp only [ProgramLinking.embedCfg_id, ProgramLinking.relabelCfg,
    ProgramLinking.relocatePc, cfg] at hs
  have hc : Trace (program add mul loader) 1
      (cfg (some (baseLabel 16)) true true false code (true :: depth)
        (Encoding.encodeList encode (y :: x :: xs)) context)
      (cfg (some (addLabel add.entry)) true true false code (true :: depth)
        (Encoding.encodeList encode (y :: x :: xs)) context) :=
    .cons (add_call_step add mul loader context code _ _) (.refl _)
  have hp := binary_prepare_trace add mul loader context false code
    (Encoding.encodeList encode (y :: x :: xs)) depth v p op
  have h := (hp.trans hc).trans hs
  refine ⟨13 + 1 + n, by omega, ?_⟩
  exact h

include hmul in
omit [Add R] in
theorem mul_instruction (x y : R) (hx : valid x) (hy : valid y) (xs : List R) (code depth : List Bool) (v p op : Bool) :
    RunsIn (program add mul loader) (14 + mulBound x y)
      (cfg (some (baseLabel 0)) v p op (true :: true :: code) (true :: true :: depth)
        (Encoding.encodeList encode (y :: x :: xs)) context)
      (cfg (some (baseLabel 0)) false false false code (true :: depth)
        (Encoding.encodeList encode ((x * y) :: xs)) context) := by
  obtain ⟨n, hn, ht⟩ := hmul x y hx hy xs code (true :: depth)
  have hs := ProgramLinking.relocate_trace mul (program add mul loader) id id mulLabel
    (some (baseLabel 0)) (cfg none false false false [] [] [] context)
    Function.injective_id Function.injective_id (program_mul_code add mul loader) ht
  simp only [ProgramLinking.embedCfg_id, ProgramLinking.relabelCfg,
    ProgramLinking.relocatePc, cfg] at hs
  have hc : Trace (program add mul loader) 1
      (cfg (some (baseLabel 17)) true true true code (true :: depth)
        (Encoding.encodeList encode (y :: x :: xs)) context)
      (cfg (some (mulLabel mul.entry)) true true true code (true :: depth)
        (Encoding.encodeList encode (y :: x :: xs)) context) :=
    .cons (mul_call_step add mul loader context code _ _) (.refl _)
  have hp := binary_prepare_trace add mul loader context true code
    (Encoding.encodeList encode (y :: x :: xs)) depth v p op
  have h := (hp.trans hc).trans hs
  refine ⟨13 + 1 + n, by omega, ?_⟩
  exact h

/-- Interpreter cost includes original literal byte length, its projection,
and the dispatcher overhead on both binary operations. -/
def exprCost (project : R → R) (loadBound : R → ℕ) : Algorithm.Expr R → ℕ
  | .lit x => 11 * (encode x).length + 17 + loadBound x
  | .add e f => exprCost project loadBound e + exprCost project loadBound f +
      (14 + addBound (e.map project).eval (f.map project).eval)
  | .mul e f => exprCost project loadBound e + exprCost project loadBound f +
      (14 + mulBound (e.map project).eval (f.map project).eval)

variable (project : R → R) (loadBound : R → ℕ)
variable (hload : LoadImplements encode project loader loadBound context)
variable (hvalid : Validity valid project)

include hadd hmul hload hvalid in
/-- Every source literal is projected, including a single-literal expression.
All source suffix bytes, lower operands, and fixed context are unchanged. -/
theorem compile_runsIn (e : Algorithm.Expr R) (suffix : List (Algorithm.Instr R))
    (xs : List R) (v p op : Bool) :
    RunsIn (program add mul loader) (exprCost encode addBound mulBound project loadBound e)
      (cfg (some (baseLabel 0)) v p op (serializeCode encode (e.compile ++ suffix))
        (operandDepth xs) (Encoding.encodeList encode xs) context)
      (cfg (some (baseLabel 0)) false false false (serializeCode encode suffix)
        (operandDepth ((e.map project).eval :: xs))
        (Encoding.encodeList encode ((e.map project).eval :: xs)) context) := by
  induction e generalizing suffix xs v p op with
  | lit x =>
      simpa [Algorithm.Expr.compile, Algorithm.Expr.map, Algorithm.Expr.eval, exprCost,
        serializeCode, serializeInstr, operandDepth, List.replicate_succ] using
        push_instruction add mul loader encode project loadBound context hload x xs
          (serializeCode encode suffix) (operandDepth xs) v p op
  | add e f he hf =>
      have h₁ := he (f.compile ++ .add :: suffix) xs v p op
      have h₂ := hf (.add :: suffix) ((e.map project).eval :: xs) false false false
      have h₃ := add_instruction add mul loader encode addBound context valid hadd
        (e.map project).eval (f.map project).eval (hvalid.eval_valid e) (hvalid.eval_valid f) xs
        (serializeCode encode suffix) (operandDepth xs) false false false
      simpa [Algorithm.Expr.compile, Algorithm.Expr.map, Algorithm.Expr.eval, exprCost,
        List.append_assoc, serializeCode, serializeInstr, operandDepth, List.replicate_succ] using
        (h₁.trans h₂).trans h₃
  | mul e f he hf =>
      have h₁ := he (f.compile ++ .mul :: suffix) xs v p op
      have h₂ := hf (.mul :: suffix) ((e.map project).eval :: xs) false false false
      have h₃ := mul_instruction add mul loader encode mulBound context valid hmul
        (e.map project).eval (f.map project).eval (hvalid.eval_valid e) (hvalid.eval_valid f) xs
        (serializeCode encode suffix) (operandDepth xs) false false false
      simpa [Algorithm.Expr.compile, Algorithm.Expr.map, Algorithm.Expr.eval, exprCost,
        List.append_assoc, serializeCode, serializeInstr, operandDepth, List.replicate_succ] using
        (h₁.trans h₂).trans h₃

include hadd hmul hload hvalid in
/-- Complete execution initializes the list marker and ends after the real EOF
halt. The final singleton contains the evaluation of projected literals. -/
theorem complete_runsIn (e : Algorithm.Expr R) :
    RunsIn (program add mul loader) (exprCost encode addBound mulBound project loadBound e + 5)
      (cfg (some (program add mul loader).entry) false false false
        (serializeCode encode e.compile) [] [] context)
      (cfg none false false false [] (operandDepth [(e.map project).eval])
        (Encoding.encodeList encode [(e.map project).eval]) context) := by
  have he := compile_runsIn add mul loader encode addBound mulBound context valid hadd hmul
    project loadBound hload hvalid e [] [] false false false
  have he' : RunsIn (program add mul loader) (exprCost encode addBound mulBound project loadBound e)
      (cfg (some (baseLabel 0)) false false false (serializeCode encode e.compile) [] [false] context)
      (cfg (some (baseLabel 0)) false false false [] (operandDepth [(e.map project).eval])
        (Encoding.encodeList encode [(e.map project).eval]) context) := by
    simpa only [List.append_nil, serializeCode, operandDepth, List.length_nil,
      List.replicate_zero, Encoding.encodeList] using he
  have hb : RunsIn (program add mul loader) 2
      (cfg (some (program add mul loader).entry) false false false
        (serializeCode encode e.compile) [] [] context)
      (cfg (some (baseLabel 0)) false false false (serializeCode encode e.compile) [] [false] context) :=
    ⟨2, le_rfl, boot_trace add mul loader context _⟩
  have hf : RunsIn (program add mul loader) 3
      (cfg (some (baseLabel 0)) false false false [] (operandDepth [(e.map project).eval])
        (Encoding.encodeList encode [(e.map project).eval]) context)
      (cfg none false false false [] (operandDepth [(e.map project).eval])
        (Encoding.encodeList encode [(e.map project).eval]) context) :=
    ⟨3, le_rfl, finish_trace add mul loader context _ _ false false false⟩
  convert (hb.trans he').trans hf using 1
  omega

end Execution

end SubexponentialSAT.SubexpProjectedInterpreter

end OAI.Algorithms
