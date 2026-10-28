import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpKernelControl
import OAI.Algorithms.SubexponentialSAT.ProgramFrames
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

/-!
# Physical source construction for universal interpolation rows

The input holds raw coefficient payloads, node inverses, and negative nodes.
It does not contain polynomial instructions. Fixed nested scans emit the
Lagrange products and correction sum as postfix source in canonical list order.
The surrounding row-data producer supplies the selected mismatch positions;
its matrix, cache, and type-mask construction is tracked separately.
-/

namespace SubexponentialSAT.Subexp.UniversalRowProgram

open BitProgram StructuredCalls
open SubexpKernelControl (Word Accumulator pushWord operator operators emit bump
  state counterWord setCounter counterPort popTag unframe emitFramedLiteral emitLiteral
  emitOperator countOne drain scan scanCost)

structure Factor (C : Type*) where
  inverseDifference : C
  negativeNode : C

structure Term (C : Type*) where
  value : C
  inverseNode : C
  factors : List (Factor C)

structure Row (C : Type*) where
  delta : C
  terms : List (Term C)

def encodeFactor (f : Factor Word) : Word :=
  Encoding.frame f.inverseDifference ++ Encoding.frame f.negativeNode

def encodeTerm (t : Term Word) : Word :=
  Encoding.frame t.value ++ Encoding.frame t.inverseNode ++ Encoding.encodeList encodeFactor t.factors

def encodeRow (r : Row Word) : Word :=
  Encoding.frame r.delta ++ Encoding.encodeList encodeTerm r.terms

def factorExpression {R : Type*} (x : R) (f : Factor R) : Algorithm.Expr R :=
  .mul (.lit f.inverseDifference) (.add (.lit x) (.lit f.negativeNode))

def termExpression {R : Type*} [One R] (x : R) (t : Term R) : Algorithm.Expr R :=
  .mul (.lit t.value) (.mul (.mul (.lit t.inverseNode) (.lit x))
    (Algorithm.Expr.product (t.factors.map (factorExpression x))))

def rowExpression {R : Type*} [Zero R] [One R] (x : R) (r : Row R) : Algorithm.Expr R :=
  .add (.lit r.delta) (Algorithm.Expr.sum (r.terms.map (termExpression x)))

def factorCode (x : Word) (f : Factor Word) : Word :=
  pushWord f.inverseDifference ++ pushWord x ++ pushWord f.negativeNode ++
    operator false ++ operator true

def productCode (one x : Word) (fs : List (Factor Word)) : Word :=
  (fs.map (factorCode x)).flatten ++ pushWord one ++ operators true fs.length

def termCode (one x : Word) (t : Term Word) : Word :=
  pushWord t.value ++ pushWord t.inverseNode ++ pushWord x ++ operator true ++
    productCode one x t.factors ++ operator true ++ operator true

def rowCode (zero one x : Word) (r : Row Word) : Word :=
  pushWord r.delta ++ (r.terms.map (termCode one x)).flatten ++
    pushWord zero ++ operators false r.terms.length ++ operator false

def literalPorts : Fin 3 → Fin 8 := ![5, 3, 4]
theorem literalPorts_injective : Function.Injective literalPorts := by decide

abbrev emitX : Cmd 3 8 :=
  .call (ProgramLinking.liftProgram SubexpHornerProgram.Literal.program id literalPorts)

private theorem embed_literal (v p v' p' : Bool) (source zero one out : Word) (a : Accumulator) :
    embedState id literalPorts (state v p source zero one a)
      ⟨SubexpHornerProgram.triple v' p' true, SubexpHornerProgram.triple a.outer out []⟩ =
      state v' p' source zero one {a with output := out} := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id literalPorts_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h3 : i ≠ 3 := fun h => hi ⟨1, h.symm⟩
    fin_cases i <;> simp_all [state]

theorem emitX_eval (v p : Bool) (source zero one : Word) (a : Accumulator) :
    Eval emitX (8 * a.outer.length + 9) (state v p source zero one a)
      (state false false source zero one (emit (pushWord a.outer) a)) := by
  have ht := eval_call_lifted SubexpHornerProgram.Literal.program id literalPorts
    (state v p source zero one a) Function.injective_id literalPorts_injective
    (a := ⟨SubexpHornerProgram.triple v p true,
      SubexpHornerProgram.triple a.outer a.output []⟩)
    (b := ⟨SubexpHornerProgram.triple false false true,
      SubexpHornerProgram.triple a.outer ((pushWord a.outer).reverse ++ a.output) []⟩)
    (SubexpHornerProgram.Literal.trace a.outer a.output v p true)
  simpa only [SubexpHornerProgram.Literal.cfg, StructuredProgram.State.withPC,
    embed_literal, emitX, emit, pushWord] using ht

local infixr:60 " ;; " => Cmd.seq

abbrev factorBody : Cmd 3 8 :=
  emitFramedLiteral ;; emitX ;; emitFramedLiteral ;; emitOperator false ;; emitOperator true ;; countOne 6

def factorCost (x : Word) (f : Factor Word) : ℕ :=
  7 * f.inverseDifference.length + 7 * f.negativeNode.length + 8 * x.length + 29

def factorUpdate (x : Word) (f : Factor Word) (a : Accumulator) : Accumulator :=
  bump 1 (emit (factorCode x f) a)

/-- A real byte-level affine-factor construction from two scalar payloads. -/
theorem factorBody_eval (f : Factor Word) (source zero one : Word) (a : Accumulator) :
    Eval factorBody (factorCost a.outer f)
      (state false false (encodeFactor f ++ source) zero one a)
      (state false true source zero one (factorUpdate a.outer f a)) := by
  let a1 := emit (pushWord f.inverseDifference) a
  let a2 := emit (pushWord a.outer) a1
  let a3 := emit (pushWord f.negativeNode) a2
  let a4 := emit (operator false) a3
  let a5 := emit (operator true) a4
  have h1 := SubexpKernelControl.emitFramedLiteral_eval false false f.inverseDifference
    (Encoding.frame f.negativeNode ++ source) zero one a
  have h2 := emitX_eval false true (Encoding.frame f.negativeNode ++ source) zero one a1
  have h3 := SubexpKernelControl.emitFramedLiteral_eval false false f.negativeNode source zero one a2
  have h4 := SubexpKernelControl.emitOperator_eval false false true source zero one a3
  have h5 := SubexpKernelControl.emitOperator_eval true false true source zero one a4
  have h6 := SubexpKernelControl.countOne_eval 1 false true source zero one a5
  have ht := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))
  convert ht using 1
  all_goals simp [factorBody, factorCost, factorUpdate, factorCode, encodeFactor,
    a1, a2, a3, a4, a5, SubexpKernelControl.emit_emit, emit, bump,
    counterPort, counterWord, setCounter, List.append_assoc]
  all_goals omega

end SubexponentialSAT.Subexp.UniversalRowProgram

end OAI.Algorithms
