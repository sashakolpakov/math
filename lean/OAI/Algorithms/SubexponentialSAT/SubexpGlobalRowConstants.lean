import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpGlobalRowPacking
import OAI.Algorithms.SubexponentialSAT.SubexpGlobalRowEvaluation
import OAI.Algorithms.SubexponentialSAT.SubexpRowExpression

namespace OAI.Algorithms

/-! Complete physical executions of the three constant-row branches. The
packing lookup, literal emission, metadata cleanup, source arithmetic, and
coefficient lift all execute in the fixed global row program. -/

namespace SubexponentialSAT.SubexpGlobalRowConstants

open BitProgram StructuredCalls SubexpDenseRowTableProgram
  SubexpGlobalRowBranch SubexpGlobalRowLookup SubexpGlobalRowSelection
  Subexp.ConstructivePacking SubexpLiftRing SubexpQuarticRing
open SubexpRowPostfixInterpreter (contextStore)

variable {p : ℕ} [Fact p.Prime]

def coefficient (source : SubexpSelectedConversions.Prepared p 0) (one : Bool) :=
  if one then source.one else source.zero

def expression (source : SubexpSelectedConversions.Prepared p 0) (one : Bool) :
    SubexpGlobalRowEvaluation.Expression p := .lit [coefficient source one]

def output (μ : ℕ) (source : SubexpSelectedConversions.Prepared p 0) (R : ℕ) (one : Bool) : Word :=
  SubexpRowToTaylorCalls.output μ source R (expression source one)

def evaluationCost (μ : ℕ) (source : SubexpSelectedConversions.Prepared p 0)
    (R : ℕ) (one : Bool) : ℕ :=
  16 + SubexpRowToTaylor.runtimeBound R (baseWidth p 1) (baseWidth p μ)
    (SubexpRowToTaylorCalls.code (expression source one)).length

theorem code_length (source : SubexpSelectedConversions.Prepared p 0) (one : Bool) :
    (SubexpRowToTaylorCalls.code (expression source one)).length = 8 * baseWidth p 1 + 2 := by
  rw [show expression source one = .lit [coefficient source one] from rfl,
    SubexpGlobalRowEvaluation.code_literal]
  simp only [literalWord, List.length_cons, Encoding.length_frame, SubexpFlatAdd.encode_length]
  omega

theorem evaluationCost_eq (μ : ℕ) (source : SubexpSelectedConversions.Prepared p 0)
    (R : ℕ) (one : Bool) :
    evaluationCost μ source R one =
      16 + SubexpRowToTaylor.runtimeBound R (baseWidth p 1) (baseWidth p μ)
        (8 * baseWidth p 1 + 2) := by rw [evaluationCost, code_length]

theorem cached_coefficient (source : SubexpSelectedConversions.Prepared p 0)
    (a : Data) (hzero : a.stacks 131 = SubexpFlatAdd.encode source.zero)
    (hone : a.stacks 132 = SubexpFlatAdd.encode source.one) (one : Bool) :
    a.stacks (constantPort one) = SubexpFlatAdd.encode (coefficient source one) := by
  cases one
  · exact hzero
  · exact hone

variable (μ : ℕ) (source : SubexpSelectedConversions.Prepared p 0) (R : ℕ)
variable (sw tw : Word) (frame : Fin 6 → Word) (context : Fin 252 → Word)

/-- This helper consumes an actual preparation trace, not a cost annotation. -/
theorem after_prepare (universal : Code) (hμ : 0 < μ)
    (H : SubexpRowPostfixContext.Ready p 1 source.modulus source.reduction source.zero
      (R + 1) sw frame context)
    (hz : SubexpFlatAdd.encode source.zero = List.replicate (4 * baseWidth p 1) false)
    (h74 : contextStore context 74 = tw) (h87 : contextStore context 87 = [])
    (hB : tw.length = baseWidth p μ) (a b : Data) (n : ℕ) (one : Bool)
    (ha : ∀ i, a.stacks (SubexpRowToTaylorCalls.stack i) = contextStore context i)
    (hzero : a.stacks 131 = SubexpFlatAdd.encode source.zero)
    (hone : a.stacks 132 = SubexpFlatAdd.encode source.one)
    (he : Eval (prepare universal) n a b)
    (hb : b.stacks = Function.update a.stacks 26 (literalWord (a.stacks (constantPort one)))) :
    ∃ m ≤ n + evaluationCost μ source R one, ∃ regs,
      Eval (row universal SubexpRowToTaylorCalls.command) m a
        (SubexpGlobalRowEvaluation.result a regs (output μ source R one)) := by
  have hcode : b.stacks = Function.update a.stacks 26
      (SubexpRowToTaylorCalls.code (expression source one)) := by
    rw [hb, cached_coefficient source a hzero hone one]
    exact congrArg (Function.update a.stacks 26)
      (SubexpGlobalRowEvaluation.code_literal (coefficient source one)).symm
  obtain ⟨m, hm, regs, hr⟩ := SubexpGlobalRowEvaluation.row_after_prepare p μ source R
    sw tw frame context universal hμ H hz h74 h87 hB (expression source one) a b n ha he hcode
  exact ⟨m, by simpa only [evaluationCost, Nat.add_assoc] using hm, regs, hr⟩

variable {D : ℕ} {U : Type*} [DecidableEq U]

/-- An unselected source vertex produces its Kronecker row after a real
vertex-word comparison. No supplied Boolean chooses the constant. -/
theorem leftover (universal : Code) (P : PackingData (Fin D) U) (encodeType : U → Word)
    (v w : Fin D) (hv : P.lookup v = none) (a : Data)
    (htable : a.stacks 265 = SubexpGlobalRowPacking.table P encodeType)
    (hsource : a.stacks 260 = SubexpGlobalRowPacking.key v)
    (htarget : a.stacks 262 = SubexpGlobalRowPacking.key w)
    (hclean : HighClean a) (h26 : a.stacks 26 = []) (hμ : 0 < μ)
    (H : SubexpRowPostfixContext.Ready p 1 source.modulus source.reduction source.zero
      (R + 1) sw frame context)
    (hz : SubexpFlatAdd.encode source.zero = List.replicate (4 * baseWidth p 1) false)
    (h74 : contextStore context 74 = tw) (h87 : contextStore context 87 = [])
    (hB : tw.length = baseWidth p μ)
    (ha : ∀ i, a.stacks (SubexpRowToTaylorCalls.stack i) = contextStore context i)
    (hzero : a.stacks 131 = SubexpFlatAdd.encode source.zero)
    (hone : a.stacks 132 = SubexpFlatAdd.encode source.one) :
    ∃ m ≤ 400 * (SubexpGlobalRowPacking.volume P encodeType v)^2 + 18 * v.val + 9 * w.val +
      14 * (a.stacks (constantPort (decide (v.val = w.val)))).length +
      2 * (P.leftovers.idxOf v) + 99 + evaluationCost μ source R (decide (v.val = w.val)),
      ∃ regs, Eval (row universal SubexpRowToTaylorCalls.command) m a
        (SubexpGlobalRowEvaluation.result a regs (output μ source R (decide (v.val = w.val)))) := by
  obtain ⟨n, hn, regs, he⟩ := SubexpGlobalRowPacking.prepare_leftover universal P encodeType
    v w hv a htable hsource htarget hclean h26
  obtain ⟨m, hm, final, hr⟩ := after_prepare μ source R sw tw frame context universal
    hμ H hz h74 h87 hB a _ n (decide (v.val = w.val)) ha hzero hone he rfl
  exact ⟨m, hm.trans (Nat.add_le_add_right hn _), final, hr⟩

/-- A selected source and an unselected target execute the complete zero
row path, retaining the full R+1 coefficient array. -/
theorem rightLeftover (universal : Code) (P : PackingData (Fin D) U) (encodeType : U → Word)
    (v w : Fin D) (i : Fin P.blockCount) (u : U)
    (hv : P.lookup v = some (i,u)) (hw : P.lookup w = none) (a : Data)
    (htable : a.stacks 265 = SubexpGlobalRowPacking.table P encodeType)
    (hsource : a.stacks 260 = SubexpGlobalRowPacking.key v)
    (htarget : a.stacks 262 = SubexpGlobalRowPacking.key w)
    (hclean : HighClean a) (h26 : a.stacks 26 = []) (hμ : 0 < μ)
    (H : SubexpRowPostfixContext.Ready p 1 source.modulus source.reduction source.zero
      (R + 1) sw frame context)
    (hz : SubexpFlatAdd.encode source.zero = List.replicate (4 * baseWidth p 1) false)
    (h74 : contextStore context 74 = tw) (h87 : contextStore context 87 = [])
    (hB : tw.length = baseWidth p μ)
    (ha : ∀ j, a.stacks (SubexpRowToTaylorCalls.stack j) = contextStore context j)
    (hzero : a.stacks 131 = SubexpFlatAdd.encode source.zero)
    (hone : a.stacks 132 = SubexpFlatAdd.encode source.one) :
    ∃ m ≤ 400 * (SubexpGlobalRowPacking.volume P encodeType v)^2 +
      400 * (SubexpGlobalRowPacking.volume P encodeType w)^2 + 14 * (a.stacks 131).length +
      2 * (i.val + (encodeType u).length + P.leftovers.idxOf w) + 75 +
      evaluationCost μ source R false,
      ∃ regs, Eval (row universal SubexpRowToTaylorCalls.command) m a
        (SubexpGlobalRowEvaluation.result a regs (output μ source R false)) := by
  obtain ⟨n, hn, regs, he⟩ := SubexpGlobalRowPacking.prepare_rightLeftover universal P encodeType
    v w i u hv hw a htable hsource htarget hclean h26
  obtain ⟨m, hm, final, hr⟩ := after_prepare μ source R sw tw frame context universal
    hμ H hz h74 h87 hB a _ n false ha hzero hone he rfl
  exact ⟨m, hm.trans (Nat.add_le_add_right hn _), final, hr⟩

/-- Different covered blocks execute the complete zero row path after the
physical block-word comparison. -/
theorem differentBlock (universal : Code) (P : PackingData (Fin D) U) (encodeType : U → Word)
    (v w : Fin D) (i j : Fin P.blockCount) (u y : U)
    (hij : i ≠ j) (hv : P.lookup v = some (i,u)) (hw : P.lookup w = some (j,y)) (a : Data)
    (htable : a.stacks 265 = SubexpGlobalRowPacking.table P encodeType)
    (hsource : a.stacks 260 = SubexpGlobalRowPacking.key v)
    (htarget : a.stacks 262 = SubexpGlobalRowPacking.key w)
    (hclean : HighClean a) (h26 : a.stacks 26 = []) (hμ : 0 < μ)
    (H : SubexpRowPostfixContext.Ready p 1 source.modulus source.reduction source.zero
      (R + 1) sw frame context)
    (hz : SubexpFlatAdd.encode source.zero = List.replicate (4 * baseWidth p 1) false)
    (h74 : contextStore context 74 = tw) (h87 : contextStore context 87 = [])
    (hB : tw.length = baseWidth p μ)
    (ha : ∀ q, a.stacks (SubexpRowToTaylorCalls.stack q) = contextStore context q)
    (hzero : a.stacks 131 = SubexpFlatAdd.encode source.zero)
    (hone : a.stacks 132 = SubexpFlatAdd.encode source.one) :
    ∃ m ≤ 400 * (SubexpGlobalRowPacking.volume P encodeType v)^2 +
      400 * (SubexpGlobalRowPacking.volume P encodeType w)^2 + 18 * i.val + 9 * j.val +
      14 * (a.stacks 131).length +
      2 * (i.val + (encodeType u).length + j.val + (encodeType y).length) + 101 +
      evaluationCost μ source R false,
      ∃ regs, Eval (row universal SubexpRowToTaylorCalls.command) m a
        (SubexpGlobalRowEvaluation.result a regs (output μ source R false)) := by
  obtain ⟨n, hn, regs, he⟩ := SubexpGlobalRowPacking.prepare_differentBlock universal P encodeType
    v w i j u y hij hv hw a htable hsource htarget hclean h26
  obtain ⟨m, hm, final, hr⟩ := after_prepare μ source R sw tw frame context universal
    hμ H hz h74 h87 hB a _ n false ha hzero hone he rfl
  exact ⟨m, hm.trans (Nat.add_le_add_right hn _), final, hr⟩

theorem expression_denote (one : Bool) :
    ((expression source one).map (SubexpRowSourceSemantics.denote source)).eval =
      Polynomial.C (if one then 1 else 0) := by
  change SubexpRowSourceSemantics.denote source [coefficient source one] = _
  rw [SubexpRowExpression.denote_singleton]
  cases one
  · exact congrArg Polynomial.C source.residueRing.zero_correct
  · exact congrArg Polynomial.C source.residueRing.one_correct

theorem output_length (one : Bool) : (output μ source R one).length =
    (R + 1) * (4 * baseWidth p μ) :=
  SubexpRowToTaylorCalls.output_length μ source R (expression source one)

/-- The array whose exact bytes are returned by the physical program is
the coefficient section of the selected zero or identity constant. -/
theorem output_denote (hμ : 0 < μ) (one : Bool) :
    PolynomialAlgorithm.denote
      ((SubexpCoefficientLiftArray.liftedArray p μ source.modulus
        (SubexpRowToTaylorCalls.evaluated source R (expression source one))).map
          (SubexpRowLiftSemantics.targetDecode p μ)) =
      SubexpExplicitLift.liftPolynomial (SubexpActualRing.sectionValue p μ hμ) R
        (Polynomial.C (if one then 1 else 0)) := by
  have hd : ((expression source one).map (SubexpRowSourceSemantics.denote source)).eval.natDegree ≤ R := by
    rw [expression_denote]
    cases one <;> simp
  have h := SubexpRowToTaylor.output_denote p μ source R hμ (expression source one) hd
  rw [expression_denote] at h
  exact h

end SubexponentialSAT.SubexpGlobalRowConstants

end OAI.Algorithms
