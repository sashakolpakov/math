import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRowToTaylor
import OAI.Algorithms.SubexponentialSAT.SubexpTaylorRow

namespace OAI.Algorithms

/-!
# Actual source rows to finite Taylor columns

The source expression is evaluated in the residue field before the complete
coefficient array is lifted.  The physical Taylor row program then shifts
that whole array and retains the requested coefficients.  These definitions
name the exact lists produced by those programs; the only row-specific
semantic premise is the degree bound on the source polynomial.
-/

namespace SubexponentialSAT.SubexpTaylorRowCorrectness

open SubexpLiftRing SubexpQuarticRing

abbrev SourceCode (p : ℕ) := SubexpRowPolynomialCalls.Coefficient p 1
abbrev TargetCode (p μ : ℕ) := SubexpTaylorRow.Code p μ
abbrev RowExpr (p : ℕ) := Algorithm.Expr (List (SourceCode p))

variable (p μ : ℕ) [Fact p.Prime]
variable (source : SubexpSelectedConversions.Prepared p 0)

/-- The complete coefficient list emitted by `SubexpRowToTaylor.run`, before
the parser-facing reversal of its bytes. -/
def sourceOutput (R : ℕ) (e : RowExpr p) : List (TargetCode p μ) :=
  letI : Add (List (SourceCode p)) :=
    ⟨SubexpRowPostfixBridge.addValue source.program⟩
  letI : Mul (List (SourceCode p)) :=
    ⟨SubexpRowPostfixBridge.mulValue p 1 source.modulus source.reduction source.zero (R + 1)⟩
  SubexpCoefficientLiftArray.liftedArray p μ source.modulus
    ((e.map (SubexpRowPostfixBridge.loadValue source.zero (R + 1))).eval)

theorem sourceOutput_length (R : ℕ) (e : RowExpr p) :
    (sourceOutput p μ source R e).length = R + 1 := by
  let _ : Add (List (SourceCode p)) :=
    ⟨SubexpRowPostfixBridge.addValue source.program⟩
  let _ : Mul (List (SourceCode p)) :=
    ⟨SubexpRowPostfixBridge.mulValue p 1 source.modulus source.reduction source.zero (R + 1)⟩
  change (SubexpCoefficientLiftArray.liftedArray p μ source.modulus
    ((e.map (SubexpRowPostfixBridge.loadValue source.zero (R + 1))).eval)).length = R + 1
  simp only [SubexpCoefficientLiftArray.liftedArray, List.length_map]
  exact (SubexpRowPostfixBridge.validity p 1 source.modulus source.reduction source.zero
    (R + 1) source.program).eval_valid e

theorem sourceOutput_denote (hμ : 0 < μ) (R : ℕ) (e : RowExpr p)
    (hdegree : ((e.map (SubexpRowSourceSemantics.denote source)).eval).natDegree ≤ R) :
    PolynomialAlgorithm.denote ((sourceOutput p μ source R e).map
      (SubexpHornerMachine.decode p μ (QuarticSearch.liftedCoefficients p μ))) =
      SubexpExplicitLift.liftPolynomial (SubexpActualRing.sectionValue p μ hμ) R
        ((e.map (SubexpRowSourceSemantics.denote source)).eval) := by
  exact SubexpRowToTaylor.output_denote p μ source R hμ e hdegree

variable (M : SubexpPreparedQuartic.Modulus p μ)
variable (reduction theta : TargetCode p μ)

/-- Exactly the ordered coefficient list emitted by the physical row-cache
program when its input is the actual source-row output. -/
def column (R N : ℕ) (e : RowExpr p) : List (TargetCode p μ) :=
  SubexpTaylorRow.cache p μ M reduction theta N (sourceOutput p μ source R e)

def entry (R N : ℕ) (e : RowExpr p) (j : Fin N) : TargetCode p μ :=
  (column p μ source M reduction theta R N e).getD j.val
    (SubexpHornerMachine.zeroCode p μ)

theorem column_length (R N : ℕ) (e : RowExpr p) :
    (column p μ source M reduction theta R N e).length = N := by
  exact SubexpTaylorRow.cache_length p μ M reduction theta N _

/-- No Taylor-array correctness hypothesis is supplied: the coefficient is
derived from the actual source evaluator, coefficient lift, and full shift. -/
theorem entry_eq (hμ : 0 < μ)
    (hreduction : reduction.map (wordValue p μ) =
      reductionData (QuarticSearch.liftedCoefficients p μ))
    (R N : ℕ) (e : RowExpr p)
    (hdegree : ((e.map (SubexpRowSourceSemantics.denote source)).eval).natDegree ≤ R)
    (j : Fin N) :
    SubexpHornerMachine.decode p μ (QuarticSearch.liftedCoefficients p μ)
      (entry p μ source M reduction theta R N e j) =
      ((SubexpExplicitLift.liftPolynomial (SubexpActualRing.sectionValue p μ hμ) R
        ((e.map (SubexpRowSourceSemantics.denote source)).eval)).comp
          (Polynomial.X + Polynomial.C
            (SubexpHornerMachine.decode p μ (QuarticSearch.liftedCoefficients p μ) theta))).coeff j.val := by
  have h := SubexpTaylorRow.cache_coeff p μ M (QuarticSearch.liftedCoefficients p μ)
    reduction theta hreduction N (sourceOutput p μ source R e) j.val j.isLt
  rw [sourceOutput_denote p μ source hμ R e hdegree] at h
  exact h

/-- Exact ordered-list equality for the finite array expected by the raw
incidence-argument emitter. -/
theorem column_eq_ofFn (R N : ℕ) (e : RowExpr p) :
    column p μ source M reduction theta R N e =
      List.ofFn (entry p μ source M reduction theta R N e) := by
  exact SubexpTaylorRow.cache_eq_ofFn_getD p μ M reduction theta N _

def columns {D : ℕ} (R N : ℕ) (rows : Fin D → RowExpr p) :
    List (List (TargetCode p μ)) :=
  List.ofFn (fun i => column p μ source M reduction theta R N (rows i))

theorem columns_eq_ofFn {D : ℕ} (R N : ℕ) (rows : Fin D → RowExpr p) :
    columns p μ source M reduction theta R N rows =
      List.ofFn (fun i => List.ofFn
        (entry p μ source M reduction theta R N (rows i))) := by
  apply congrArg List.ofFn
  funext i
  exact column_eq_ofFn p μ source M reduction theta R N (rows i)

/-- The payload lists have exactly the shape accepted by the concrete
incidence-argument producer. -/
theorem column_bits_eq {D : ℕ} (R N : ℕ) (rows : Fin D → RowExpr p) :
    (columns p μ source M reduction theta R N rows).map
      (List.map SubexpTaylorRow.flat) =
      List.ofFn (fun i => List.ofFn (fun j => SubexpTaylorRow.flat
        (entry p μ source M reduction theta R N (rows i) j))) := by
  rw [columns_eq_ofFn]
  simp only [List.map_ofFn, Function.comp_def]

/-- The nested cache bytes are in coordinate-major order, with increasing
Taylor degree inside each coordinate. -/
theorem encoded_columns {D : ℕ} (R N : ℕ) (rows : Fin D → RowExpr p) :
    Encoding.encodeList (Encoding.encodeList SubexpTaylorRow.flat)
      (columns p μ source M reduction theta R N rows) =
      Encoding.encodeList id (List.ofFn (fun i =>
        Encoding.encodeList id (List.ofFn (fun j => SubexpTaylorRow.flat
          (entry p μ source M reduction theta R N (rows i) j))))) := by
  rw [columns_eq_ofFn]
  rw [← SubexpTaylorRow.encode_map]
  simp only [List.map_ofFn]
  apply congrArg (Encoding.encodeList id)
  apply congrArg List.ofFn
  funext i
  simpa only [List.map_ofFn, Function.comp_def, id_eq] using
    (SubexpTaylorRow.encode_map SubexpTaylorRow.flat
      (List.ofFn (entry p μ source M reduction theta R N (rows i)))).symm

end SubexponentialSAT.SubexpTaylorRowCorrectness

end OAI.Algorithms
