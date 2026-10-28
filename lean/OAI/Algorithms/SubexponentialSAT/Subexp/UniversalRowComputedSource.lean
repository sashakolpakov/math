import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowAssemblyPrepared
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowTableSource
import OAI.Algorithms.SubexponentialSAT.Subexp.ComputedRowSource
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientNormalization

namespace OAI.Algorithms

/-!
# The actual correction arrays and the represented universal row

Natural-index reads are derived from the arrays built by the physical
producer. Only individual scalar decoder laws remain; neither an array
result equality nor a row-polynomial equality is an input.
-/

namespace SubexponentialSAT.Subexp.UniversalRowComputedSource

open MulticolorTypes SubexpSymbolicCost SubexpRepresentedRows SubexpRowInterpolation
open UniversalRowAssembly (computedTables)

variable {r Q Δ : ℕ} (p : ℕ) [Fact p.Prime]
variable (i : Fin Δ) (u y : UniversalType r Q Δ) (xs : List (ZMod p))
variable (inverse negative : Fin Q → List Bool)
variable (difference : Fin Q → Fin Q → List Bool)

theorem values_getD (j : Fin Q) :
    (computedTables p i u y xs inverse negative difference).values.getD j.val [] =
      CorrectionScalarCanonical.quartet p (-MatrixExtendedEntryProgram.value p i j u y xs) := by
  change ((List.range' 0 Q).map (CorrectionVectorProgram.bytesAt p i u y xs)).getD j.val [] = _
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp [CorrectionVectorProgram.bytesAt, CorrectionVectorProgram.valueAt, j.isLt]

theorem inverses_getD (j : Fin Q) :
    (computedTables p i u y xs inverse negative difference).inverses.getD j.val [] = inverse j := by
  change (List.ofFn inverse).getD j.val [] = _
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

theorem negatives_getD (j : Fin Q) :
    (computedTables p i u y xs inverse negative difference).negatives.getD j.val [] = negative j := by
  change (List.ofFn negative).getD j.val [] = _
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

theorem differences_getD (j k : Fin Q) :
    ((computedTables p i u y xs inverse negative difference).differences.getD j.val []).getD k.val [] =
      difference j k := by
  change ((List.ofFn (fun j => List.ofFn (difference j))).getD j.val []).getD k.val [] = _
  have hj : (List.ofFn (fun j => List.ofFn (difference j))).getD j.val [] =
      List.ofFn (difference j) := by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  rw [hj, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

theorem selected_eq_positions :
    UniversalRowAssembly.selected i u y =
      UniversalRowTableSource.positions (mismatchPositions (fun v => v.head) (u.slot i) y) := by
  rw [UniversalRowTableSource.positions_mismatch]
  rfl

variable {C E : Type*} [Field E] [Algebra (ZMod p) E]
variable (source : RepresentedRing C E) (cache : NodeCache C Q)
variable {node : Fin Q → E} (units : NodeUnits node)
variable (hnode : ∀ j, source.decode (cache.node j) = node j)
variable (hinv : ∀ j, source.decode (cache.inverse j) = units.nodeInverse j)
variable (hdiff : ∀ j k, source.decode (cache.difference j k) = units.differenceInverse j k)
variable (embed : ZMod p → C) (hembed : ∀ z, source.decode (embed z) = algebraMap (ZMod p) E z)
variable (decode : List Bool → E)
variable (hscalar : ∀ z, decode (CorrectionScalarCanonical.quartet p z) = algebraMap (ZMod p) E z)
variable (hinverse : ∀ j, decode (inverse j) = source.decode (cache.inverse j))
variable (hnegative : ∀ j, decode (negative j) = source.decode ((source.negRun (cache.node j)).1))
variable (hdifference : ∀ j k, decode (difference j k) = source.decode (cache.difference j k))

include hnode hinv hdiff hembed hscalar hinverse hnegative hdifference in
/-- The computed vector, actual cache arrays, and generated mismatch list
give the full universal-row polynomial. All decoding premises are scalar. -/
theorem row_eval (delta : List Bool)
    (hdelta : decode delta = source.decode (if u = y then source.oneRun.1 else source.zeroRun.1)) :
    (UniversalRowProgram.rowExpression Polynomial.X
      (UniversalRowSource.mapRow (fun bits => Polynomial.C (decode bits))
        (UniversalRowDataProgram.row (computedTables p i u y xs inverse negative difference)
          (UniversalRowAssembly.selected i u y) delta (List.replicate xs.length true)))).eval =
      (SubexpTaylorExecution.mapCode source.decode
        (ComputedRowSource.universalCode source.program cache embed xs.length
          (fun j => xs.getD j 0 * (2 : ZMod p) ^ j) u i y)).denote := by
  rw [selected_eq_positions i u y]
  apply UniversalRowTableSource.row_eval_of_decode
    (cache := cache) (t := computedTables p i u y xs inverse negative difference)
    source units hnode hinv hdiff decode
    u (fun v => v.head) (u.slot i) xs.length
    (matrixValues source.program embed
      (fun t g i => ElementaryMatrix.jointMatrixDP i t g xs.length
        (fun j => xs.getD j 0 * (2 : ZMod p) ^ j)) u i) y delta
    (List.replicate xs.length true)
  · intro j
    rw [values_getD p i u y xs inverse negative difference j, hscalar]
    simp only [matrixValues, source.neg_correct, hembed,
      map_neg, MatrixExtendedEntryProgram.value]
  · intro j
    rw [inverses_getD p i u y xs inverse negative difference j, hinverse]
  · intro j k
    rw [differences_getD p i u y xs inverse negative difference j k, hdifference]
  · intro j
    rw [negatives_getD p i u y xs inverse negative difference j, hnegative]
  · exact hdelta
  · simp only [List.length_replicate]

include hnode hinv hdiff hembed hscalar hinverse hnegative hdifference in
/-- A successful normalized coefficient checker identifies the same row
used by the chosen layout, independently of coefficient-search order. -/
theorem row_eval_selected (A R : ℕ) (hlength : xs.length = R)
    (hcheck : ∀ d : Fin R,
      CoefficientDynamics.evaluate xs (A + d.val) = (-1 : ZMod p) ^ (A + d.val))
    (delta : List Bool)
    (hdelta : decode delta = source.decode (if u = y then source.oneRun.1 else source.zeroRun.1)) :
    (UniversalRowProgram.rowExpression Polynomial.X
      (UniversalRowSource.mapRow (fun bits => Polynomial.C (decode bits))
        (UniversalRowDataProgram.row (computedTables p i u y xs inverse negative difference)
          (UniversalRowAssembly.selected i u y) delta (List.replicate xs.length true)))).eval =
      (SubexpTaylorExecution.mapCode source.decode
        (ComputedRowSource.universalCode source.program cache embed R
          (CoefficientSearch.coefficientsNat p A R) u i y)).denote := by
  rw [row_eval p i u y xs inverse negative difference source cache units hnode hinv hdiff
    embed hembed decode hscalar hinverse hnegative hdifference delta hdelta]
  have hc : (fun j => xs.getD j 0 * (2 : ZMod p) ^ j) =
      CoefficientSearch.coefficientsNat p A R :=
    CoefficientNormalization.coefficients_eq p A R (Fact.out : p.Prime).pos xs hlength hcheck
  rw [hlength, hc]

end SubexponentialSAT.Subexp.UniversalRowComputedSource

end OAI.Algorithms
