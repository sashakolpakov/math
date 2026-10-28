import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutExecution
import OAI.Algorithms.SubexponentialSAT.SubexpDenseRowTableSemantics

namespace OAI.Algorithms

/-! The data produced by the complete Main layout phase. The row master's
typed coefficient arrays are recovered from the actual table bytes, and the
coefficient checker equations follow from the produced coefficient vector. -/

namespace SubexponentialSAT.SubexpMainLayoutExecution

open BitProgram StructuredCalls SubexpMainProgram Subexp
open SubexpLayoutPorts (Allocation ordinary master)

theorem check_of_coefficients {p R A : ℕ} [Fact p.Prime]
    (xs : List (ZMod p)) (hlength : xs.length = R)
    (hcoeff : CoefficientNormalization.unnormalize xs = CoefficientSearch.coefficientsNat p A R)
    (d : Fin R) :
    CoefficientDynamics.evaluate xs (A + d.val) = (-1 : ZMod p) ^ (A + d.val) := by
  unfold CoefficientDynamics.evaluate
  rw [hlength]
  change (∑ j ∈ Finset.range R,
    CoefficientNormalization.unnormalize xs j * ((A + d.val).choose j : ZMod p)) = _
  rw [hcoeff]
  exact CoefficientSearch.coefficientsNat_spec p A R (Fact.out : p.Prime).pos d

variable {er es p r Δ R D : ℕ} [Fact p.Prime] [NeZero r]
variable {alloc : Allocation es} {a middle out : MainState er es}
variable {hregs : 16 ≤ er} {hr : 0 < r} {hQ : 0 < p^4 - 1}
variable {scopes : List (List ℕ)}
variable {hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ}
variable {tables : List (List Bool)}
variable (h : Result hregs alloc a middle out p r Δ R D hr hQ scopes hd tables)

include h

theorem Result.coefficient_check (d : Fin R) :
    CoefficientDynamics.evaluate (List.ofFn h.choices.coefficients)
      (TailInterval.intervalStart r (p^4 - 1) R + d.val) =
        (-1 : ZMod p) ^ (TailInterval.intervalStart r (p^4 - 1) R + d.val) :=
  check_of_coefficients _ List.length_ofFn h.choices.coefficientCorrect d

noncomputable def Result.expressions : List (List (SubexpTaylorRowCorrectness.RowExpr p)) :=
  SubexpDenseRowTableSemantics.expressions h.rows.cacheFacts.source
    (List.ofFn h.choices.coefficients) h.rows.cacheFacts.inverse h.rows.cacheFacts.negative
    h.rows.cacheFacts.difference h.choices.packing.packing scopes hd

theorem Result.row_master (hvalid : ∀ C ∈ scopes, ∀ v ∈ C, v < D) :
    out.stacks (ordinary alloc 255) =
      SubexpTaylorCacheControl.encodeRows SubexpTaylorRow.flat
        (SubexpNodeCacheTyped.rows p (D + 1) h.rows.cacheFacts.source R h.expressions) := by
  have hb := SubexpDenseRowTableSemantics.tableCode_eq_encodeRows h.rows.cacheFacts.source
    (List.ofFn h.choices.coefficients) h.rows.cacheFacts.inverse h.rows.cacheFacts.negative
    h.rows.cacheFacts.difference h.choices.packing.packing scopes hd (D + 1) hvalid
  simpa only [List.length_ofFn, Result.expressions] using h.rows.rows.output.trans hb

theorem Result.expression_count : h.expressions.length = (scopes.map List.length).sum :=
  SubexpDenseRowTableSemantics.expressions_length h.rows.cacheFacts.source
    (List.ofFn h.choices.coefficients) h.rows.cacheFacts.inverse h.rows.cacheFacts.negative
    h.rows.cacheFacts.difference h.choices.packing.packing scopes hd

theorem Result.expression_width : ∀ row ∈ h.expressions, row.length = D :=
  SubexpDenseRowTableSemantics.expressions_width h.rows.cacheFacts.source
    (List.ofFn h.choices.coefficients) h.rows.cacheFacts.inverse h.rows.cacheFacts.negative
    h.rows.cacheFacts.difference h.choices.packing.packing scopes hd

theorem Result.saved_master (i : Fin 32) (hi : i ≠ 28) :
    out.stacks (master alloc i) = middle.stacks (master alloc i) :=
  SubexpMainLayoutRows.Result.master_frame (List.ofFn h.choices.coefficients)
    h.choices.packing.packing scopes hd h.rows i hi

theorem Result.scope_master : out.stacks (master alloc 0) = SubexpPlanAlphabetBase.scopeBytes scopes :=
  (h.saved_master 0 (by decide)).trans h.choices.prefixResult.scopeBytes

theorem Result.table_master : out.stacks (master alloc 1) = Encoding.encodeList id tables :=
  (h.saved_master 1 (by decide)).trans h.choices.prefixResult.tableBytes

theorem Result.assignment_master : out.stacks (master alloc 2) =
    SubexpAssignmentStaging.assignedBytes Δ D scopes hd h.choices.first h.choices.tail :=
  (h.saved_master 2 (by decide)).trans h.choices.prefixResult.assignment

theorem Result.coefficient_master : out.stacks (master alloc 9) =
    CoefficientSearchSemantics.encode p h.choices.coefficients :=
  (h.saved_master 9 (by decide)).trans h.choices.coefficientBytes

theorem Result.packing_master (i : Fin 6) :
    out.stacks (master alloc (SubexpMainPacking.outputIndex i)) =
      SubexpMainPacking.outputBytes h.choices.packing i := by
  have hi : SubexpMainPacking.outputIndex i ≠ 28 := by fin_cases i <;> decide
  exact (h.saved_master _ hi).trans (h.choices.packingOutputs i)

theorem Result.basis_master : out.stacks (master alloc 14) =
    ProgramEncoding.encodeRecords (h.choices.rows.map ProgramEncoding.encodeRecords) :=
  (h.saved_master 14 (by decide)).trans h.choices.basisBytes

end SubexponentialSAT.SubexpMainLayoutExecution

end OAI.Algorithms
