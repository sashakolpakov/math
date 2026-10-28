import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFieldRowValues
import OAI.Algorithms.SubexponentialSAT.SubexpMaterializedTable
import OAI.Algorithms.SubexponentialSAT.SubexpLeafTables
import OAI.Algorithms.SubexponentialSAT.SubexpUnaryTableCorrectness

namespace OAI.Algorithms

/-!
# The numeric clause-row stream and the ordered factor table

The input scope list is used in its emitted order. Its labels are the
least-significant-first base-p digits of the rank. The materializer therefore
computes the little-endian clause factor, including both validity checks.
The final Boolean stream is paired with the same descending rank grid used
by the interpolation source; no sort or implicit coordinate reversal occurs.
-/

namespace SubexponentialSAT.SubexpRankedTable

open BinaryArithmetic SubexpFieldRowValues SubexpFieldRowProgram
open SubexpScopeMaterializer SubexpMaterializedBits SubexpMaterializedTable
open SubexpDigitGrid SubexpTableInterpolation

variable {D n p : ℕ} [Fact p.Prime]

/-- Pair Boolean-only output with its exact generated label order. Physical
serialization of those labels remains a separate program obligation. -/
def attachAnswers {k : ℕ} {C : Type*} (zero one : C) (answers : List Bool) :
    List (Row p k C) :=
  (descending p k).zipWith Row.mk
    (answers.map (fun answer => if answer = true then one else zero))

omit [Fact p.Prime] in
theorem attachAnswers_map {k : ℕ} {C : Type*} (zero one : C)
    (f : List.Vector (Fin p) k → Bool) :
    attachAnswers zero one ((descending p k).map f) =
      SubexpDigitGrid.rows (fun a => if f a = true then one else zero) := by
  unfold attachAnswers SubexpDigitGrid.rows
  rw [List.map_map]
  induction descending p k with
  | nil => rfl
  | cons a as ih =>
      simpa only [List.map_cons, List.zipWith_cons_cons, Function.comp_apply] using
        (congrArg (List.cons (Row.mk a (if f a = true then one else zero))) ih)

omit [Fact p.Prime] in
/-- The concrete zip can be indexed without changing the scope order. -/
theorem zip_labels_eq_ofFn (scope : List (Fin D)) (width : ℕ)
    (a : List.Vector (Fin p) scope.length) :
    scope.zip (a.toList.map (fun d => SubexpLiftRing.fixedBits width d.val)) =
      List.ofFn (fun i : Fin scope.length =>
        (scope.get i, SubexpLiftRing.fixedBits width (a.get i).val)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_zip, List.getElem_map, List.getElem_ofFn,
      List.Vector.toList_getElem, List.get_eq_getElem]
    rfl

omit [Fact p.Prime] in
/-- Decode the rank by exactly the same digit order as the row machine. -/
theorem jobs_eq_ofFn (m : Masters) (scope : List (Fin D))
    (hp : BinaryArithmetic.toNat m.modulus = p) (hcount : scope.length = m.arity.length)
    (rank : Fin (p ^ scope.length)) :
    jobs m scope rank.val = List.ofFn (fun i : Fin scope.length =>
      (scope.get i, SubexpLiftRing.fixedBits m.modulus.length
        ((rankEquiv p scope.length rank).get i).val)) := by
  unfold jobs labels
  rw [hp, ← hcount, ← rankEquiv_values p scope.length rank, List.map_map]
  exact zip_labels_eq_ofFn scope m.modulus.length (rankEquiv p scope.length rank)

private theorem wordAssignment_eq_getD (word : List Bool) (hlen : word.length = n) :
    SubexpClauseRowProgram.wordAssignment word hlen = fun i => word[i.val]?.getD false := by
  funext i
  have hi : i.val < word.length := by omega
  simp only [SubexpClauseRowProgram.wordAssignment, List.getElem?_eq_getElem hi,
    Option.getD_some]

section Clause

variable {b : Fin D → ℕ}
variable (positions : Fin n ≃ ((j : Fin D) × Fin (b j)))
variable (capacity : ∀ j, 2 ^ b j ≤ p) (F : SAT.CNF (Fin n)) (e : {C // C ∈ F})
variable (m : Masters) (scope : List (Fin D))
variable (hnodup : scope.Nodup)
variable (hmem : ∀ j, j ∈ scope ↔ j ∈ FactorReduction.cnfScope positions F e)

local notation "S" => SubexpLEFactorSystem.system positions capacity F
local notation "order" => SubexpLeafTables.scopeOfList S (Sum.inr e) scope hnodup hmem

/-- Actual materialization at a numeric rank equals the corresponding local
clause factor. All hypotheses describe input shape, addresses, or scope. -/
theorem value_eq_table (literals : List (SAT.Literal (Fin n)))
    (hliterals : literals.toFinset = e.val)
    (hp : BinaryArithmetic.toNat m.modulus = p) (hcount : scope.length = m.arity.length)
    (hell : m.ell.length ≤ m.modulus.length) (hn : n ≤ D * m.ell.length)
    (hsize : ∀ j, b j = min m.ell.length (n - j.val * m.ell.length))
    (hpositions : ∀ v : Fin n,
      v.val = (positions v).1.val * m.ell.length + (positions v).2.val)
    (rank : Fin (p ^ scope.length)) :
    value m scope literals rank.val =
      (S).table (.inr e) (fun j => ZMod.finEquiv p
        ((rankEquiv p scope.length rank).get ((order).symm j))) := by
  let a := rankEquiv p scope.length rank
  let x : {j // j ∈ FactorReduction.cnfScope positions F e} → ZMod p :=
    fun j => ZMod.finEquiv p (a.get ((order).symm j))
  let js := jobs m scope rank.val
  let chunks := zeroChunks D m.ell.length
  have hjs : js = List.ofFn (fun i : Fin scope.length =>
      (scope.get i, SubexpLiftRing.fixedBits m.modulus.length (a.get i).val)) :=
    jobs_eq_ofFn m scope hp hcount rank
  have hc : chunks.length = D := by simp [chunks, zeroChunks]
  have hrows : ∀ row ∈ chunks, row.length = m.ell.length := by
    intro row hr
    have he : row = List.replicate m.ell.length false := (List.mem_replicate.mp hr).2
    simp [he]
  have hw : ∀ job ∈ js, job.2.length = m.modulus.length := by
    intro job hj
    rw [hjs] at hj
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hj
    exact SubexpLiftRing.fixedBits_length _ _
  have hd : (js.map Prod.fst).Nodup := by
    simpa only [hjs, List.map_ofFn, Function.comp_def, List.ofFn_get] using hnodup
  have hval (i : Fin scope.length) :
      BinaryArithmetic.toNat (SubexpLiftRing.fixedBits m.modulus.length (a.get i).val) = (a.get i).val :=
    SubexpLiftRing.toNat_fixedBits_of_lt _ _
      ((a.get i).isLt.trans (hp ▸ ModularArithmetic.toNat_lt_pow_length m.modulus))
  have hcovered : ∀ j : {j // j ∈ FactorReduction.cnfScope positions F e},
      ∃ label, (j.val, label) ∈ js ∧ BinaryArithmetic.toNat label = (x j).val := by
    intro j
    let i := (order).symm j
    have hi : scope.get i = j.val := congrArg Subtype.val ((order).apply_symm_apply j)
    refine ⟨SubexpLiftRing.fixedBits m.modulus.length (a.get i).val, ?_, ?_⟩
    · rw [hjs]
      exact List.mem_ofFn.mpr ⟨i, by simp only [hi]⟩
    · simpa only [x, i, BooleanPacking.finEquiv_val] using hval i
  have honly : ∀ job ∈ js, ∃ j : {j // j ∈ FactorReduction.cnfScope positions F e},
      j.val = job.1 ∧ BinaryArithmetic.toNat job.2 = (x j).val := by
    intro job hj
    rw [hjs] at hj
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hj
    refine ⟨order i, rfl, ?_⟩
    simpa only [x, Equiv.symm_apply_apply, BooleanPacking.finEquiv_val] using hval i
  have hpadding : SubexpFactorProgram.allZero (chunks.flatten.drop n) = true := by
    rw [show chunks = zeroChunks D m.ell.length from rfl, zeroChunks_flatten]
    exact allZero_drop_replicate_false _ _
  have hlen := materialize_take_length m.ell.length m.modulus.length n js chunks true
    hc hrows hw hell hn
  have ht := output_eq_table m.ell.length m.modulus.length positions capacity F e x js chunks
    literals hliterals hc hrows hw hell hd hsize hpositions hcovered honly hpadding hlen
  rw [output, wordAssignment_eq_getD _ hlen] at ht
  exact ht

/-- Each emitted answer is attached to the exact descending rank vector.
This is a stream identity, not an assertion that row labels are physically
serialized by the Boolean-only table producer. -/
theorem descending_values_eq_orderedRows {C : Type*} (zero one : C)
    (literals : List (SAT.Literal (Fin n))) (hliterals : literals.toFinset = e.val)
    (hp : BinaryArithmetic.toNat m.modulus = p) (hcount : scope.length = m.arity.length)
    (hell : m.ell.length ≤ m.modulus.length) (hn : n ≤ D * m.ell.length)
    (hsize : ∀ j, b j = min m.ell.length (n - j.val * m.ell.length))
    (hpositions : ∀ v : Fin n,
      v.val = (positions v).1.val * m.ell.length + (positions v).2.val) :
    ((List.range (p ^ scope.length)).reverse.map (value m scope literals)).map
      (fun answer => if answer = true then one else zero) =
      (SubexpLeafTables.orderedRows S (.inr e) order zero one).map Row.value := by
  rw [← List.map_coe_finRange (p ^ scope.length)]
  simp only [List.map_reverse, List.map_map, SubexpLeafTables.orderedRows,
    SubexpDigitGrid.rows, descending, ascending, Function.comp_def]
  apply congrArg List.reverse
  apply List.map_congr_left
  intro rank _
  rw [value_eq_table positions capacity F e m scope hnodup hmem literals hliterals
    hp hcount hell hn hsize hpositions rank]

/-- The actual Boolean stream, paired with the agreed generated labels,
is the complete ordered-row source consumed by interpolation. -/
theorem attachAnswers_eq_orderedRows {C : Type*} (zero one : C)
    (literals : List (SAT.Literal (Fin n))) (hliterals : literals.toFinset = e.val)
    (hp : BinaryArithmetic.toNat m.modulus = p) (hcount : scope.length = m.arity.length)
    (hell : m.ell.length ≤ m.modulus.length) (hn : n ≤ D * m.ell.length)
    (hsize : ∀ j, b j = min m.ell.length (n - j.val * m.ell.length))
    (hpositions : ∀ v : Fin n,
      v.val = (positions v).1.val * m.ell.length + (positions v).2.val) :
    attachAnswers zero one
      ((List.range (p ^ scope.length)).reverse.map (value m scope literals)) =
      SubexpLeafTables.orderedRows S (.inr e) order zero one := by
  unfold attachAnswers
  rw [descending_values_eq_orderedRows positions capacity F e m scope hnodup hmem
    zero one literals hliterals hp hcount hell hn hsize hpositions]
  unfold SubexpLeafTables.orderedRows SubexpDigitGrid.rows
  rw [List.map_map]
  induction descending p scope.length with
  | nil => rfl
  | cons a as ih =>
      simpa only [List.map_cons, List.zipWith_cons_cons, Function.comp_apply] using
        (congrArg (List.cons _) ih)

end Clause

/-- The same physical unary validity predicate is valid for LE packing,
because both encodings have the identical initial-segment range. -/
theorem unary_answer_eq_table {b : Fin D → ℕ}
    (positions : Fin n ≃ ((j : Fin D) × Fin (b j)))
    (capacity : ∀ j, 2 ^ b j ≤ p) (F : SAT.CNF (Fin n))
    (x : Fin D → ZMod p) (j : Fin D) :
    SubexpUnaryRowProgram.answer (b j) (x j).val =
      Factor.evalFactor (SubexpLEFactorSystem.system positions capacity F) (.inl j) x := by
  apply Bool.eq_iff_iff.mpr
  simpa only [SubexpUnaryRowProgram.answer, decide_eq_true_eq] using
    (SubexpLEFactorSystem.unary_iff positions capacity F x j).symm

/-- The actual descending unary row stream matches the LE factor system
without reordering any output bits. -/
theorem unary_getElem_eq_table {b : Fin D → ℕ}
    (positions : Fin n ≃ ((j : Fin D) × Fin (b j)))
    (capacity : ∀ j, 2 ^ b j ≤ p) (F : SAT.CNF (Fin n))
    (x : Fin D → ZMod p) (j : Fin D) (i : ℕ) (hi : i < p)
    (hx : (x j).val = p - 1 - i) :
    (SubexpUnaryFactorTable.table (b j) p)[i]'(by simpa using hi) =
      Factor.evalFactor (SubexpLEFactorSystem.system positions capacity F) (.inl j) x := by
  rw [SubexpUnaryTableCorrectness.table_getElem (b j) p i hi, ← hx]
  exact unary_answer_eq_table positions capacity F x j

end SubexponentialSAT.SubexpRankedTable

end OAI.Algorithms
