import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchColor
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisRefinement
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalKernel
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientNormalization

namespace OAI.Algorithms

/-!
# Interpreting the actual local-search batch

The batch returns successful square tables in ascending node/color order.
These proofs give those same records the types used by the global matrix
assembler and the layout. The witnesses are interpretations of emitted
bytes, not a second search or a choice of replacement bases.
-/

namespace SubexponentialSAT.Subexp.LocalBasisBatchRefinement

open MulticolorTypes BlockSearch BlockSearchEncoding

/-- One successful result, retaining the physical side-coordinate order. -/
structure Result (p : ℕ) [Fact p.Prime] {r Q Δ : ℕ}
    (hr : 0 < r) (hQ : 0 < Q) (coefficients : List (ZMod p))
    (t : Fin Q) (g : Fin r) where
  table : Fin (TypeEnumeration.sideList (Δ := Δ) hr hQ t g).length →
    Fin (TypeEnumeration.sideList (Δ := Δ) hr hQ t g).length → ZMod p
  split : Fin ((TypeEnumeration.sideList (Δ := Δ) hr hQ t g).length + 1)
  good : GoodPair (ConstraintMatrixProgram.matrix (Δ := Δ) p hr hQ t g coefficients)
    (splitPair split table)

variable {p r Q Δ : ℕ} [Fact p.Prime]
variable {hr : 0 < r} {hQ : 0 < Q} {coefficients : List (ZMod p)}

noncomputable def Result.payload {t : Fin Q} {g : Fin r}
    (result : Result (Δ := Δ) p hr hQ coefficients t g) : List Bool :=
  LocalBasisBatchProgram.resultPayload
    (List.replicate (TypeEnumeration.sideList (Δ := Δ) hr hQ t g).length true)
    (List.replicate result.split.val true) (BlockCoefficientProgram.tableBits p result.table)

theorem result_of_good {t : Fin Q} {g : Fin r} {payload : List Bool}
    (h : LocalBasisBatchProgram.GoodResult (Δ := Δ) p hr hQ coefficients
      t.val g.val payload) :
    ∃ result : Result (Δ := Δ) p hr hQ coefficients t g, result.payload = payload := by
  obtain ⟨ht, hg, table, split, good, hbytes⟩ := h
  exact ⟨⟨table, split, good⟩, hbytes.symm⟩

private theorem of_forall₂_range {B : Type*} {N : ℕ} {P : ℕ → B → Prop}
    {xs : List B} (h : List.Forall₂ P (List.range N) xs) :
    ∃ f : Fin N → B, xs = List.ofFn f ∧ ∀ i, P i.val (f i) := by
  have hlength : N = xs.length := by simpa only [List.length_range] using h.length_eq
  subst N
  refine ⟨xs.get, (List.ofFn_get xs).symm, ?_⟩
  intro i
  simpa using h.get (by simpa only [List.length_range] using i.isLt) i.isLt

/-- The two nested output lists are exactly the stored tables in their
node/color order, with no permutation or agreement with another search. -/
theorem exists_results {rows : List (List (List Bool))}
    (h : LocalBasisBatchProgram.RowsGood
      (LocalBasisBatchProgram.GoodResult (Δ := Δ) p hr hQ coefficients) r Q rows) :
    ∃ results : (t : Fin Q) → (g : Fin r) → Result (Δ := Δ) p hr hQ coefficients t g,
      rows = List.ofFn (fun t => List.ofFn (fun g => (results t g).payload)) := by
  obtain ⟨atNode, hrows, hnode⟩ := of_forall₂_range h
  have hex : ∀ t : Fin Q,
      ∃ results : (g : Fin r) → Result (Δ := Δ) p hr hQ coefficients t g,
        atNode t = List.ofFn (fun g => (results g).payload) := by
    intro t
    obtain ⟨payload, hpayload, hgood⟩ := of_forall₂_range (hnode t)
    have hresultExists : ∀ g : Fin r,
        ∃ result : Result (Δ := Δ) p hr hQ coefficients t g,
          result.payload = payload g := fun g => result_of_good (hgood g)
    choose results hresult using hresultExists
    refine ⟨results, hpayload.trans ?_⟩
    apply congrArg List.ofFn
    funext g
    exact (hresult g).symm
  choose results hresult using hex
  refine ⟨results, hrows.trans ?_⟩
  apply congrArg List.ofFn
  funext t
  exact hresult t

noncomputable def Result.localTable {t : Fin Q} {g : Fin r}
    (result : Result (Δ := Δ) p hr hQ coefficients t g) : GlobalBasisInput.LocalTable p where
  dimension := (TypeEnumeration.sideList (Δ := Δ) hr hQ t g).length
  split := result.split.val
  table := result.table

theorem Result.localTable_bits {t : Fin Q} {g : Fin r}
    (result : Result (Δ := Δ) p hr hQ coefficients t g) :
    result.localTable.bits = BlockCoefficientProgram.tableBits p result.table := by
  rw [GlobalBasisInput.LocalTable.bits, Result.localTable, BasisTransposeProgram.rows_flatten]
  change SubexpTupleRefinement.encodeTuple (BlockSearchPredicate.scalarCode p)
    (flattenTable result.table) = _
  exact BlockSearchConcrete.tableBits_eq p result.table

theorem Result.localTable_payload {t : Fin Q} {g : Fin r}
    (result : Result (Δ := Δ) p hr hQ coefficients t g) :
    result.localTable.data.payload = result.payload := by
  unfold GlobalBasisInput.LocalTable.data GlobalBasisComplementColumns.LocalData.payload
  rw [Result.localTable_bits]
  simp only [SubexpLocalBatchParse.payload, SubexpLocalBatchParse.unary,
    Result.localTable, Result.payload, LocalBasisBatchProgram.resultPayload, List.append_assoc]

variable (results : (t : Fin Q) → (g : Fin r) → Result (Δ := Δ) p hr hQ coefficients t g)

/-- Interpret the node's original records directly as the assembler input. -/
noncomputable def context (metadata : List (List Bool × List Bool)) (t : Fin Q) :
    GlobalBasisInput.Context p r Q Δ where
  position := t
  tables g := (results t g).localTable
  metadata := metadata
  dimensions g := (TypeByteIndex.side_length hr hQ t g).symm

theorem context_split_le (metadata : List (List Bool × List Bool)) (t : Fin Q) (g : Fin r) :
    ((context results metadata t).tables g).split ≤
      ((context results metadata t).tables g).dimension :=
  Nat.le_of_lt_succ (results t g).split.isLt

theorem context_batch (metadata : List (List Bool × List Bool)) (t : Fin Q) :
    (context results metadata t).batch =
      ProgramEncoding.encodeRecords (List.ofFn fun g => (results t g).payload) := by
  rw [GlobalBasisInput.Context.batch, GlobalBasisInput.encoded_eq]
  simp only [GlobalBasisInput.Context.data, context, List.map_ofFn, Function.comp_def,
    Result.localTable_payload]

theorem batch_bytes {rows : List (List (List Bool))}
    (hrows : rows = List.ofFn (fun t => List.ofFn fun g => (results t g).payload))
    (metadata : List (List Bool × List Bool)) :
    ProgramEncoding.encodeRecords (rows.map ProgramEncoding.encodeRecords) =
      ProgramEncoding.encodeRecords (List.ofFn fun t => (context results metadata t).batch) := by
  rw [hrows, List.map_ofFn]
  apply congrArg ProgramEncoding.encodeRecords
  apply congrArg List.ofFn
  funext t
  exact (context_batch results metadata t).symm

theorem context_sideIndex (metadata : List (List Bool × List Bool)) (t : Fin Q) (g : Fin r) :
    GlobalBasisRefinement.sideIndex (context results metadata t) hr hQ g =
      TypeEnumeration.sideEquiv hr hQ t g := by
  apply Equiv.ext
  intro i
  rfl

theorem context_pairs (metadata : List (List Bool × List Bool)) (t : Fin Q) (g : Fin r) :
    GlobalBasisRefinement.pairs (context results metadata t)
        (context_split_le results metadata t) g =
      splitPair (results t g).split (results t g).table := rfl

theorem context_good (metadata : List (List Bool × List Bool)) (t : Fin Q) (g : Fin r) :
    GoodPair (ConstraintMatrixProgram.matrix (Δ := Δ) p hr hQ t g coefficients)
      (GlobalBasisRefinement.pairs (context results metadata t)
        (context_split_le results metadata t) g) :=
  (results t g).good

section Normalization

variable (A R : ℕ)

theorem matrix_eq_normalized (hlength : coefficients.length = R)
    (hcheck : ∀ d : Fin R,
      CoefficientDynamics.evaluate coefficients (A + d.val) = (-1 : ZMod p) ^ (A + d.val))
    (t : Fin Q) (g : Fin r) :
    ConstraintMatrixProgram.matrix (Δ := Δ) p hr hQ t g coefficients =
      SubspaceDimension.encodedConstraintMatrix (side t g) (joint t g)
        (joint_subset_side t g)
        (fun i => (ElementaryMatrix.jointMatrixDP i t g R
          (CoefficientSearch.coefficientsNat p A R)).mulVecLin)
        (ConstraintMatrixProgram.rowEquiv hr hQ t g) (TypeEnumeration.sideEquiv hr hQ t g) := by
  rw [ConstraintMatrixProgram.matrix_eq_constraints]
  have hM : (fun i : Fin Δ => (ElementaryMatrix.jointMatrixDP i t g coefficients.length
      (fun j => coefficients.getD j 0 * (2 : ZMod p)^j)).mulVecLin) =
      (fun i => (ElementaryMatrix.jointMatrixDP i t g R
        (CoefficientSearch.coefficientsNat p A R)).mulVecLin) := by
    funext i
    exact congrArg (fun M : Matrix (Joint t g i) (Joint t g i) (ZMod p) => M.mulVecLin)
      (CoefficientNormalization.jointMatrix_eq i t g A R coefficients hlength hcheck)
  rw [hM]

/-- A successful physical checker result is a good pair for exactly the
layout's fixed-space constraints, in the same actual side order. -/
theorem context_good_normalized (hlength : coefficients.length = R)
    (hcheck : ∀ d : Fin R,
      CoefficientDynamics.evaluate coefficients (A + d.val) = (-1 : ZMod p) ^ (A + d.val))
    (metadata : List (List Bool × List Bool)) (t : Fin Q) (g : Fin r) :
    GoodPair
      (GlobalKernel.universalConstraint t
        (fun g i => (ElementaryMatrix.jointMatrixDP i t g R
          (CoefficientSearch.coefficientsNat p A R)).mulVecLin)
        (ConstraintMatrixProgram.rowEquiv hr hQ t)
        (GlobalBasisRefinement.sideIndex (context results metadata t) hr hQ) g)
      (GlobalBasisRefinement.pairs (context results metadata t)
        (context_split_le results metadata t) g) := by
  unfold GlobalKernel.universalConstraint
  rw [context_sideIndex]
  change GoodPair
    (SubspaceDimension.encodedConstraintMatrix (side t g) (joint t g)
      (joint_subset_side t g)
      (fun i => (ElementaryMatrix.jointMatrixDP i t g R
        (CoefficientSearch.coefficientsNat p A R)).mulVecLin)
      (ConstraintMatrixProgram.rowEquiv hr hQ t g)
      (TypeEnumeration.sideEquiv hr hQ t g))
    (GlobalBasisRefinement.pairs (context results metadata t)
      (context_split_le results metadata t) g)
  rw [← matrix_eq_normalized A R hlength hcheck]
  exact context_good results metadata t g

end Normalization

end SubexponentialSAT.Subexp.LocalBasisBatchRefinement

end OAI.Algorithms
