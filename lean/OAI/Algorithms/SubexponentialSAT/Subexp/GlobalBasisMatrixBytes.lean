import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisRefinement
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalDescriptorOrder
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisValidity
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisProgramExecution
import OAI.Algorithms.SubexponentialSAT.SubexpNodeBankMapCallback

namespace OAI.Algorithms

/-!
# The global basis bundle is the matrix-image mapper's exact input

All list equalities retain the actual ambient row order and the generated
column order. The outer matrix is followed by one inner matrix for each
ascending color. No permutation of matrices or scalar bytes is assumed.
-/

namespace SubexponentialSAT.Subexp.GlobalBasisMatrixBytes

open MulticolorTypes GlobalBasisInput GlobalBasis GlobalBasisDescriptors
open GlobalBasisRefinement ConstructivePacking BlockSearch
open GlobalBasisColumns (Descriptor)

private theorem words_map {A : Type*} (xs : List A) (f : A → List Bool) :
    MatrixProgramSupport.words (xs.map f) = xs.flatMap (fun x => Encoding.frame (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [MatrixProgramSupport.words, ih]

private theorem words_flatten (xs : List (List (List Bool))) :
    MatrixProgramSupport.words xs.flatten = xs.flatMap MatrixProgramSupport.words := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [MatrixProgramSupport.words_append, ih]

theorem matrixBits_of_entries {p r Q Δ D : ℕ} [Fact p.Prime]
    (C : Context p r Q Δ) (loc : Fin D → Location r Q Δ)
    {J : Type*} [DecidableEq J] (columns : FiniteEnumeration J)
    (descriptor : J → Descriptor)
    (M : Fin D → Fin columns.values.length → ZMod p)
    (hentry : ∀ v j,
      GlobalBasisEntry.value (C.row (loc v)) (descriptor (columns.equivFin j)) = M v j) :
    GlobalBasisProgram.matrixBits C (List.ofFn loc) (columns.values.map descriptor) =
      BlockCoefficientProgram.matrixBits p M := by
  have hc : columns.values = (List.finRange columns.values.length).map columns.equivFin := by
    rw [← List.ofFn_eq_map]
    exact (List.ofFn_get columns.values).symm
  have hd : columns.values.map descriptor = (List.finRange columns.values.length).map
      (fun j => descriptor (columns.equivFin j)) := by
    simpa only [List.map_map, Function.comp_def] using congrArg (List.map descriptor) hc
  rw [hd]
  simp only [GlobalBasisProgram.matrixBits, GlobalBasisRows.rowBits,
    BlockCoefficientProgram.matrixBits, BlockCoefficientProgram.matrixRows,
    words_flatten, List.ofFn_eq_map, List.flatMap_map]
  apply List.flatMap_congr
  intro v _
  simp only [BlockCoefficientProgram.vectorWords, List.ofFn_eq_map, words_map,
    GlobalBasisEntry.entryFrame, GlobalBasisEntry.scalarFrame]
  apply List.flatMap_congr
  intro j _
  rw [hentry]

variable {p r Q Δ D : ℕ} [Fact p.Prime]
variable (C : Context p r Q Δ) (hr : 0 < r) (hQ : 0 < Q)
variable (hsplit : ∀ g, (C.tables g).split ≤ (C.tables g).dimension)
variable {m : Fin r → ℕ}
variable (constraint : ∀ g, Fin (m g) → Fin (C.tables g).dimension → ZMod p)
variable (good : ∀ g, GoodPair (constraint g) (pairs C hsplit g))
variable (alphabet : List (ZMod p)) (complete : ∀ x, x ∈ alphabet)
variable (P : PackingData (Fin D) (UniversalType r Q Δ))

noncomputable def outerImage : SubexpNodeBankMap.Matrix p D where
  columns := (outerList (b := P.blockCount) (l := P.leftovers.length) (pairs C hsplit)).length
  entries := outerMatrix (fun x : UniversalType r Q Δ => x.head C.position)
    (sideIndex C hr hQ) constraint (pairs C hsplit) good alphabet complete
    P.completeBlocks.embed P.leftoverEquiv

noncomputable def innerImage (g : Fin r) : SubexpNodeBankMap.Matrix p D where
  columns := (innerList (b := P.blockCount) (pairs C hsplit) g).length
  entries := innerMatrix (fun x : UniversalType r Q Δ => x.head C.position)
    (sideIndex C hr hQ) constraint (pairs C hsplit) good alphabet complete
    P.completeBlocks.embed P.leftoverEquiv g

theorem outerColumns_eq :
    GlobalBasisProgram.outerColumnsList C P.blockCount P.leftovers.length =
      (outerList (b := P.blockCount) (l := P.leftovers.length) (pairs C hsplit)).map
        (outerDescriptor (pairs C hsplit)) := by
  apply (GlobalDescriptorOrder.outerDescriptors_eq (pairs C hsplit)
    (fun g => (C.tables g).data) (fun _ => rfl) ?_).symm
  intro g
  exact (BlockSearchEncoding.splitPair_dimensions_add _ _).symm

omit [Fact p.Prime] in
theorem innerColumns_eq (g : Fin r) :
    GlobalBasisProgram.innerColumns C P.blockCount g =
      (innerList (b := P.blockCount) (pairs C hsplit) g).map
        (innerDescriptor (pairs C hsplit) g) :=
  (GlobalDescriptorOrder.innerDescriptors_eq (pairs C hsplit) g).symm

theorem outer_matrixBits :
    GlobalBasisProgram.matrixBits C (List.ofFn (packingLocation P))
        (GlobalBasisProgram.outerColumnsList C P.blockCount P.leftovers.length) =
      BlockCoefficientProgram.matrixBits p
        (outerImage C hr hQ hsplit constraint good alphabet complete P).entries := by
  rw [outerColumns_eq C hsplit P]
  apply matrixBits_of_entries C (packingLocation P)
    (outerEnumeration (b := P.blockCount) (l := P.leftovers.length) (pairs C hsplit))
    (outerDescriptor (pairs C hsplit))
  intro v j
  exact packingLocation_value C hr hQ hsplit constraint good alphabet complete P v
    (.inl ((outerEnumeration (pairs C hsplit)).equivFin j))

theorem inner_matrixBits (g : Fin r) :
    GlobalBasisProgram.matrixBits C (List.ofFn (packingLocation P))
        (GlobalBasisProgram.innerColumns C P.blockCount g) =
      BlockCoefficientProgram.matrixBits p
        (innerImage C hr hQ hsplit constraint good alphabet complete P g).entries := by
  rw [innerColumns_eq C hsplit P g]
  apply matrixBits_of_entries C (packingLocation P)
    (innerEnumeration (b := P.blockCount) (pairs C hsplit) g)
    (innerDescriptor (pairs C hsplit) g)
  intro v j
  exact packingLocation_value C hr hQ hsplit constraint good alphabet complete P v
    (.inr ⟨g, (innerEnumeration (pairs C hsplit) g).equivFin j⟩)

theorem outer_payload :
    GlobalBasisMatrixOutput.payload
        (List.replicate (GlobalBasisProgram.outerColumnsList C P.blockCount P.leftovers.length).length true)
        (GlobalBasisProgram.matrixBits C (List.ofFn (packingLocation P))
          (GlobalBasisProgram.outerColumnsList C P.blockCount P.leftovers.length)) =
      SubexpNodeBankMap.payload (outerImage C hr hQ hsplit constraint good alphabet complete P) := by
  have hl : (GlobalBasisProgram.outerColumnsList C P.blockCount P.leftovers.length).length =
      (outerImage C hr hQ hsplit constraint good alphabet complete P).columns := by
    rw [outerColumns_eq C hsplit P, List.length_map]
    rfl
  rw [outer_matrixBits C hr hQ hsplit constraint good alphabet complete P, hl]
  rfl

theorem inner_payload (g : Fin r) :
    GlobalBasisProgram.innerPayloadAt C P.blockCount (List.ofFn (packingLocation P)) g.val =
      SubexpNodeBankMap.payload (innerImage C hr hQ hsplit constraint good alphabet complete P g) := by
  have hl : (GlobalBasisProgram.innerColumns C P.blockCount g).length =
      (innerImage C hr hQ hsplit constraint good alphabet complete P g).columns := by
    rw [innerColumns_eq C hsplit P g, List.length_map]
    rfl
  simp only [GlobalBasisProgram.innerPayloadAt, dite_eq_left g.isLt]
  rw [inner_matrixBits C hr hQ hsplit constraint good alphabet complete P, hl]
  rfl

/-- A proof-facing typed view of the literal outer-then-colors bundle. -/
noncomputable def images : List (SubexpNodeBankMap.Matrix p D) :=
  outerImage C hr hQ hsplit constraint good alphabet complete P ::
    List.ofFn (innerImage C hr hQ hsplit constraint good alphabet complete P)

theorem bundlePayloads_eq :
    GlobalBasisProgram.bundlePayloads C P.blockCount P.leftovers.length
        (List.ofFn (packingLocation P)) =
      (images C hr hQ hsplit constraint good alphabet complete P).map SubexpNodeBankMap.payload := by
  simp only [GlobalBasisProgram.bundlePayloads, images, List.map_cons]
  rw [outer_payload C hr hQ hsplit constraint good alphabet complete P]
  apply congrArg (List.cons
    (SubexpNodeBankMap.payload (outerImage C hr hQ hsplit constraint good alphabet complete P)))
  rw [← GlobalDescriptorOrder.map_finRange_val r
    (GlobalBasisProgram.innerPayloadAt C P.blockCount (List.ofFn (packingLocation P)))]
  simp only [List.ofFn_eq_map, List.map_map, Function.comp_def]
  apply congrArg (fun f => (List.finRange r).map f)
  funext g
  simpa only [List.ofFn_eq_map] using
    inner_payload C hr hQ hsplit constraint good alphabet complete P g

theorem bundleBits_eq :
    GlobalBasisProgram.bundleBits C P.blockCount P.leftovers.length
        (List.ofFn (packingLocation P)) =
      ProgramEncoding.encodeRecords
        ((images C hr hQ hsplit constraint good alphabet complete P).map SubexpNodeBankMap.payload) := by
  rw [GlobalBasisProgram.bundleBits_eq_records,
    bundlePayloads_eq C hr hQ hsplit constraint good alphabet complete P]

/-- The bank mapper's output nesting agrees with the layout's per-matrix
bank lists; each individual list retains its physical tuple order. -/
theorem bankLists_eq :
    (images C hr hQ hsplit constraint good alphabet complete P).map SubexpNodeBankMap.bankList =
      ProgramEncoding.encodeRecords
          (MatrixImageEnumeration.bankRecords p
            (outerImage C hr hQ hsplit constraint good alphabet complete P).entries) ::
        List.ofFn (fun g => ProgramEncoding.encodeRecords
          (MatrixImageEnumeration.bankRecords p
            (innerImage C hr hQ hsplit constraint good alphabet complete P g).entries)) := by
  simp only [images, List.map_cons, List.map_ofFn, SubexpNodeBankMap.bankList]
  rfl

/-- The actual fixed program emits these exact matrix-image inputs. Its
reader bounds and all row locations follow from the recorded local splits
and executable packing metadata, rather than additional correctness
premises on the global matrix. -/
theorem program_runsIn_images
    (before : List (List Bool)) (tail : List Bool) (d : GlobalBasisProgram.Data)
    (H : GlobalBasisProgram.Inputs C P.blockCount P.leftovers.length
      (List.ofFn (packingLocation P)) before tail d)
    (hmeta : C.metadata = PackingMetadata.records P
      (fun v => PackingMetadata.unary v.val) CollisionProgram.encodeType) :
    ∃ e : GlobalBasisProgram.Data,
      BitProgram.RunsIn GlobalBasisProgram.program
        (GlobalBasisProgram.totalBudget C P.blockCount P.leftovers.length
          (List.ofFn (packingLocation P)) (d.stacks 47).length + 1)
        (d.withPC (some GlobalBasisProgram.program.entry)) (e.withPC none) ∧
      e.stacks = Function.update d.stacks 63
        (ProgramEncoding.encodeRecords
          ((images C hr hQ hsplit constraint good alphabet complete P).map
            SubexpNodeBankMap.payload)) := by
  obtain ⟨e, he, hs⟩ := GlobalBasisProgram.program_runsIn_records C P.blockCount
    P.leftovers.length (List.ofFn (packingLocation P)) before tail d H
    (packing_locations C P hmeta)
    (fun g loc _ x hx => GlobalBasisValidity.innerDescriptors_valid C loc P.blockCount g
      (hsplit g) x hx)
    (fun loc _ x hx => GlobalBasisValidity.outerDescriptors_valid C loc P.blockCount
      P.leftovers.length x hx)
  refine ⟨e, he, ?_⟩
  rw [bundlePayloads_eq C hr hQ hsplit constraint good alphabet complete P] at hs
  exact hs

end SubexponentialSAT.Subexp.GlobalBasisMatrixBytes

end OAI.Algorithms
