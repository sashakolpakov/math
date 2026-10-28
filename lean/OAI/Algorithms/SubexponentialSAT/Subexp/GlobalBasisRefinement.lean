import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisInput
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisDescriptors
import OAI.Algorithms.SubexponentialSAT.Subexp.TypeByteIndex
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingMetadata

namespace OAI.Algorithms

/-!
# Actual local tables and packing locations denote the global basis

The physical table uses the byte-list order of each side. Splitting that
same table at its recorded rank gives the local pair used by the global
linear-algebra construction. The proofs below identify every covered and
leftover entry, including the original ambient row order.
-/

namespace SubexponentialSAT.Subexp.GlobalBasisRefinement

open MulticolorTypes GlobalBasisInput BlockSearch BlockSearchEncoding
open GlobalBasis GlobalBasisDescriptors LocalEnumeration ComputablePackingSplit
open ConstructivePacking

variable {p r Q Δ : ℕ} [Fact p.Prime]
variable (C : Context p r Q Δ) (hr : 0 < r) (hQ : 0 < Q)

/-- This is the exact side order read by the physical row preparation. -/
noncomputable def sideIndex (g : Fin r) :
    Fin (C.tables g).dimension ≃ Side (Δ := Δ) C.position g :=
  (finCongr (C.dimensions g)).trans (TypeByteIndex.sideByteEquiv hr hQ C.position g)

omit [Fact p.Prime] in
theorem sideIndex_symm_val (g : Fin r) (u : Side (Δ := Δ) C.position g) :
    ((sideIndex C hr hQ g).symm u).val =
      (TypeEnumeration.sideBytes r Q Δ C.position.val g.val).idxOf
        (CollisionProgram.encodeType u.val) := by
  change ((TypeByteIndex.sideByteEquiv hr hQ C.position g).symm u).val = _
  exact TypeByteIndex.sideByteEquiv_symm_val hr hQ C.position g u

variable (hsplit : ∀ g, (C.tables g).split ≤ (C.tables g).dimension)

/-- The candidate is the actual square table split at the emitted rank. -/
def pairs (g : Fin r) :
    Candidate (ZMod p) (C.tables g).dimension ×
      Candidate (ZMod p) (C.tables g).dimension :=
  splitPair ⟨(C.tables g).split, Nat.lt_succ_of_le (hsplit g)⟩ (C.tables g).table

omit [Fact p.Prime] in
theorem tableOfPair_pairs (g : Fin r)
    (h : (pairs C hsplit g).1.1.val + (pairs C hsplit g).2.1.val =
      (C.tables g).dimension) :
    tableOfPair (pairs C hsplit g) h = (C.tables g).table :=
  tableOfPair_splitPair _ _

variable {m : Fin r → ℕ}
variable (constraint : ∀ g, Fin (m g) → Fin (C.tables g).dimension → ZMod p)
variable (good : ∀ g, GoodPair (constraint g) (pairs C hsplit g))

/-- The index computed by byte lookup is precisely the coordinate read
by the explicit global synthesis. The local table itself is unchanged. -/
theorem row_covered_eq {b : ℕ} (block : Fin b) (u : UniversalType r Q Δ) :
    C.row (.covered block.val u) =
      coveredRow (fun x : UniversalType r Q Δ => x.head C.position)
        (sideIndex C hr hQ) constraint (pairs C hsplit) good block u := by
  dsimp only [Context.row, GlobalBasisCoveredRow.row, coveredRow]
  rw [tableOfPair_pairs C hsplit]
  congr 1
  exact (sideIndex_symm_val C hr hQ (u.head C.position) ⟨u, rfl⟩).symm

omit [Fact p.Prime] in
theorem row_leftover_eq {l : ℕ} (j : Fin l) :
    C.row (.leftover j.val) = GlobalBasisDescriptors.leftoverRow (p := p) j := by
  simp only [Context.row, GlobalBasisRowPrepare.leftoverRow,
    GlobalBasisDescriptors.leftoverRow]
  congr 1
  funext i
  exact Fin.elim0 i

variable {V : Type*} [DecidableEq V] {b l : ℕ}
variable (alphabet : List (ZMod p)) (complete : ∀ x, x ∈ alphabet)
variable (packing : Fin b × UniversalType r Q Δ ↪ V)
variable (leftovers : Fin l ≃ Leftover packing)

theorem covered_value (block : Fin b) (u : UniversalType r Q Δ)
    (column : Column (b := b) (l := l) (pairs C hsplit)) :
    GlobalBasisEntry.value (C.row (.covered block.val u))
        (columnDescriptor (pairs C hsplit) column) =
      matrix (fun x : UniversalType r Q Δ => x.head C.position)
        (sideIndex C hr hQ) constraint (pairs C hsplit) good
        alphabet complete packing leftovers (packing (block, u)) column := by
  rw [row_covered_eq C hr hQ hsplit constraint good]
  exact coveredRow_value _ _ _ _ _ _ _ _ _ _ _ _

theorem leftover_value (j : Fin l)
    (column : Column (b := b) (l := l) (pairs C hsplit)) :
    GlobalBasisEntry.value (C.row (.leftover j.val))
        (columnDescriptor (pairs C hsplit) column) =
      matrix (fun x : UniversalType r Q Δ => x.head C.position)
        (sideIndex C hr hQ) constraint (pairs C hsplit) good
        alphabet complete packing leftovers (leftovers j).val column := by
  rw [row_leftover_eq C]
  exact leftoverRow_value _ _ _ _ _ _ _ _ _ _ _

section Packing

variable {D : ℕ} (P : PackingData (Fin D) (UniversalType r Q Δ))

/-- Each row's location comes from the actual executable packing inverse.
The leftover rank is its original-order list index. -/
def packingLocation (v : Fin D) : Location r Q Δ :=
  match P.lookup v with
  | some z => .covered z.1.val z.2
  | none => .leftover (P.leftovers.idxOf v)

theorem packingLocation_metadata (v : Fin D) :
    (packingLocation P v).metadata = PackingMetadata.value P CollisionProgram.encodeType v := by
  cases h : P.lookup v <;> simp [packingLocation, PackingMetadata.value, h,
    Location.metadata, PackingMetadata.unary]

omit [Fact p.Prime] in
theorem packing_matches
    (hmeta : C.metadata = PackingMetadata.records P
      (fun v => PackingMetadata.unary v.val) CollisionProgram.encodeType)
    (v : Fin D) : C.matches v.val (packingLocation P v) := by
  change C.metadata.lookup (PackingMetadata.unary v.val) = _
  rw [hmeta]
  simpa only [packingLocation_metadata] using
    PackingMetadata.lookup_eq P (fun v : Fin D => PackingMetadata.unary v.val)
      CollisionProgram.encodeType
      (by intro a b h; exact Fin.ext (PackingMetadata.unary_injective h)) v

omit [Fact p.Prime] in
private theorem locations_of_get (start : ℕ) (locs : List (Location r Q Δ))
    (h : ∀ i : Fin locs.length, C.matches (start + i.val) (locs.get i)) :
    C.locations start locs := by
  induction locs generalizing start with
  | nil => trivial
  | cons loc locs ih =>
    refine ⟨?_, ih (start + 1) ?_⟩
    · simpa using h ⟨0, by simp⟩
    · intro i
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        h ⟨i.val + 1, by
          change i.val + 1 < locs.length + 1
          exact Nat.add_lt_add_right i.isLt 1⟩

omit [Fact p.Prime] in
/-- No row-location oracle is needed: the concrete metadata table supplies
all locations in the ambient `Fin D` order used by the matrix loop. -/
theorem packing_locations
    (hmeta : C.metadata = PackingMetadata.records P
      (fun v => PackingMetadata.unary v.val) CollisionProgram.encodeType) :
    C.locations 0 (List.ofFn (packingLocation P)) := by
  apply locations_of_get C
  intro i
  simpa using packing_matches C P hmeta ⟨i.val, by simpa using i.isLt⟩

theorem packingLocation_value (v : Fin D)
    (column : Column (b := P.blockCount) (l := P.leftovers.length) (pairs C hsplit)) :
    GlobalBasisEntry.value (C.row (packingLocation P v))
        (columnDescriptor (pairs C hsplit) column) =
      matrix (fun x : UniversalType r Q Δ => x.head C.position)
        (sideIndex C hr hQ) constraint (pairs C hsplit) good
        alphabet complete P.completeBlocks.embed P.leftoverEquiv v column := by
  cases hv : P.lookup v with
  | some z =>
    obtain ⟨block, u⟩ := z
    have he := (P.lookup_some_iff v (block, u)).mp hv
    simpa only [packingLocation, hv, he] using
      covered_value C hr hQ hsplit constraint good alphabet complete
        P.completeBlocks.embed P.leftoverEquiv block u column
  | none =>
    let z : Leftover P.completeBlocks.embed := ⟨v, (P.lookup_none_iff v).mp hv⟩
    let j := P.leftoverEquiv.symm z
    have hj : j.val = P.leftovers.idxOf v := rfl
    have he : (P.leftoverEquiv j).val = v :=
      congrArg Subtype.val (P.leftoverEquiv.apply_symm_apply z)
    simpa only [packingLocation, hv, hj, he] using
      leftover_value C hr hQ hsplit constraint good alphabet complete
        P.completeBlocks.embed P.leftoverEquiv j column

end Packing

end SubexponentialSAT.Subexp.GlobalBasisRefinement

end OAI.Algorithms
