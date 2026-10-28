import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInputAddressed
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramProducedRankLiteral
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingMetadata

namespace OAI.Algorithms

/-! Changing only the displayed incidence-list length transports the same
packing; numeric positions, labels, metadata bytes, and matrix values agree. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput
open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes

variable {D E : ℕ} {U : Type*}

def reindexPacking (h : D = E) (P : PackingData (Fin D) U) : PackingData (Fin E) U := h ▸ P

@[simp] theorem reindexPacking_rfl (P : PackingData (Fin D) U) : reindexPacking rfl P = P := rfl

@[simp] theorem reindexPacking_label (h : D = E) (P : PackingData (Fin D) U) (i : Fin E) :
    (reindexPacking h P).label i = P.label (Fin.cast h.symm i) := by
  cases h
  rfl

@[simp] theorem reindexPacking_label_cast (h : D = E) (P : PackingData (Fin D) U) (i : Fin D) :
    (reindexPacking h P).label (Fin.cast h i) = P.label i := by
  cases h
  rfl

@[simp] theorem reindexPacking_types (h : D = E) (P : PackingData (Fin D) U) :
    (reindexPacking h P).types = P.types := by
  cases h
  rfl

theorem reindexPacking_vertices (h : D = E) (P : PackingData (Fin D) U) :
    (reindexPacking h P).vertices.values = P.vertices.values.map (Fin.cast h) := by
  cases h
  simp [reindexPacking]

@[simp] theorem reindexPacking_blockCount [DecidableEq U] (h : D = E)
    (P : PackingData (Fin D) U) : (reindexPacking h P).blockCount = P.blockCount := by
  cases h
  rfl

@[simp] theorem reindexPacking_metadataValue [DecidableEq U] (h : D = E)
    (P : PackingData (Fin D) U) (encodeType : U → List Bool) (i : Fin E) :
    PackingMetadata.value (reindexPacking h P) encodeType i =
      PackingMetadata.value P encodeType (Fin.cast h.symm i) := by
  cases h
  rfl

@[simp] theorem reindexPacking_metadataRecords [DecidableEq U] (h : D = E)
    (P : PackingData (Fin D) U) (encodeType : U → List Bool) :
    PackingMetadata.records (reindexPacking h P) (fun v => List.replicate v.val true) encodeType =
      PackingMetadata.records P (fun v => List.replicate v.val true) encodeType := by
  cases h
  rfl

@[simp] theorem reindexPacking_metadataBytes [DecidableEq U] (h : D = E)
    (P : PackingData (Fin D) U) (encodeType : U → List Bool) :
    SelectorProgram.rawRecords (PackingMetadata.records (reindexPacking h P)
      (fun v => List.replicate v.val true) encodeType) =
    SelectorProgram.rawRecords (PackingMetadata.records P
      (fun v => List.replicate v.val true) encodeType) := by
  rw [reindexPacking_metadataRecords]

variable {r Q : ℕ}

@[simp] theorem reindexPacking_localEntry (h : D = E)
    (P : PackingData (Fin D) (UniversalType r Q 1)) (A R : ℕ) (t : Fin Q) (i j : Fin E) :
    LayoutProgram.localEntry (reindexPacking h P) A R t i j =
      LayoutProgram.localEntry P A R t (Fin.cast h.symm i) (Fin.cast h.symm j) := by
  cases h
  rfl

@[simp] theorem reindexPacking_entryNat (h : D = E)
    (P : PackingData (Fin D) (UniversalType r Q 1)) (A R : ℕ) (t : Fin Q) (i j : ℕ) :
    BucketProgram.ProducedRank.entryNat (reindexPacking h P) A R t i j =
      BucketProgram.ProducedRank.entryNat P A R t i j := by
  cases h
  rfl

def addressedPacking (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (P : PackingData (Semantics.Incidences scopes mask) U) :
    PackingData (Fin (addressedEntries scopes n mask).length) U :=
  reindexPacking (addressedEntries_length scopes n mask).symm P

@[simp] theorem addressedPacking_label (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (P : PackingData (Semantics.Incidences scopes mask) U)
    (i : Fin (addressedEntries scopes n mask).length) :
    (addressedPacking scopes n mask P).label i = P.label (addressedIndex scopes n mask i) := by
  rw [addressedPacking,reindexPacking_label]
  rfl

@[simp] theorem addressedPacking_entryNat (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (P : PackingData (Semantics.Incidences scopes mask) (UniversalType r Q 1))
    (A R : ℕ) (t : Fin Q) (i j : ℕ) :
    BucketProgram.ProducedRank.entryNat (addressedPacking scopes n mask P) A R t i j =
      BucketProgram.ProducedRank.entryNat P A R t i j := by
  exact reindexPacking_entryNat _ P A R t i j

end SubexponentialSAT.SqrtLog.PackingIncidenceInput

end OAI.Algorithms
