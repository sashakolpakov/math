import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisRowExecution
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisComplementColumns

namespace OAI.Algorithms

/-!
Byte-level input relations for the fixed global matrix assembler. Local
tables and packing metadata are the outputs of upstream physical programs.
The relations below name their contents; they do not supply a global matrix,
a read plan, an entry oracle, or an execution certificate.
-/

namespace SubexponentialSAT.Subexp.GlobalBasisInput

open BitProgram StructuredCalls

structure LocalTable (p : ℕ) where
  dimension : ℕ
  split : ℕ
  table : Fin dimension → Fin dimension → ZMod p

def LocalTable.bits {p : ℕ} [Fact p.Prime] (L : LocalTable p) : List Bool :=
  (BasisTransposeProgram.rows (MatrixWordEncoding.code p) L.table).flatten

def LocalTable.data {p : ℕ} [Fact p.Prime] (L : LocalTable p) : GlobalBasisComplementColumns.LocalData :=
  ⟨L.dimension, L.split, L.bits⟩

inductive Location (r Q Δ : ℕ) where
  | covered (block : ℕ) (type : MulticolorTypes.UniversalType r Q Δ)
  | leftover (rank : ℕ)

def Location.metadata {r Q Δ : ℕ} : Location r Q Δ → GlobalBasisMetadata.Metadata
  | .covered block u => .covered (List.replicate block true) (CollisionProgram.encodeType u)
  | .leftover rank => .leftover (List.replicate rank true)

structure Context (p r Q Δ : ℕ) where
  position : Fin Q
  tables : Fin r → LocalTable p
  metadata : List (List Bool × List Bool)
  dimensions : ∀ g, (tables g).dimension = (TypeEnumeration.sideBytes r Q Δ position.val g.val).length

def Context.data {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ) :=
  List.ofFn (fun g => (C.tables g).data)

def Context.batch {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ) : List Bool :=
  GlobalBasisComplementColumns.encoded C.data

def Context.row {p r Q Δ : ℕ} (C : Context p r Q Δ) : Location r Q Δ → GlobalBasisEntry.Row p
  | .covered block u =>
    let L := C.tables (u.head C.position)
    GlobalBasisCoveredRow.row u C.position block L.dimension L.table
  | .leftover rank => GlobalBasisRowPrepare.leftoverRow p rank

def Context.matches {p r Q Δ : ℕ} (C : Context p r Q Δ) (index : ℕ) (loc : Location r Q Δ) : Prop :=
  C.metadata.lookup (List.replicate index true) = some loc.metadata.encode

def Context.locations {p r Q Δ : ℕ} (C : Context p r Q Δ) : ℕ → List (Location r Q Δ) → Prop
  | _, [] => True
  | index, loc :: rest => C.matches index loc ∧ C.locations (index+1) rest

structure Context.Stored {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ)
    (d : GlobalBasisRowPrepare.Data) : Prop where
  width : d.stacks 13 = List.replicate (GlobalBasisEntry.frameWidth p) true
  zero : d.stacks 14 = GlobalBasisEntry.scalarFrame p 0
  one : d.stacks 15 = GlobalBasisEntry.scalarFrame p 1
  position : d.stacks 32 = List.replicate C.position.val true
  metadata : d.stacks 33 = SelectorProgram.rawRecords C.metadata
  universal : d.stacks 37 = ProgramEncoding.encodeRecords (TypeEnumeration.universalBytes r Q Δ)
  colors : d.stacks 38 = List.replicate r true
  batch : d.stacks 40 = C.batch

theorem encoded_eq (qs : List GlobalBasisComplementColumns.LocalData) :
    GlobalBasisComplementColumns.encoded qs =
      Encoding.encodeList id (qs.map GlobalBasisComplementColumns.LocalData.payload) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simpa only [GlobalBasisComplementColumns.encoded, Encoding.encodeList, List.map_cons, id_eq] using
      (congrArg (fun rest => true :: (Encoding.frame q.payload ++ rest)) ih)

theorem encode_append (before after : List (List Bool)) :
    Encoding.encodeList id (before ++ after) =
      GlobalBasisRecordLookup.recordsPrefix before ++ Encoding.encodeList id after := by
  induction before with
  | nil => rfl
  | cons bits before ih =>
    simp [Encoding.encodeList, GlobalBasisRecordLookup.recordsPrefix,
      GlobalBasisRecordLookup.record, ih, List.append_assoc]

theorem encode_get (words : List (List Bool)) (i : ℕ) (hi : i < words.length) :
    Encoding.encodeList id words =
      GlobalBasisRecordLookup.recordsPrefix (words.take i) ++
        GlobalBasisRecordLookup.record words[i] ++ Encoding.encodeList id (words.drop (i+1)) := by
  have hs := List.take_append_drop i words
  rw [List.drop_eq_getElem_cons hi] at hs
  calc
    Encoding.encodeList id words = Encoding.encodeList id (words.take i ++ words[i] :: words.drop (i+1)) :=
      congrArg (Encoding.encodeList id) hs.symm
    _ = _ := by
      rw [encode_append]
      simp only [Encoding.encodeList, id_eq, GlobalBasisRecordLookup.record,
        List.cons_append, List.append_assoc]

def Context.before {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ) (g : Fin r) : List (List Bool) :=
  (C.data.map GlobalBasisComplementColumns.LocalData.payload).take g.val

def Context.after {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ) (g : Fin r) : List Bool :=
  Encoding.encodeList id ((C.data.map GlobalBasisComplementColumns.LocalData.payload).drop (g.val+1))

theorem Context.before_length {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ) (g : Fin r) :
    (C.before g).length = g.val := by
  simp [Context.before, Context.data]

theorem Context.batch_split {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ) (g : Fin r) :
    C.batch = GlobalBasisRecordLookup.recordsPrefix (C.before g) ++
      GlobalBasisRecordLookup.record (SubexpLocalBatchParse.payload
        (C.tables g).dimension (C.tables g).split (C.tables g).bits) ++ C.after g := by
  have hi : g.val < (C.data.map GlobalBasisComplementColumns.LocalData.payload).length := by
    simp [Context.data]
  have h := encode_get (C.data.map GlobalBasisComplementColumns.LocalData.payload) g.val hi
  simpa [Context.batch, encoded_eq, Context.before, Context.after, Context.data,
    LocalTable.data, GlobalBasisComplementColumns.LocalData.payload] using h

def Context.setupBudget {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ)
    (index : ℕ) : Location r Q Δ → ℕ
  | .covered _ u =>
      GlobalBasisRowPrepare.coveredBudget u C.position (C.tables (u.head C.position)).dimension
        (C.tables (u.head C.position)).split C.metadata (List.replicate index true) C.batch + 1
  | .leftover _ => 400 * (GlobalBasisMetadata.volume C.metadata (List.replicate index true))^2 + 5

/-- Every row is obtained by running the same fixed preparation program.
The case distinction here follows the bytes found in the packing table. -/
theorem Context.prepare {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ)
    (index : ℕ) (loc : Location r Q Δ) (d : GlobalBasisRowPrepare.Data)
    (hm : C.matches index loc) (hs : C.Stored d)
    (hi : d.stacks 34 = List.replicate index true) (hc : GlobalBasisRowPrepare.RowClean d) :
    ∃ e : GlobalBasisRowPrepare.Data,
      RunsIn GlobalBasisRowPrepare.program (C.setupBudget index loc)
        (d.withPC (some GlobalBasisRowPrepare.program.entry)) (e.withPC none) ∧
      e.stacks = GlobalBasisRowPrepare.rowStacks (C.row loc) d.stacks ∧
      GlobalBasisCoveredRow.RowReady (C.row loc) e := by
  cases loc with
  | leftover rank =>
    exact GlobalBasisRowPrepare.leftover_program_runsIn C.metadata (List.replicate index true) rank d
      hm hs.metadata hi hc hs.width hs.zero hs.one
  | covered block u =>
    simpa only [Context.setupBudget, Context.row, hs.batch, LocalTable.bits] using
      GlobalBasisRowPrepare.covered_program_runsIn u C.position C.metadata (List.replicate index true)
        (C.before (u.head C.position)) (C.tables (u.head C.position)).dimension
        (C.tables (u.head C.position)).split block (C.tables (u.head C.position)).table
        (C.after (u.head C.position)) d hm hs.metadata hi hc hs.position hs.universal hs.colors
        (hs.batch.trans (C.batch_split (u.head C.position)))
        (C.before_length (u.head C.position)) hs.width hs.zero hs.one
        (C.dimensions (u.head C.position))

end SubexponentialSAT.Subexp.GlobalBasisInput

end OAI.Algorithms
