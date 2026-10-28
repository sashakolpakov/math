import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LagrangePacketBinary
import OAI.Algorithms.SubexponentialSAT.SubexpProgramBuilder
import OAI.Algorithms.SubexponentialSAT.SubexpTableSource

namespace OAI.Algorithms

/-!
# Ordered raw factor packets from the computed incidence data

Rows retain their supplied table order. Coordinates retain the factor's
scope order, while each origin and Taylor column uses increasing ambient
coordinate order. A table label selects the corresponding Lagrange cache
entry. The selection theorem below invokes the actual binary-index packet
program; constructing the origin and Taylor bytes remains the responsibility
of their physical producers.
-/

namespace SubexponentialSAT.Subexp.FactorBlueprint

open LagrangePacketProgram

structure Coordinate where
  origin : List Word
  taylor : List (List Word)
  coefficients : List Word

structure Row where
  value : Word
  coordinates : List Coordinate

def originBytes (c : Coordinate) : Word := Encoding.encodeList id c.origin
def taylorBytes (c : Coordinate) : Word :=
  Encoding.encodeList (Encoding.encodeList id) c.taylor
def coefficientBytes (c : Coordinate) : Word := Encoding.encodeList id c.coefficients

def encodeCoordinate (c : Coordinate) : Word :=
  packet (originBytes c) (taylorBytes c) (coefficientBytes c)

def encodeRow (row : Row) : Word :=
  Encoding.frame row.value ++ Encoding.encodeList encodeCoordinate row.coordinates

def encodeRows (rows : List Row) : Word := Encoding.encodeList encodeRow rows

theorem encodeList_length {A : Type*} (encode : A → Word) (xs : List A) :
    (Encoding.encodeList encode xs).length =
      2 * (xs.map (fun x => (encode x).length)).sum + 2 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [Encoding.length_encodeList_cons, List.map_cons, List.sum_cons,
      List.length_cons, ih]
    omega

theorem encodeCoordinate_length (c : Coordinate) :
    (encodeCoordinate c).length = 4 * (originBytes c).length +
      4 * (taylorBytes c).length + 2 * (coefficientBytes c).length + 6 :=
  packet_length _ _ _

theorem encodeRow_length (row : Row) :
    (encodeRow row).length = 2 * row.value.length +
      2 * (row.coordinates.map (fun c => (encodeCoordinate c).length)).sum +
      2 * row.coordinates.length + 2 := by
  rw [encodeRow, List.length_append, Encoding.length_frame, encodeList_length]
  omega

theorem encodeRows_length (rows : List Row) :
    (encodeRows rows).length =
      2 * (rows.map (fun row => (encodeRow row).length)).sum + 2 * rows.length + 1 :=
  encodeList_length _ _

section ActualFactor

variable {D p q r : ℕ} {K A : Type*}
variable (encodeK : K → Word) (encodeA : A → Word)
variable (cache : List (List A)) (f : SubexpProgramBuilder.FactorData D p q r K A)

/-- Increasing ambient coordinates, with increasing degree inside each column. -/
def coordinate (label : Fin p) (i : Fin f.arity) : Coordinate where
  origin := List.ofFn (fun w : Fin D => encodeK (f.origin i w))
  taylor := List.ofFn (fun w : Fin D =>
    List.ofFn (fun j : Fin (q + 1) => encodeA (f.taylor i j w)))
  coefficients := (cache.getD label.val []).map encodeA

def row (source : SubexpTableInterpolation.Row p f.arity A) : Row where
  value := encodeA source.value
  coordinates := List.ofFn (fun i => coordinate encodeK encodeA cache f (source.labels.get i) i)

def rows : List Row := f.table.map (row encodeK encodeA cache f)

@[simp] theorem coordinate_origin_length (label : Fin p) (i : Fin f.arity) :
    (coordinate encodeK encodeA cache f label i).origin.length = D := by
  simp [coordinate]

@[simp] theorem coordinate_taylor_length (label : Fin p) (i : Fin f.arity) :
    (coordinate encodeK encodeA cache f label i).taylor.length = D := by
  simp [coordinate]

theorem coordinate_taylor_column_length (label : Fin p) (i : Fin f.arity)
    (column : List Word) (h : column ∈ (coordinate encodeK encodeA cache f label i).taylor) :
    column.length = q + 1 := by
  obtain ⟨w, rfl⟩ := List.mem_ofFn.mp h
  simp

@[simp] theorem row_coordinates_length (source : SubexpTableInterpolation.Row p f.arity A) :
    (row encodeK encodeA cache f source).coordinates.length = f.arity := by
  simp [row]

@[simp] theorem rows_length : (rows encodeK encodeA cache f).length = f.table.length := by
  simp [rows]

def preparedCoordinate (input : Word) (c : Coordinate) : SubexpTableSource.Coordinate :=
  ⟨input, c.coefficients⟩

/-- Once beta and Ce have actually been produced, the exact selected scalar
lists are those consumed by the factored table compiler. -/
theorem prepared_row_eq (source : SubexpTableInterpolation.Row p f.arity A)
    (inputs : Fin f.arity → Word) :
    (⟨encodeA source.value, List.ofFn (fun i => preparedCoordinate (inputs i)
      (coordinate encodeK encodeA cache f (source.labels.get i) i))⟩ : SubexpTableSource.Row) =
      SubexpTableSource.ofRow id encodeA cache inputs source := rfl

end ActualFactor

section PhysicalSelection

private theorem split_getD {A : Type*} (xs : List A) (n : ℕ) (fallback : A)
    (hn : n < xs.length) :
    xs.take n ++ xs.getD n fallback :: xs.drop (n + 1) = xs := by
  induction xs generalizing n with
  | nil => simp at hn
  | cons x xs ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simpa [List.getD_cons_succ] using
        congrArg (List.cons x) (ih n (by simpa using hn))

/-- No selected-stream premise: the fixed binary-index program reads the
actual label's entry from the complete encoded Lagrange cache. -/
theorem selected_packet_runsIn {A : Type*} (encode : A → Word)
    (cache : List (List A)) (label : Fin cache.length)
    (origin taylor bits acc : Word) (hbits : CounterPrograms.value bits = label.val)
    (regs : Fin 8 → Bool) :
    ∃ rf, BitProgram.RunsIn LagrangePacketBinary.program
      (LagrangePacketBinary.cost
        ((cache.take label.val).map (Encoding.encodeList encode))
        (Encoding.encodeList encode (cache.getD label.val []))
        ((cache.drop (label.val + 1)).map (Encoding.encodeList encode))
        (incidenceFields origin taylor) bits)
      ((LagrangePacketProgram.state regs bits [] []
        (ProgramEncoding.encodeRecords (cache.map (Encoding.encodeList encode))) []
        (incidenceFields origin taylor).reverse acc).withPC
          (some LagrangePacketBinary.program.entry))
      ((LagrangePacketProgram.state rf [] [] []
        (ProgramEncoding.encodeRecords (cache.map (Encoding.encodeList encode))) [] []
        (TupleProgram.prependRecord
          (packet origin taylor (Encoding.encodeList encode (cache.getD label.val []))) acc)).withPC none) := by
  have hsplit : (cache.take label.val).map (Encoding.encodeList encode) ++
      Encoding.encodeList encode (cache.getD label.val []) ::
        (cache.drop (label.val + 1)).map (Encoding.encodeList encode) =
      cache.map (Encoding.encodeList encode) := by
    simpa only [List.map_append, List.map_cons] using
      congrArg (List.map (Encoding.encodeList encode)) (split_getD cache label.val [] label.isLt)
  have hlength : CounterPrograms.value bits =
      ((cache.take label.val).map (Encoding.encodeList encode)).length := by
    simp only [List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt label.isLt)]
    exact hbits
  simpa only [hsplit, packet, SelectorPairProgram.payload] using
    LagrangePacketBinary.program_runsIn
      ((cache.take label.val).map (Encoding.encodeList encode))
      (Encoding.encodeList encode (cache.getD label.val []))
      ((cache.drop (label.val + 1)).map (Encoding.encodeList encode))
      (incidenceFields origin taylor) bits acc hlength regs

end PhysicalSelection

end SubexponentialSAT.Subexp.FactorBlueprint

end OAI.Algorithms
