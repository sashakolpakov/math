import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPacketProvenance
import OAI.Algorithms.SubexponentialSAT.SubexpFactorRowValues

namespace OAI.Algorithms

/-! Exact transport from the physical binary-label row constructor to the
typed factor packets. Coordinate order, cache indexing, and the descending
rank order of Boolean answers are all preserved. -/

namespace SubexponentialSAT.SubexpFactorPacketProvenance

open SubexpLiftRing SubexpQuarticRing SubexpSymbolicCost
open SubexpSelectedConversions SubexpInputBitProgram

variable {p D labels arity degree : ℕ} [Fact p.Prime]
variable (source : Prepared p 0) (target : Prepared p D)
variable (theta : Code p D) (input : Input p D labels arity degree)

def encodedCache : List (List (List Bool)) :=
  input.cache.map (List.map SubexpQuarticFlatNeg.flat)

def coordinatePrefix (i : Fin arity) : Subexp.FactorPacketCoordinates.Prefix where
  origin := (List.finRange D).map (fun w => SubexpQuarticFlatMul.flat (input.origins i w))
  taylor := columns source target theta input i

def prefixes : List Subexp.FactorPacketCoordinates.Prefix :=
  List.ofFn (coordinatePrefix source target theta input)

def binaryRows (width : ℕ) : List Subexp.FactorPacketRows.RawRow :=
  input.rows.map (fun row => SubexpFactorRowStream.rawOfTable width
    (SubexpRepresentedBuilder.mapRow SubexpQuarticFlatNeg.flat row))

theorem selected_pairs_eq (width : ℕ)
    (row : SubexpTableInterpolation.Row labels arity (Code p D)) :
    Subexp.FactorPacketRows.pairs (prefixes source target theta input)
      (SubexpFactorRowStream.rawOfTable width
        (SubexpRepresentedBuilder.mapRow SubexpQuarticFlatNeg.flat row)) =
      List.ofFn (fun i =>
        (fixedBits width (row.labels.get i).val, coordinatePrefix source target theta input i)) := by
  apply List.ext_getElem
  · simp [Subexp.FactorPacketRows.pairs, prefixes, SubexpFactorRowStream.rawOfTable,
      SubexpRepresentedBuilder.mapRow]
  · intro i hi hj
    simp only [Subexp.FactorPacketRows.pairs, prefixes, SubexpFactorRowStream.rawOfTable,
      SubexpRepresentedBuilder.mapRow, List.getElem_zip, List.getElem_map,
      List.getElem_ofFn, List.Vector.toList_getElem]
    rfl

/-- Binary decoding selects the same integer cache row as the typed label. -/
theorem selected_row_eq (width : ℕ) (hwidth : labels ≤ 2 ^ width)
    (row : SubexpTableInterpolation.Row labels arity (Code p D)) :
    Subexp.FactorPacketRows.blueprintRow (encodedCache input)
      (prefixes source target theta input)
      (SubexpFactorRowStream.rawOfTable width
        (SubexpRepresentedBuilder.mapRow SubexpQuarticFlatNeg.flat row)) =
      (SubexpBlueprintRows.Row.mk (SubexpQuarticFlatNeg.flat row.value)
        (List.ofFn (coordinate source target theta input row))).packet := by
  change Subexp.FactorBlueprint.Row.mk (SubexpQuarticFlatNeg.flat row.value)
      ((Subexp.FactorPacketRows.pairs (prefixes source target theta input)
        (SubexpFactorRowStream.rawOfTable width
          (SubexpRepresentedBuilder.mapRow SubexpQuarticFlatNeg.flat row))).map
        (Subexp.FactorPacketCoordinates.coordinate (encodedCache input))) =
    Subexp.FactorBlueprint.Row.mk (SubexpQuarticFlatNeg.flat row.value)
      ((List.ofFn (coordinate source target theta input row)).map
        SubexpBlueprintCoordinate.Coordinate.packet)
  apply congrArg (Subexp.FactorBlueprint.Row.mk (SubexpQuarticFlatNeg.flat row.value))
  rw [selected_pairs_eq, List.map_ofFn, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  have hv : CounterPrograms.value (fixedBits width (row.labels.get i).val) =
      (row.labels.get i).val := by
    rw [CounterPrograms.value_eq_toNat,
      toNat_fixedBits_of_lt _ _ ((row.labels.get i).isLt.trans_le hwidth)]
  simp only [Function.comp_apply, Subexp.FactorPacketCoordinates.coordinate,
    coordinatePrefix, coordinate, SubexpBlueprintCoordinate.Coordinate.packet, hv, encodedCache]
  congr 1
  exact List.getD_map (l := input.cache) (d := [])
    (n := (row.labels.get i).val) (List.map SubexpQuarticFlatNeg.flat)

theorem selected_rows_eq_blueprintRows (width : ℕ) (hwidth : labels ≤ 2 ^ width) :
    (binaryRows input width).map
      (Subexp.FactorPacketRows.blueprintRow (encodedCache input)
        (prefixes source target theta input)) =
      (blueprintRows source target theta input).map SubexpBlueprintRows.Row.packet := by
  simp only [binaryRows, blueprintRows, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro row hrow
  exact selected_row_eq source target theta input width hwidth row

omit [Fact p.Prime] in
theorem attachAnswers_flat (zero one : Code p D) (answers : List Bool) :
    (SubexpRankedTable.attachAnswers (p := p) (k := arity) zero one answers).map
      (SubexpRepresentedBuilder.mapRow SubexpQuarticFlatNeg.flat) =
      SubexpRankedTable.attachAnswers (p := p) (k := arity)
        (SubexpQuarticFlatNeg.flat zero) (SubexpQuarticFlatNeg.flat one) answers := by
  simp only [SubexpRankedTable.attachAnswers, List.map_zipWith, List.zipWith_map_right]
  apply congrArg (fun f : List.Vector (Fin p) arity → Bool →
      SubexpTableInterpolation.Row p arity (List Bool) =>
    (SubexpDigitGrid.descending p arity).zipWith f answers)
  funext row answer
  cases answer <;> rfl

/-- The actual numeric-rank table producer followed by the actual cache-row
selector yields exactly the typed blueprint rows used by provenance. -/
theorem ranked_selected_rows_eq
    (ranked : Input p D p arity degree) (modulus : List Bool)
    (hp : BinaryArithmetic.toNat modulus = p)
    (zero one : Code p D) (answers : List Bool)
    (hlen : answers.length = p ^ arity)
    (hrows : ranked.rows = SubexpRankedTable.attachAnswers zero one answers) :
    (SubexpFactorRowStream.tableRows modulus arity
      (SubexpQuarticFlatNeg.flat zero) (SubexpQuarticFlatNeg.flat one) answers).map
      (Subexp.FactorPacketRows.blueprintRow (encodedCache ranked)
        (prefixes source target theta ranked)) =
      (blueprintRows source target theta ranked).map SubexpBlueprintRows.Row.packet := by
  have hr : SubexpFactorRowStream.tableRows modulus arity
      (SubexpQuarticFlatNeg.flat zero) (SubexpQuarticFlatNeg.flat one) answers =
      binaryRows ranked modulus.length := by
    rw [SubexpFactorRowStream.tableRows_eq_attachAnswers modulus p arity
      (SubexpQuarticFlatNeg.flat zero) (SubexpQuarticFlatNeg.flat one) answers
      hp (Fact.out : p.Prime).pos hlen, ← attachAnswers_flat zero one answers]
    simp only [binaryRows, hrows, List.map_map, Function.comp_def]
  rw [hr]
  exact selected_rows_eq_blueprintRows source target theta ranked modulus.length
    (Nat.le_of_lt (hp ▸ ModularArithmetic.toNat_lt_pow_length modulus))

theorem ranked_selected_bytes_eq
    (ranked : Input p D p arity degree) (modulus : List Bool)
    (hp : BinaryArithmetic.toNat modulus = p)
    (zero one : Code p D) (answers : List Bool)
    (hlen : answers.length = p ^ arity)
    (hrows : ranked.rows = SubexpRankedTable.attachAnswers zero one answers) :
    Subexp.FactorBlueprint.encodeRows
      ((SubexpFactorRowStream.tableRows modulus arity
        (SubexpQuarticFlatNeg.flat zero) (SubexpQuarticFlatNeg.flat one) answers).map
        (Subexp.FactorPacketRows.blueprintRow (encodedCache ranked)
          (prefixes source target theta ranked))) =
      Subexp.FactorBlueprint.encodeRows
        ((blueprintRows source target theta ranked).map SubexpBlueprintRows.Row.packet) :=
  congrArg Subexp.FactorBlueprint.encodeRows
    (ranked_selected_rows_eq source target theta ranked modulus hp zero one answers hlen hrows)

end SubexponentialSAT.SubexpFactorPacketProvenance

end OAI.Algorithms
