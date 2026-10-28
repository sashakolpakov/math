import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTemplateExecution
import OAI.Algorithms.SubexponentialSAT.SubexpCacheArgumentCost
import OAI.Algorithms.SubexponentialSAT.BitProgramSelectedSpace

namespace OAI.Algorithms

/-!
# Byte bounds for the actual raw-template preparation program

The Taylor-column length is an explicit shape parameter. All coefficient
payloads are charged in the serialized input. The argument-size bound follows
from the trace of its real emitter, rather than an output-size hypothesis.
-/

namespace SubexponentialSAT.SubexpTemplateCostBounds

open scoped BigOperators
open BitProgram StructuredCalls SubexpLiftRing SubexpSelectedConversions

abbrev Bits := List Bool

attribute [local irreducible] SubexpScalarLiteralProgram.rawLiteral
  SubexpSymbolicCost.fixedKey SubexpBlueprintCoordinate.argument SubexpBlueprintCoordinate.negative

/-- One unit of overhead per framed list item, in addition to its bytes. -/
def mass {α : Type*} (enc : α → Bits) (xs : List α) : ℕ :=
  (xs.map (fun x => (enc x).length + 1)).sum

theorem encoded_length {α : Type*} (enc : α → Bits) (xs : List α) :
    (Encoding.encodeList enc xs).length + 1 = 2 * (mass enc xs + 1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [Encoding.length_encodeList_cons, mass, List.map_cons, List.sum_cons] at *
      omega

theorem sum_le_mass {α : Type*} (enc : α → Bits) (f : α → ℕ) (xs : List α) (K : ℕ)
    (h : ∀ x ∈ xs, f x ≤ K * ((enc x).length + 1)) :
    (xs.map f).sum ≤ K * mass enc xs := by
  induction xs with
  | nil => simp [mass]
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [mass, List.map_cons, List.sum_cons] at *
      nlinarith

theorem encoded_map_le {α : Type*} (enc out : α → Bits) (xs : List α) (K : ℕ)
    (hK : 1 ≤ K) (h : ∀ x ∈ xs, (out x).length + 1 ≤ K * ((enc x).length + 1)) :
    (Encoding.encodeList out xs).length + 1 ≤ K * ((Encoding.encodeList enc xs).length + 1) := by
  have hs := sum_le_mass enc (fun x => (out x).length + 1) xs K h
  rw [encoded_length, encoded_length]
  change mass out xs ≤ K * mass enc xs at hs
  nlinarith

theorem scan_le {α : Type*} (enc : α → Bits) (f : α → ℕ) (xs : List α) (K : ℕ)
    (h : ∀ x ∈ xs, f x ≤ K * ((enc x).length + 1)) :
    SubexpTemplateTraversal.scanBudget enc f xs ≤ (K + 9) * mass enc xs := by
  apply sum_le_mass
  intro x hx
  have hh := h x hx
  nlinarith

theorem bare_le {α : Type*} (enc : α → Bits) (f : α → ℕ) (xs : List α) (K : ℕ)
    (h : ∀ x ∈ xs, f x ≤ K * ((enc x).length + 1)) :
    SubexpTemplateTraversal.bareBudget f xs ≤ (K + 2) * mass enc xs := by
  apply sum_le_mass
  intro x hx
  have hh := h x hx
  nlinarith

theorem table_coordinate_length (c : SubexpTableSource.Coordinate) :
    (SubexpTableSource.encodeCoordinate c).length + 1 =
      2 * (c.input.length + 1) + (Encoding.encodeList id c.coefficients).length := by
  simp only [SubexpTableSource.encodeCoordinate, List.length_append, Encoding.length_frame]
  omega

theorem table_row_length (r : SubexpTableSource.Row) :
    (SubexpTableSource.encodeRow r).length + 1 =
      2 * (r.value.length + 1) + (Encoding.encodeList SubexpTableSource.encodeCoordinate r.coordinates).length := by
  simp only [SubexpTableSource.encodeRow, List.length_append, Encoding.length_frame]
  omega

def preparationUnit (D : ℕ) : ℕ := 1000 * (D + SubexpSymbolicCost.indexBits D + 1)

theorem preparationUnit_pos (D : ℕ) : 1 ≤ preparationUnit D := by
  unfold preparationUnit
  omega

theorem scalar_bounds (D : ℕ) (bits : Bits) (tag : Bool) :
    (SubexpScalarLiteralProgram.rawLiteral D bits).length + 1 ≤
      preparationUnit D * (bits.length + 1) ∧
    SubexpPreparedFactor.scalarCost D tag bits ≤ preparationUnit D * (bits.length + 1) := by
  have hl := SubexpWeightLiteralProgram.rawLiteral_length D bits
  have hc := SubexpScalarLiteralProgram.program_steps_le D bits
  constructor
  · rw [hl]
    unfold preparationUnit
    nlinarith
  · unfold SubexpPreparedFactor.scalarCost preparationUnit
    cases tag with
    | false =>
        simp only [Bool.false_eq_true, ite_false]
        rw [hl]
        nlinarith
    | true =>
        simp only [ite_true]
        rw [hl]
        nlinarith

theorem prepare_coordinate_bounds (D : ℕ) (c : SubexpTableSource.Coordinate) :
    (SubexpTableSource.encodeCoordinate (SubexpPreparedFactor.prepareCoordinate D c)).length + 1 ≤
      preparationUnit D * ((SubexpTableSource.encodeCoordinate c).length + 1) ∧
    SubexpPreparedFactor.coordinateCost D c ≤ 30 * preparationUnit D * ((SubexpTableSource.encodeCoordinate c).length + 1) := by
  have hJ := preparationUnit_pos D
  have hl := encoded_map_le id (SubexpScalarLiteralProgram.rawLiteral D) c.coefficients
    (preparationUnit D) hJ (fun x _ => (scalar_bounds D x true).1)
  have hs := sum_le_mass id (fun x => SubexpPreparedFactor.scalarCost D true x + 2) c.coefficients
    (preparationUnit D + 2) (by
      intro x hx
      have h := (scalar_bounds D x true).2
      simp only [id_eq]
      nlinarith)
  have hi := encoded_length id c.coefficients
  have ho : (SubexpTableSource.encodeCoordinate (SubexpPreparedFactor.prepareCoordinate D c)).length + 1 =
      2 * (c.input.length + 1) +
        (Encoding.encodeList (SubexpScalarLiteralProgram.rawLiteral D) c.coefficients).length := by
    rw [table_coordinate_length]
    simp only [SubexpPreparedFactor.prepareCoordinate, SubexpBlueprintRows.encodeList_map, id_eq]
  have hp : (SubexpPreparedFactor.coordinatePrefix D c).length + 1 =
      (SubexpTableSource.encodeCoordinate (SubexpPreparedFactor.prepareCoordinate D c)).length := by
    have h := SubexpPreparedFactor.encodeList_eq (SubexpScalarLiteralProgram.rawLiteral D) c.coefficients
    simp only [SubexpPreparedFactor.coordinatePrefix, SubexpTableSource.encodeCoordinate, SubexpPreparedFactor.prepareCoordinate,
      SubexpBlueprintRows.encodeList_map, id_eq, h, List.length_append, List.length_singleton]
    omega
  have he := table_coordinate_length c
  have hout : (SubexpTableSource.encodeCoordinate (SubexpPreparedFactor.prepareCoordinate D c)).length + 1 ≤
      preparationUnit D * ((SubexpTableSource.encodeCoordinate c).length + 1) := by nlinarith
  refine ⟨hout, ?_⟩
  change (c.coefficients.map (fun x => SubexpPreparedFactor.scalarCost D true x + 2)).sum ≤ _ at hs
  unfold SubexpPreparedFactor.coordinateCost SubexpPreparedFactor.scanCost
  nlinarith

theorem prepare_row_bounds (D : ℕ) (r : SubexpTableSource.Row) :
    (SubexpTableSource.encodeRow (SubexpPreparedFactor.prepareRow D r)).length + 1 ≤
      2 * preparationUnit D * ((SubexpTableSource.encodeRow r).length + 1) ∧
    SubexpPreparedFactor.rowCost D r ≤ 100 * preparationUnit D * ((SubexpTableSource.encodeRow r).length + 1) := by
  have hJ := preparationUnit_pos D
  have hv := scalar_bounds D r.value false
  have hl := encoded_map_le SubexpTableSource.encodeCoordinate
    (fun c => SubexpTableSource.encodeCoordinate (SubexpPreparedFactor.prepareCoordinate D c)) r.coordinates
    (preparationUnit D) hJ (fun c _ => (prepare_coordinate_bounds D c).1)
  have hs := sum_le_mass SubexpTableSource.encodeCoordinate
    (fun c => 9 * (SubexpTableSource.encodeCoordinate c).length + 7 + SubexpPreparedFactor.coordinateCost D c + 2)
    r.coordinates (30 * preparationUnit D + 9) (by
      intro c hc
      have h := (prepare_coordinate_bounds D c).2
      nlinarith)
  have hi := encoded_length SubexpTableSource.encodeCoordinate r.coordinates
  have ho : (SubexpTableSource.encodeRow (SubexpPreparedFactor.prepareRow D r)).length + 1 =
      2 * ((SubexpScalarLiteralProgram.rawLiteral D r.value).length + 1) +
        (Encoding.encodeList (fun c => SubexpTableSource.encodeCoordinate (SubexpPreparedFactor.prepareCoordinate D c)) r.coordinates).length := by
    rw [table_row_length]
    simp only [SubexpPreparedFactor.prepareRow, SubexpBlueprintRows.encodeList_map]
  have hp : (SubexpPreparedFactor.rowPrefix D r).length + 1 = (SubexpTableSource.encodeRow (SubexpPreparedFactor.prepareRow D r)).length := by
    have h := SubexpPreparedFactor.encodeList_eq (fun c => SubexpTableSource.encodeCoordinate (SubexpPreparedFactor.prepareCoordinate D c)) r.coordinates
    simp only [SubexpPreparedFactor.rowPrefix, SubexpTableSource.encodeRow, SubexpPreparedFactor.prepareRow, SubexpBlueprintRows.encodeList_map,
      h, List.length_append, List.length_singleton]
    omega
  have he := table_row_length r
  have hout : (SubexpTableSource.encodeRow (SubexpPreparedFactor.prepareRow D r)).length + 1 ≤
      2 * preparationUnit D * ((SubexpTableSource.encodeRow r).length + 1) := by nlinarith
  refine ⟨hout, ?_⟩
  unfold SubexpPreparedFactor.rowCost SubexpPreparedFactor.scanCost
  nlinarith

theorem prepare_rows_bounds (D : ℕ) (rows : List SubexpTableSource.Row) :
    (SubexpTableSource.encodeRows (SubexpPreparedFactor.prepareRows D rows)).length + 1 ≤
      2 * preparationUnit D * ((SubexpTableSource.encodeRows rows).length + 1) ∧
    SubexpPreparedFactor.runCost D rows ≤ 200 * preparationUnit D * ((SubexpTableSource.encodeRows rows).length + 1) := by
  have hJ := preparationUnit_pos D
  have hl := encoded_map_le SubexpTableSource.encodeRow (fun r => SubexpTableSource.encodeRow (SubexpPreparedFactor.prepareRow D r))
    rows (2 * preparationUnit D) (by omega) (fun r _ => (prepare_row_bounds D r).1)
  have hs := sum_le_mass SubexpTableSource.encodeRow
    (fun r => 9 * (SubexpTableSource.encodeRow r).length + 7 + SubexpPreparedFactor.rowCost D r + 2)
    rows (100 * preparationUnit D + 9) (by
      intro r hr
      have h := (prepare_row_bounds D r).2
      nlinarith)
  have hi := encoded_length SubexpTableSource.encodeRow rows
  change _ ≤ 2 * preparationUnit D * ((SubexpTableSource.encodeRows rows).length + 1) at hl
  have hout : (SubexpTableSource.encodeRows (SubexpPreparedFactor.prepareRows D rows)).length + 1 ≤
      2 * preparationUnit D * ((SubexpTableSource.encodeRows rows).length + 1) := by
    simpa only [SubexpTableSource.encodeRows, SubexpPreparedFactor.prepareRows, SubexpBlueprintRows.encodeList_map] using hl
  refine ⟨hout, ?_⟩
  unfold SubexpTableSource.encodeRows at hout
  unfold SubexpPreparedFactor.runCost SubexpPreparedFactor.rowsCost SubexpPreparedFactor.scanCost
  dsimp only
  simp only [SubexpTableSource.encodeRows]
  change (Encoding.encodeList SubexpTableSource.encodeRow rows).length + 1 = _ at hi
  nlinarith

theorem encoded_uniform {α : Type*} (enc : α → Bits) (xs : List α) (n : ℕ)
    (h : ∀ x ∈ xs, (enc x).length = n) :
    (Encoding.encodeList enc xs).length = xs.length * (2 * n + 2) + 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [Encoding.length_encodeList_cons, List.length_cons, hx, ht]
      nlinarith

theorem eval_output_le {r s : ℕ} {cmd : Cmd r s} {n : ℕ} {a b : State r s}
    (i : Fin s) (h : Eval cmd n a b) : (b.stacks i).length ≤ (a.stacks i).length + n := by
  have hh := trace_selectedStackBits (compiled cmd i i) {i} (compiled_trace h i i)
  simpa only [selectedStackBits, Finset.sum_singleton, StructuredProgram.State.withPC] using hh

/-- Every emitted bit is accounted for by an actual instruction in the cache program. -/
theorem argument_length_le (beta negative : Bits) (columns : List (List Bits)) (I : ℕ) :
    (SubexpCacheArgument.resultBits beta negative columns I [false]).length ≤
      SubexpCacheArgument.totalCost beta negative columns I + 1 := by
  obtain ⟨v, p, u, h⟩ := SubexpCacheArgument.command_eval beta negative columns I
    false false false false false false false false [false]
  have hh := eval_output_le 5 h
  change (SubexpCacheArgument.resultBits beta negative columns I [false]).length ≤
    1 + SubexpCacheArgument.totalCost beta negative columns I at hh
  omega

variable {p D : ℕ} [Fact p.Prime]

def betaBound (p D : ℕ) : ℕ :=
  430000 * (D + 2)^2 * (baseWidth p 1 + 2)^2 +
    28 * baseWidth p 1 + 7 * (D * (8 * baseWidth p 1 + 2) + 1) + 10

def cacheBound (p D q : ℕ) : ℕ :=
  352 * baseWidth p (D + 1) +
    D * q * (33 * (D + q) + 32 * SubexpSymbolicCost.indexBits D + 275) +
    130 * D + 64 * SubexpSymbolicCost.indexBits D + 449

def workUnit (p D q : ℕ) : ℕ :=
  betaBound p D + 25000 * (baseWidth p (D + 1) + 1)^2 + cacheBound p D q +
    SubexpPointBank.steps D (baseWidth p 1) + 100

def coordinateUnit (p D q : ℕ) : ℕ := 100 * workUnit p D q

def ColumnBound (q : ℕ) (c : SubexpBlueprintCoordinate.Coordinate p D) : Prop :=
  ∀ column ∈ c.columns, column.length ≤ q

theorem workUnit_pos (p D q : ℕ) : 100 ≤ workUnit p D q := by unfold workUnit; omega

omit [Fact p.Prime] in
theorem pointBytes_length (point : Fin D → SubexpInputBitProgram.ResidueCode p) :
    (SubexpTemplateFactors.pointBytes point).length = D * (8 * baseWidth p 1 + 2) + 1 := by
  unfold SubexpTemplateFactors.pointBytes
  rw [encoded_uniform _ _ (4 * baseWidth p 1) (by
    intro x hx
    exact SubexpQuarticFlatMul.flat_length x)]
  simp only [List.length_map, List.length_finRange]
  ring

theorem betaBudget_le (ctx : SubexpBlueprintFactor.Context) (source : Prepared p 0)
    (target : Prepared p D) (minusOne : SubexpQuarticRing.Word (baseWidth p (D+1)))
    (point : Fin D → SubexpInputBitProgram.ResidueCode p)
    (hc : SubexpBlueprintCoordinate.ContextGood ctx source target minusOne point) :
    SubexpBlueprintCoordinate.betaBudget (p := p) (D := D) ctx ≤ betaBound p D := by
  have h := SubexpInputBitProgram.sourceSteps_polynomial D p
  have hp := pointBytes_length point
  have hz : ctx.sourceZero.length = 4 * baseWidth p 1 := by
    rw [hc.sourceZero, SubexpQuarticFlatMul.flat_length]
  have hl : ctx.pointStream.length = D * (8 * baseWidth p 1 + 2) + 1 := by
    rw [hc.pointStream]
    exact hp
  unfold SubexpBlueprintCoordinate.betaBudget betaBound
  rw [hz, hl]
  have hb : Nat.log 2 p + 3 = baseWidth p 1 + 2 := by simp [baseWidth]
  rw [hb] at h
  omega

theorem coordinate_bounds (ctx : SubexpBlueprintFactor.Context) (source : Prepared p 0)
    (target : Prepared p D) (minusOne : SubexpQuarticRing.Word (baseWidth p (D+1)))
    (point : Fin D → SubexpInputBitProgram.ResidueCode p)
    (hc : SubexpBlueprintCoordinate.ContextGood ctx source target minusOne point)
    (hI : ctx.indexWidth = SubexpSymbolicCost.indexBits D)
    (q : ℕ) (c : SubexpBlueprintCoordinate.Coordinate p D) (hq : ColumnBound q c) :
    (SubexpTableSource.encodeCoordinate (SubexpBlueprintCoordinate.output ctx source target minusOne point c)).length + 1 ≤
      coordinateUnit p D q * ((SubexpBlueprintCoordinate.encode c).length + 1) ∧
    SubexpBlueprintCoordinate.cost ctx source target minusOne point c ≤
      coordinateUnit p D q * ((SubexpBlueprintCoordinate.encode c).length + 1) := by
  let W := workUnit p D q
  have hW : 100 ≤ W := workUnit_pos p D q
  have hparts : betaBound p D + 25000 * (baseWidth p (D+1) + 1)^2 +
      cacheBound p D q + 100 ≤ W := by dsimp [W, workUnit]; omega
  have hB : 352 * baseWidth p (D+1) ≤ cacheBound p D q := by unfold cacheBound; omega
  have hb := betaBudget_le ctx source target minusOne point hc
  have ht := SubexpCacheArgument.totalCost_le
    (SubexpQuarticFlatNeg.flat (SubexpInputBitProgram.betaOutput source c.origin point))
    (SubexpQuarticFlatNeg.flat (SubexpBlueprintCoordinate.negative source target minusOne point c))
    c.columns ctx.indexWidth q hq
  simp only [SubexpQuarticFlatNeg.flat_length, c.dimension, hI] at ht
  change SubexpCacheArgument.totalCost _ _ _ _ + 1 ≤
    44 * (4 * baseWidth p (D+1) + 4 * baseWidth p (D+1)) +
      92 * SubexpCacheArgument.allPayloadBits c.columns +
      D * q * (33 * (D+q) + 32 * SubexpSymbolicCost.indexBits D + 275) +
      130*D+64*SubexpSymbolicCost.indexBits D+449 at ht
  have hcache : SubexpCacheArgument.totalCost
      (SubexpQuarticFlatNeg.flat (SubexpInputBitProgram.betaOutput source c.origin point))
      (SubexpQuarticFlatNeg.flat (SubexpBlueprintCoordinate.negative source target minusOne point c))
      c.columns ctx.indexWidth + 1 ≤
      cacheBound p D q + 92 * SubexpCacheArgument.allPayloadBits c.columns := by
    rw [hI]
    unfold cacheBound
    nlinarith [ht]
  have ha := argument_length_le
    (SubexpQuarticFlatNeg.flat (SubexpInputBitProgram.betaOutput source c.origin point))
    (SubexpQuarticFlatNeg.flat (SubexpBlueprintCoordinate.negative source target minusOne point c))
    c.columns ctx.indexWidth
  have harg : (SubexpBlueprintCoordinate.argument ctx source target minusOne point c).length ≤
      cacheBound p D q + 92 * SubexpCacheArgument.allPayloadBits c.columns := by
    rw [SubexpBlueprintCoordinate.argument]
    exact ha.trans hcache
  have hpayload := SubexpCacheArgument.cache_length c.columns
  rw [← SubexpBlueprintCoordinate.taylorBytes_eq] at hpayload
  have henc : (SubexpBlueprintCoordinate.encode c).length = 4 * (SubexpBlueprintCoordinate.originBytes c).length +
      4 * (SubexpBlueprintCoordinate.taylorBytes c).length + 2 * (SubexpBlueprintCoordinate.coefficientBytes c).length + 6 :=
    Subexp.FactorBlueprint.encodeCoordinate_length c.packet
  have hi : (SubexpBlueprintCoordinate.incidenceBytes c).length =
      2 * (SubexpBlueprintCoordinate.originBytes c).length + 2 * (SubexpBlueprintCoordinate.taylorBytes c).length + 2 := by
    simp only [SubexpBlueprintCoordinate.incidenceBytes, List.length_append, Encoding.length_frame]
    omega
  have ho : (SubexpTableSource.encodeCoordinate (SubexpBlueprintCoordinate.output ctx source target minusOne point c)).length =
      2 * (SubexpBlueprintCoordinate.argument ctx source target minusOne point c).length + 1 +
        (SubexpBlueprintCoordinate.coefficientBytes c).length := by
    simp only [SubexpTableSource.encodeCoordinate, SubexpBlueprintCoordinate.output, List.length_append, Encoding.length_frame]
    rfl
  have hbudget : SubexpBlueprintCoordinate.argumentBudget ctx source target minusOne point c ≤
      25000 * (baseWidth p (D+1) + 1)^2 + cacheBound p D q +
        92 * SubexpCacheArgument.allPayloadBits c.columns + 3 := by
    unfold SubexpBlueprintCoordinate.argumentBudget
    omega
  let T := W * ((SubexpBlueprintCoordinate.encode c).length + 1)
  have hWT : W ≤ T := by dsimp only [T]; nlinarith only [hW]
  have hET : (SubexpBlueprintCoordinate.encode c).length + 1 ≤ T := by
    dsimp only [T]; nlinarith only [hW]
  have hPT : 92 * SubexpCacheArgument.allPayloadBits c.columns ≤ T := by
    dsimp only [T]
    nlinarith only [hW, henc, hpayload]
  have hsmall : (SubexpBlueprintCoordinate.argument ctx source target minusOne point c).length + 1 ≤ T := by
    dsimp only [T]
    nlinarith only [harg, hpayload, henc, hparts, hW]
  have hout : (SubexpTableSource.encodeCoordinate (SubexpBlueprintCoordinate.output ctx source target minusOne point c)).length + 1 ≤
      3 * T := by omega
  have hbudgetT : SubexpBlueprintCoordinate.argumentBudget ctx source target minusOne point c ≤ 2 * T := by omega
  have hbetaT : SubexpBlueprintCoordinate.betaBudget (p:=p) (D:=D) ctx ≤ T := by omega
  have hBT : 4 * baseWidth p (D+1) ≤ T := by omega
  constructor
  · unfold coordinateUnit
    change _ ≤ 100 * W * _
    rw [Nat.mul_assoc]
    change _ ≤ 100 * T
    omega
  · unfold SubexpBlueprintCoordinate.cost coordinateUnit
    simp only [SubexpQuarticFlatNeg.flat_length, SubexpQuarticFlatMul.flat_length]
    change _ ≤ 100 * W * _
    rw [Nat.mul_assoc]
    change _ ≤ 100 * T
    omega

def RowBound (q : ℕ) (r : SubexpBlueprintRows.Row p D) : Prop :=
  ∀ c ∈ r.coordinates, ColumnBound q c

def FactorBound (q : ℕ) (rows : SubexpTemplateFactors.Factor p D) : Prop :=
  ∀ r ∈ rows, RowBound q r

def factorUnit (p D q : ℕ) : ℕ :=
  1000 * preparationUnit D * coordinateUnit p D q

theorem coordinateUnit_pos (p D q : ℕ) : 100 ≤ coordinateUnit p D q := by
  have h := workUnit_pos p D q
  unfold coordinateUnit
  omega

theorem factorUnit_pos (p D q : ℕ) : 1 ≤ factorUnit p D q := by
  have hJ := preparationUnit_pos D
  have hK := coordinateUnit_pos p D q
  unfold factorUnit
  nlinarith

omit [Fact p.Prime] in
theorem raw_row_length (r : SubexpBlueprintRows.Row p D) :
    (SubexpBlueprintRows.encode r).length + 1 =
      2 * r.value.length + 1 + (Encoding.encodeList SubexpBlueprintCoordinate.encode r.coordinates).length + 1 := by
  simp only [SubexpBlueprintRows.encode, SubexpBlueprintRows.Row.packet,
    Subexp.FactorBlueprint.encodeRow, SubexpBlueprintRows.encodeList_map,
    List.length_append, Encoding.length_frame]
  rfl

omit [Fact p.Prime] in
theorem factor_encode (rows : SubexpTemplateFactors.Factor p D) :
    SubexpTemplateFactors.encode rows = Encoding.encodeList SubexpBlueprintRows.encode rows := by
  simp only [SubexpTemplateFactors.encode, Subexp.FactorBlueprint.encodeRows,
    SubexpBlueprintRows.encodeList_map]
  rfl

theorem row_bounds (ctx : SubexpBlueprintFactor.Context) (source : Prepared p 0)
    (target : Prepared p D) (minusOne : SubexpQuarticRing.Word (baseWidth p (D+1)))
    (point : Fin D → SubexpInputBitProgram.ResidueCode p)
    (hc : SubexpBlueprintCoordinate.ContextGood ctx source target minusOne point)
    (hI : ctx.indexWidth = SubexpSymbolicCost.indexBits D)
    (q : ℕ) (r : SubexpBlueprintRows.Row p D) (hq : RowBound q r) :
    (SubexpTableSource.encodeRow (SubexpBlueprintRows.output ctx source target minusOne point r)).length + 1 ≤
      coordinateUnit p D q * ((SubexpBlueprintRows.encode r).length + 1) ∧
    SubexpBlueprintRows.cost ctx source target minusOne point r ≤
      100 * coordinateUnit p D q * ((SubexpBlueprintRows.encode r).length + 1) := by
  let K := coordinateUnit p D q
  have hK : 100 ≤ K := coordinateUnit_pos p D q
  have hl := encoded_map_le SubexpBlueprintCoordinate.encode
    (fun c => SubexpTableSource.encodeCoordinate (SubexpBlueprintCoordinate.output ctx source target minusOne point c)) r.coordinates
    K (by omega) (fun c hc' => (coordinate_bounds ctx source target minusOne point hc hI q c (hq c hc')).1)
  have hs := scan_le SubexpBlueprintCoordinate.encode (SubexpBlueprintCoordinate.cost ctx source target minusOne point) r.coordinates K
    (fun c hc' => (coordinate_bounds ctx source target minusOne point hc hI q c (hq c hc')).2)
  have hi := encoded_length SubexpBlueprintCoordinate.encode r.coordinates
  have he := raw_row_length r
  have ho : (SubexpTableSource.encodeRow (SubexpBlueprintRows.output ctx source target minusOne point r)).length + 1 =
      2 * r.value.length + 1 +
        (Encoding.encodeList (fun c => SubexpTableSource.encodeCoordinate (SubexpBlueprintCoordinate.output ctx source target minusOne point c))
          r.coordinates).length + 1 := by
    simp only [SubexpTableSource.encodeRow, SubexpBlueprintRows.output, SubexpBlueprintRows.encodeList_map, List.length_append, Encoding.length_frame]
  have hp : (Encoding.frame r.value ++ SubexpBlueprintRows.coordinateRecords ctx source target minusOne point r.coordinates).length + 1 =
      (SubexpTableSource.encodeRow (SubexpBlueprintRows.output ctx source target minusOne point r)).length := by
    have h := SubexpBlueprintRows.encodeList_eq_records
      (fun c => SubexpTableSource.encodeCoordinate (SubexpBlueprintCoordinate.output ctx source target minusOne point c)) r.coordinates
    simp only [SubexpBlueprintRows.coordinateRecords, SubexpTableSource.encodeRow, SubexpBlueprintRows.output, SubexpBlueprintRows.encodeList_map,
      h, List.length_append, List.length_singleton]
    omega
  have hout : (SubexpTableSource.encodeRow (SubexpBlueprintRows.output ctx source target minusOne point r)).length + 1 ≤
      K * ((SubexpBlueprintRows.encode r).length + 1) := by nlinarith
  refine ⟨hout, ?_⟩
  change SubexpBlueprintTraversal.scanBudget SubexpBlueprintCoordinate.encode
    (SubexpBlueprintCoordinate.cost ctx source target minusOne point) r.coordinates ≤ _ at hs
  unfold SubexpBlueprintRows.cost
  change _ ≤ 100 * K * _
  nlinarith

theorem rows_bounds (ctx : SubexpBlueprintFactor.Context) (source : Prepared p 0)
    (target : Prepared p D) (minusOne : SubexpQuarticRing.Word (baseWidth p (D+1)))
    (point : Fin D → SubexpInputBitProgram.ResidueCode p)
    (hc : SubexpBlueprintCoordinate.ContextGood ctx source target minusOne point)
    (hI : ctx.indexWidth = SubexpSymbolicCost.indexBits D)
    (q : ℕ) (rows : SubexpTemplateFactors.Factor p D) (hq : FactorBound q rows) :
    (SubexpTableSource.encodeRows (SubexpBlueprintRows.rowsOutput ctx source target minusOne point rows)).length + 1 ≤
      coordinateUnit p D q * ((SubexpTemplateFactors.encode rows).length + 1) ∧
    SubexpBlueprintRows.rowsCost ctx source target minusOne point rows ≤
      200 * coordinateUnit p D q * ((SubexpTemplateFactors.encode rows).length + 1) := by
  let K := coordinateUnit p D q
  have hK : 100 ≤ K := coordinateUnit_pos p D q
  have hl := encoded_map_le SubexpBlueprintRows.encode
    (fun r => SubexpTableSource.encodeRow (SubexpBlueprintRows.output ctx source target minusOne point r)) rows K (by omega)
    (fun r hr => (row_bounds ctx source target minusOne point hc hI q r (hq r hr)).1)
  have hout : (SubexpTableSource.encodeRows (SubexpBlueprintRows.rowsOutput ctx source target minusOne point rows)).length + 1 ≤
      K * ((SubexpTemplateFactors.encode rows).length + 1) := by
    simpa only [SubexpTableSource.encodeRows, SubexpBlueprintRows.rowsOutput, SubexpBlueprintRows.encodeList_map, factor_encode] using hl
  have hs := scan_le SubexpBlueprintRows.encode (SubexpBlueprintRows.cost ctx source target minusOne point) rows (100*K)
    (fun r hr => (row_bounds ctx source target minusOne point hc hI q r (hq r hr)).2)
  have hi := encoded_length SubexpBlueprintRows.encode rows
  rw [← factor_encode] at hi
  refine ⟨hout, ?_⟩
  change SubexpBlueprintTraversal.scanBudget SubexpBlueprintRows.encode
    (SubexpBlueprintRows.cost ctx source target minusOne point) rows ≤ _ at hs
  unfold SubexpBlueprintRows.rowsCost
  change _ ≤ 200 * K * _
  nlinarith

theorem factor_bounds (ctx : SubexpBlueprintFactor.Context) (source : Prepared p 0)
    (target : Prepared p D) (minusOne : SubexpQuarticRing.Word (baseWidth p (D+1)))
    (hc : SubexpTemplateData.ContextGood ctx source target minusOne)
    (point : Fin D → SubexpInputBitProgram.ResidueCode p)
    (q : ℕ) (rows : SubexpTemplateFactors.Factor p D) (hq : FactorBound q rows) :
    (SubexpTableSource.encodeRows (SubexpTemplateFactors.output ctx source target minusOne point rows)).length + 1 ≤
      factorUnit p D q * ((SubexpTemplateFactors.encode rows).length + 1) ∧
    SubexpTemplateFactors.cost ctx source target minusOne point rows ≤
      factorUnit p D q * ((SubexpTemplateFactors.encode rows).length + 1) := by
  let K := coordinateUnit p D q
  let J := preparationUnit D
  have hK : 100 ≤ K := coordinateUnit_pos p D q
  have hJ : 1 ≤ J := preparationUnit_pos D
  have hr := rows_bounds (SubexpTemplateFactors.contextFor ctx point) source target minusOne point
    (hc.forPoint point) (by simpa only [SubexpTemplateFactors.contextFor, hc.dimension] using hc.indexWidth) q rows hq
  have hp := prepare_rows_bounds D
    (SubexpBlueprintRows.rowsOutput (SubexpTemplateFactors.contextFor ctx point) source target minusOne point rows)
  have hd : (SubexpTemplateFactors.contextFor ctx point).dimension = D := hc.dimension
  have hout : (SubexpTableSource.encodeRows (SubexpTemplateFactors.output ctx source target minusOne point rows)).length + 1 ≤
      2 * J * K * ((SubexpTemplateFactors.encode rows).length + 1) := by
    unfold SubexpTemplateFactors.output SubexpBlueprintExecution.preparedRows
    rw [hd]
    exact hp.1.trans (by nlinarith [hr.1])
  have hprep : SubexpPreparedFactor.runCost D
      (SubexpBlueprintRows.rowsOutput (SubexpTemplateFactors.contextFor ctx point) source target minusOne point rows) ≤
      200 * J * K * ((SubexpTemplateFactors.encode rows).length + 1) :=
    hp.2.trans (by nlinarith [hr.1])
  constructor
  · unfold factorUnit
    change _ ≤ 1000 * J * K * _
    nlinarith
  · unfold SubexpTemplateFactors.cost SubexpBlueprintExecution.runCost
    rw [hd]
    unfold factorUnit
    change _ ≤ 1000 * J * K * _
    nlinarith [hr.2]

def TermBound (q : ℕ) (t : SubexpTemplateData.Term p D) : Prop :=
  ∀ rows ∈ t.factors, FactorBound q rows

def BlockBound (q : ℕ) (b : SubexpTemplateData.Block p D) : Prop :=
  ∀ group ∈ b.groups, ∀ t ∈ group, TermBound q t

/-- Only the number of Taylor entries per coordinate is bounded separately;
all scalar payload widths remain part of the actual raw input byte count. -/
def TaylorBound (q : ℕ) (bs : List (SubexpTemplateData.Block p D)) : Prop :=
  ∀ b ∈ bs, BlockBound q b

def rawBytes (bs : List (SubexpTemplateData.Block p D)) : ℕ :=
  (SubexpTemplateProgram.encodeBlocks (bs.map SubexpTemplateData.rawBlock)).length

omit [Fact p.Prime] in
theorem raw_term_length (t : SubexpTemplateData.Term p D) :
    (SubexpTemplateProgram.encodeTerm (SubexpTemplateData.rawTerm t)).length + 1 =
      2 * ((SubexpTemplateData.bankBytes t.increment).length + (SubexpTemplateData.supportBytes t.support).length +
        (SubexpTemplateData.rawFactorBytes t).length + 2) := by
  simp only [SubexpTemplateProgram.encodeTerm, SubexpTemplateData.rawTerm,
    SubexpTemplateData.rawFactorBytes, SubexpBlueprintRows.encodeList_map,
    List.length_append, Encoding.length_frame]
  change (2 * (SubexpTemplateData.bankBytes t.increment).length + 1) +
    (2 * (SubexpTemplateData.supportBytes t.support).length + 1) +
    (2 * (SubexpTemplateData.rawFactorBytes t).length + 1) + 1 =
      2 * ((SubexpTemplateData.bankBytes t.increment).length +
        (SubexpTemplateData.supportBytes t.support).length + (SubexpTemplateData.rawFactorBytes t).length + 2)
  omega

omit [Fact p.Prime] in
theorem bank_length (point : Fin D → SubexpTemplatePointServices.BaseWord p) :
    (SubexpTemplateData.bankBytes point).length = D * baseWidth p 1 := by
  rw [SubexpTemplateData.bankBytes, DensePolynomialLoop.flatten_length, List.length_map, List.length_finRange]

theorem point_overhead_le (q : ℕ) (source : Prepared p 0)
    (base increment : Fin D → SubexpTemplatePointServices.BaseWord p) :
    2 * (SubexpTemplatePointServices.pointStream p source.modulus base increment).length +
      SubexpPointBank.steps D (baseWidth p 1) + 79 ≤ factorUnit p D q := by
  have hs : (SubexpTemplatePointServices.pointStream p source.modulus base increment).length =
      D * (8 * baseWidth p 1 + 2) + 1 :=
    pointBytes_length (SubexpTemplatePointServices.quarticPoint p source.modulus base increment)
  have hW := workUnit_pos p D q
  have hJ := preparationUnit_pos D
  have hm : 2 * (D * (8 * baseWidth p 1 + 2) + 1) +
      SubexpPointBank.steps D (baseWidth p 1) + 79 ≤ workUnit p D q := by
    unfold workUnit betaBound
    omega
  rw [hs]
  unfold factorUnit coordinateUnit
  nlinarith

theorem term_bounds (ctx : SubexpBlueprintFactor.Context) (source : Prepared p 0)
    (target : Prepared p D) (minusOne : SubexpQuarticRing.Word (baseWidth p (D+1)))
    (hc : SubexpTemplateData.ContextGood ctx source target minusOne)
    (base : Fin D → SubexpTemplatePointServices.BaseWord p)
    (q : ℕ) (t : SubexpTemplateData.Term p D) (hq : TermBound q t) :
    (SubexpMomentSourceProgram.encodeTerm (SubexpTemplateData.preparedTerm ctx source target minusOne base t)).length + 1 ≤
      factorUnit p D q * ((SubexpTemplateProgram.encodeTerm (SubexpTemplateData.rawTerm t)).length + 1) ∧
    SubexpTemplateData.termCost ctx source target minusOne base t ≤
      100 * factorUnit p D q * ((SubexpTemplateProgram.encodeTerm (SubexpTemplateData.rawTerm t)).length + 1) := by
  let F := factorUnit p D q
  have hF : 1 ≤ F := factorUnit_pos p D q
  have hl := encoded_map_le SubexpTemplateFactors.encode
    (fun rows => SubexpTableSource.encodeRows (SubexpTemplateFactors.output ctx source target minusOne (SubexpTemplateData.point source base t) rows))
    t.factors F hF
    (fun rows hr => (factor_bounds ctx source target minusOne hc (SubexpTemplateData.point source base t) q rows (hq rows hr)).1)
  have hf : (SubexpTemplateData.preparedFactorBytes ctx source target minusOne base t).length + 1 ≤
      F * ((SubexpTemplateData.rawFactorBytes t).length + 1) := by
    simpa only [SubexpTemplateData.preparedFactorBytes, SubexpTemplateData.preparedFactors, SubexpTemplateData.rawFactorBytes,
      SubexpBlueprintRows.encodeList_map] using hl
  have hs := bare_le SubexpTemplateFactors.encode
    (SubexpTemplateFactors.cost ctx source target minusOne (SubexpTemplateData.point source base t)) t.factors F
    (fun rows hr => (factor_bounds ctx source target minusOne hc (SubexpTemplateData.point source base t) q rows (hq rows hr)).2)
  have hi := encoded_length SubexpTemplateFactors.encode t.factors
  change (SubexpTemplateData.rawFactorBytes t).length + 1 = _ at hi
  have hb := SubexpTemplatePointServices.pointBank_length p source.modulus base t.increment
  rw [← bank_length t.increment] at hb
  have hp := point_overhead_le q source base t.increment
  have he := raw_term_length t
  have ho : (SubexpMomentSourceProgram.encodeTerm (SubexpTemplateData.preparedTerm ctx source target minusOne base t)).length + 1 =
      2 * ((SubexpTemplateData.bankBytes t.increment).length + (SubexpTemplateData.supportBytes t.support).length +
        (SubexpTemplateData.preparedFactorBytes ctx source target minusOne base t).length + 2) := by
    simp only [SubexpMomentSourceProgram.encodeTerm, SubexpMomentSourceProgram.encodeDescriptor, SubexpTemplateData.preparedTerm,
      SubexpTemplateData.preparedFactorBytes, List.length_append, Encoding.length_frame, hb]
    omega
  have hout : (SubexpMomentSourceProgram.encodeTerm (SubexpTemplateData.preparedTerm ctx source target minusOne base t)).length + 1 ≤
      F * ((SubexpTemplateProgram.encodeTerm (SubexpTemplateData.rawTerm t)).length + 1) := by nlinarith
  refine ⟨hout, ?_⟩
  unfold SubexpTemplateData.termCost
  rw [hb]
  change _ ≤ 100 * F * _
  nlinarith

theorem group_bounds (ctx : SubexpBlueprintFactor.Context) (source : Prepared p 0)
    (target : Prepared p D) (minusOne : SubexpQuarticRing.Word (baseWidth p (D+1)))
    (hc : SubexpTemplateData.ContextGood ctx source target minusOne)
    (base : Fin D → SubexpTemplatePointServices.BaseWord p)
    (q : ℕ) (ts : List (SubexpTemplateData.Term p D)) (hq : ∀ t ∈ ts, TermBound q t) :
    (SubexpTemplateGroups.groupOutput ctx source target minusOne base ts).length + 1 ≤
      factorUnit p D q * ((SubexpTemplateProgram.encodeGroup (ts.map SubexpTemplateData.rawTerm)).length + 1) ∧
    SubexpTemplateGroups.groupCost ctx source target minusOne base ts ≤
      200 * factorUnit p D q * ((SubexpTemplateProgram.encodeGroup (ts.map SubexpTemplateData.rawTerm)).length + 1) := by
  let F := factorUnit p D q
  have hF : 1 ≤ F := factorUnit_pos p D q
  have hl := encoded_map_le (fun t => SubexpTemplateProgram.encodeTerm (SubexpTemplateData.rawTerm t))
    (fun t => SubexpMomentSourceProgram.encodeTerm (SubexpTemplateData.preparedTerm ctx source target minusOne base t)) ts F hF
    (fun t ht => (term_bounds ctx source target minusOne hc base q t (hq t ht)).1)
  have hout : (SubexpTemplateGroups.groupOutput ctx source target minusOne base ts).length + 1 ≤
      F * ((SubexpTemplateProgram.encodeGroup (ts.map SubexpTemplateData.rawTerm)).length + 1) := by
    simpa only [SubexpTemplateGroups.groupOutput, SubexpMomentSourceProgram.encodeGroup, SubexpTemplateProgram.encodeGroup,
      SubexpBlueprintRows.encodeList_map] using hl
  have hs := scan_le (fun t => SubexpTemplateProgram.encodeTerm (SubexpTemplateData.rawTerm t))
    (SubexpTemplateData.termCost ctx source target minusOne base) ts (100*F)
    (fun t ht => (term_bounds ctx source target minusOne hc base q t (hq t ht)).2)
  have hi : (SubexpTemplateProgram.encodeGroup (ts.map SubexpTemplateData.rawTerm)).length + 1 =
      2 * (mass (fun t => SubexpTemplateProgram.encodeTerm (SubexpTemplateData.rawTerm t)) ts + 1) := by
    simpa only [SubexpTemplateProgram.encodeGroup, SubexpBlueprintRows.encodeList_map] using
      encoded_length (fun t => SubexpTemplateProgram.encodeTerm (SubexpTemplateData.rawTerm t)) ts
  refine ⟨hout, ?_⟩
  unfold SubexpTemplateGroups.groupCost
  change _ ≤ 200 * F * _
  nlinarith

attribute [local irreducible] SubexpTemplateData.preparedTerm SubexpTemplateData.preparedBlock
  SubexpTemplateGroups.groupOutput SubexpTemplateGroups.groupCost
  factorUnit coordinateUnit workUnit preparationUnit

theorem block_bounds (ctx : SubexpBlueprintFactor.Context) (source : Prepared p 0)
    (target : Prepared p D) (minusOne : SubexpQuarticRing.Word (baseWidth p (D+1)))
    (hc : SubexpTemplateData.ContextGood ctx source target minusOne)
    (q : ℕ) (b : SubexpTemplateData.Block p D) (hq : BlockBound q b) :
    (SubexpTemplateBlocks.output ctx source target minusOne b).length + 1 ≤
      factorUnit p D q * ((SubexpTemplateProgram.encodeBlock (SubexpTemplateData.rawBlock b)).length + 1) ∧
    SubexpTemplateBlocks.cost ctx source target minusOne b ≤
      300 * factorUnit p D q * ((SubexpTemplateProgram.encodeBlock (SubexpTemplateData.rawBlock b)).length + 1) := by
  let F := factorUnit p D q
  have hF : 1 ≤ F := factorUnit_pos p D q
  have groupLength (ts : List (SubexpTemplateData.Term p D)) (ht : ts ∈ b.groups) :
      (SubexpTemplateGroups.groupOutput ctx source target minusOne b.base ts).length + 1 ≤
        F * ((SubexpTemplateProgram.encodeGroup (ts.map SubexpTemplateData.rawTerm)).length + 1) := by
    have hg := group_bounds (p:=p) (D:=D) ctx source target minusOne hc b.base q ts (hq ts ht)
    exact hg.1
  have groupTime (ts : List (SubexpTemplateData.Term p D)) (ht : ts ∈ b.groups) :
      SubexpTemplateGroups.groupCost ctx source target minusOne b.base ts ≤
        200 * F * ((SubexpTemplateProgram.encodeGroup (ts.map SubexpTemplateData.rawTerm)).length + 1) := by
    have hg := group_bounds (p:=p) (D:=D) ctx source target minusOne hc b.base q ts (hq ts ht)
    exact hg.2
  have hl := encoded_map_le (fun ts => SubexpTemplateProgram.encodeGroup (ts.map SubexpTemplateData.rawTerm))
    (SubexpTemplateGroups.groupOutput ctx source target minusOne b.base) b.groups F hF groupLength
  have hs := scan_le (fun ts => SubexpTemplateProgram.encodeGroup (ts.map SubexpTemplateData.rawTerm))
    (SubexpTemplateGroups.groupCost ctx source target minusOne b.base) b.groups (200*F) groupTime
  have hi := encoded_length (fun ts => SubexpTemplateProgram.encodeGroup (ts.map SubexpTemplateData.rawTerm)) b.groups
  have he : (SubexpTemplateProgram.encodeBlock (SubexpTemplateData.rawBlock b)).length + 1 =
      2 * ((SubexpTemplateData.bankBytes b.base).length + (SubexpTemplateData.supportBytes b.support).length + 1) +
        (Encoding.encodeList (fun ts => SubexpTemplateProgram.encodeGroup (ts.map SubexpTemplateData.rawTerm)) b.groups).length + 1 := by
    simp only [SubexpTemplateProgram.encodeBlock, SubexpTemplateData.rawBlock, SubexpBlueprintRows.encodeList_map, List.length_append, Encoding.length_frame]
    omega
  have ho : (SubexpTemplateBlocks.output ctx source target minusOne b).length + 1 =
      2 * ((SubexpTemplateData.bankBytes b.base).length + (SubexpTemplateData.supportBytes b.support).length + 1) +
        (Encoding.encodeList (SubexpTemplateGroups.groupOutput ctx source target minusOne b.base) b.groups).length + 1 := by
    simp only [SubexpTemplateBlocks.output, SubexpMomentSourceProgram.encodeBlock, SubexpTemplateData.preparedBlock,
      SubexpMomentSourceProgram.encodeDescriptor, SubexpBlueprintRows.encodeList_map,
      List.length_append, Encoding.length_frame]
    unfold SubexpTemplateGroups.groupOutput
    omega
  have hout : (SubexpTemplateBlocks.output ctx source target minusOne b).length + 1 ≤
      F * ((SubexpTemplateProgram.encodeBlock (SubexpTemplateData.rawBlock b)).length + 1) := by nlinarith
  refine ⟨hout, ?_⟩
  unfold SubexpTemplateBlocks.cost
  change _ ≤ 300 * F * _
  nlinarith

/-- Closed numerical bound on the measured program, linear in the raw bytes. -/
theorem execution_bounds (ctx : SubexpBlueprintFactor.Context) (source : Prepared p 0)
    (target : Prepared p D) (minusOne : SubexpQuarticRing.Word (baseWidth p (D+1)))
    (hc : SubexpTemplateData.ContextGood ctx source target minusOne)
    (q : ℕ) (bs : List (SubexpTemplateData.Block p D)) (hq : TaylorBound q bs) :
    (SubexpTemplateExecution.output ctx source target minusOne bs).length + 1 ≤
      factorUnit p D q * (rawBytes bs + 1) ∧
    SubexpTemplateExecution.runCost ctx source target minusOne bs ≤
      400 * factorUnit p D q * (rawBytes bs + 1) := by
  let F := factorUnit p D q
  have hF : 1 ≤ F := factorUnit_pos p D q
  have hl := encoded_map_le (fun b => SubexpTemplateProgram.encodeBlock (SubexpTemplateData.rawBlock b))
    (SubexpTemplateBlocks.output ctx source target minusOne) bs F hF
    (fun b hb => (block_bounds ctx source target minusOne hc q b (hq b hb)).1)
  have hout : (SubexpTemplateExecution.output ctx source target minusOne bs).length + 1 ≤
      F * (rawBytes bs + 1) := by
    change (Encoding.encodeList (fun b => SubexpMomentSourceProgram.encodeBlock
      (SubexpTemplateData.preparedBlock ctx source target minusOne b)) bs).length + 1 ≤
        F * ((Encoding.encodeList (fun b =>
          SubexpTemplateProgram.encodeBlock (SubexpTemplateData.rawBlock b)) bs).length + 1) at hl
    simpa only [SubexpTemplateExecution.output, SubexpMomentSourceProgram.encodeTemplate,
      SubexpTemplateProgram.encodeBlocks, rawBytes, SubexpBlueprintRows.encodeList_map] using hl
  have hs := scan_le (fun b => SubexpTemplateProgram.encodeBlock (SubexpTemplateData.rawBlock b))
    (SubexpTemplateBlocks.cost ctx source target minusOne) bs (300*F)
    (fun b hb => (block_bounds ctx source target minusOne hc q b (hq b hb)).2)
  have hi : rawBytes bs + 1 = 2 * (mass (fun b => SubexpTemplateProgram.encodeBlock (SubexpTemplateData.rawBlock b)) bs + 1) := by
    simpa only [rawBytes, SubexpTemplateProgram.encodeBlocks, SubexpBlueprintRows.encodeList_map] using
      encoded_length (fun b => SubexpTemplateProgram.encodeBlock (SubexpTemplateData.rawBlock b)) bs
  refine ⟨hout, ?_⟩
  unfold SubexpTemplateExecution.runCost
  change _ ≤ 400 * F * _
  nlinarith

/-- Dimension, source/target word widths, serialized key width, and Taylor depth. -/
def scale (p D q : ℕ) : ℕ :=
  D + baseWidth p 1 + baseWidth p (D+1) + SubexpSymbolicCost.indexBits D + q + 3

theorem workUnit_polynomial (p D q : ℕ) :
    workUnit p D q ≤ 500000 * (scale p D q)^4 := by
  let S := scale p D q
  have hS : 1 ≤ S := by dsimp [S, scale]; omega
  have hD : D + 2 ≤ S := by dsimp [S, scale]; omega
  have hb : baseWidth p 1 + 2 ≤ S := by dsimp [S, scale]; omega
  have hB : baseWidth p (D+1) + 1 ≤ S := by dsimp [S, scale]; omega
  have hI : SubexpSymbolicCost.indexBits D ≤ S := by dsimp [S, scale]; omega
  have hq : q ≤ S := by dsimp [S, scale]; omega
  have h12 : S ≤ S^2 := by nlinarith
  have h24 : S^2 ≤ S^4 := Nat.pow_le_pow_right hS (by decide)
  have h34 : S^3 ≤ S^4 := Nat.pow_le_pow_right hS (by decide)
  have h14 : S ≤ S^4 := h12.trans h24
  have hmain : (D+2)^2 * (baseWidth p 1+2)^2 ≤ S^4 := by
    calc
      _ ≤ S^2 * S^2 := Nat.mul_le_mul (Nat.pow_le_pow_left hD 2) (Nat.pow_le_pow_left hb 2)
      _ = _ := by ring
  have hDB : D * (8 * baseWidth p 1 + 2) ≤ 10 * S^2 := by
    calc
      _ ≤ S * (10*S) := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have hbeta : betaBound p D ≤ 430115*S^4 := by
    unfold betaBound
    nlinarith only [hmain, hDB, hb, hS, h12, h24, h14]
  have hkey : 33*(D+q)+32*SubexpSymbolicCost.indexBits D+275 ≤ 373*S := by omega
  have hcacheProduct : D*q*(33*(D+q)+32*SubexpSymbolicCost.indexBits D+275) ≤ 373*S^3 := by
    calc
      _ ≤ (S*S)*(373*S) := Nat.mul_le_mul (Nat.mul_le_mul (by omega) hq) hkey
      _ = _ := by ring
  have h13 : S ≤ S^3 := h12.trans (Nat.pow_le_pow_right hS (by decide))
  have hcache : cacheBound p D q ≤ 2000*S^3 := by
    unfold cacheBound
    nlinarith only [hcacheProduct, hB, hD, hI, hS, h13]
  have hpoint : SubexpPointBank.steps D (baseWidth p 1) ≤ 15000*S^3 := by
    apply (SubexpPointBank.steps_polynomial D (baseWidth p 1)).trans
    calc
      _ ≤ 15000*S*S^2 := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega))
        (Nat.pow_le_pow_left (by omega) 2)
      _ = _ := by ring
  have hneg : 25000*(baseWidth p (D+1)+1)^2 ≤ 25000*S^2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hB 2)
  change workUnit p D q ≤ 500000*S^4
  unfold workUnit
  nlinarith only [hbeta, hcache, hpoint, hneg, hS, h24, h34, h14]

theorem factorUnit_polynomial (p D q : ℕ) :
    400 * factorUnit p D q ≤ 10^20 * (scale p D q)^5 := by
  let S := scale p D q
  have hJ : preparationUnit D ≤ 1000*S := by
    unfold preparationUnit
    apply Nat.mul_le_mul_left
    dsimp [S, scale]
    omega
  have hW : workUnit p D q ≤ 500000*S^4 := workUnit_polynomial p D q
  calc
    400 * factorUnit p D q = 40000000 * (preparationUnit D * workUnit p D q) := by
      unfold factorUnit coordinateUnit
      ring
    _ ≤ 40000000 * ((1000*S) * (500000*S^4)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul hJ hW)
    _ = 20000000000000000*S^5 := by ring
    _ ≤ 10^20*S^5 := Nat.mul_le_mul_right _ (by norm_num)

/-- The real template controller's time bound; raw bytes remain a linear factor. -/
theorem runCost_le (ctx : SubexpBlueprintFactor.Context) (source : Prepared p 0)
    (target : Prepared p D) (minusOne : SubexpQuarticRing.Word (baseWidth p (D+1)))
    (hc : SubexpTemplateData.ContextGood ctx source target minusOne)
    (q : ℕ) (bs : List (SubexpTemplateData.Block p D)) (hq : TaylorBound q bs) :
    SubexpTemplateExecution.runCost ctx source target minusOne bs ≤
      10^20 * (scale p D q)^5 * (rawBytes bs + 1) :=
  (execution_bounds ctx source target minusOne hc q bs hq).2.trans
    (Nat.mul_le_mul_right _ (factorUnit_polynomial p D q))

/-- Every generated byte is bounded from input bytes and explicit shape data. -/
theorem output_length_le (ctx : SubexpBlueprintFactor.Context) (source : Prepared p 0)
    (target : Prepared p D) (minusOne : SubexpQuarticRing.Word (baseWidth p (D+1)))
    (hc : SubexpTemplateData.ContextGood ctx source target minusOne)
    (q : ℕ) (bs : List (SubexpTemplateData.Block p D)) (hq : TaylorBound q bs) :
    (SubexpTemplateExecution.output ctx source target minusOne bs).length ≤
      10^20 * (scale p D q)^5 * (rawBytes bs + 1) := by
  have h := (execution_bounds ctx source target minusOne hc q bs hq).1
  have hp := Nat.mul_le_mul_right (rawBytes bs + 1) (factorUnit_polynomial p D q)
  nlinarith

/-- Actual finite-program execution at the polynomial bound, with the same
input masters, output bytes, and cleared workspace as the execution theorem. -/
theorem program_runsIn_polynomial (ctx : SubexpBlueprintFactor.Context) (source : Prepared p 0)
    (target : Prepared p D) (minusOne : SubexpQuarticRing.Word (baseWidth p (D+1)))
    (hc : SubexpTemplateData.ContextGood ctx source target minusOne)
    (q : ℕ) (bs : List (SubexpTemplateData.Block p D)) (hq : TaylorBound q bs) (regs : Fin 8 → Bool) :
    ∃ rf, RunsIn SubexpTemplateProgram.program (10^20 * (scale p D q)^5 * (rawBytes bs + 1))
      ((SubexpTemplateProgram.serviceState ctx regs (SubexpTemplateProgram.encodeBlocks (bs.map SubexpTemplateData.rawBlock))).withPC (some SubexpTemplateProgram.program.entry))
      ((SubexpTemplateProgram.state ctx rf {output:=SubexpTemplateExecution.output ctx source target minusOne bs}).withPC none) := by
  obtain ⟨rf,n,hn,ht⟩ := SubexpTemplateExecution.program_runsIn ctx source target minusOne hc bs regs
  exact ⟨rf,n,hn.trans (runCost_le ctx source target minusOne hc q bs hq),ht⟩

/-- The machine compiler has a fixed overhead, independent of all runtime data. -/
theorem primitive_execution_polynomial (ctx : SubexpBlueprintFactor.Context) (source : Prepared p 0)
    (target : Prepared p D) (minusOne : SubexpQuarticRing.Word (baseWidth p (D+1)))
    (hc : SubexpTemplateData.ContextGood ctx source target minusOne)
    (q : ℕ) (bs : List (SubexpTemplateData.Block p D)) (hq : TaylorBound q bs) (regs : Fin 8 → Bool) :
    ∃ rf, Computation.RunsIn (BitProgram.primitive SubexpTemplateProgram.program).step
      (primitiveOverhead SubexpTemplateProgram.program * (10^20 * (scale p D q)^5 * (rawBytes bs + 1)))
      (primitiveCfg SubexpTemplateProgram.program
        ((SubexpTemplateProgram.serviceState ctx regs (SubexpTemplateProgram.encodeBlocks (bs.map SubexpTemplateData.rawBlock))).withPC (some SubexpTemplateProgram.program.entry)))
      (primitiveCfg SubexpTemplateProgram.program
        ((SubexpTemplateProgram.state ctx rf {output:=SubexpTemplateExecution.output ctx source target minusOne bs}).withPC none)) := by
  obtain ⟨rf,h⟩ := program_runsIn_polynomial ctx source target minusOne hc q bs hq regs
  exact ⟨rf,BitProgram.primitive_execution SubexpTemplateProgram.program h⟩

end SubexponentialSAT.SubexpTemplateCostBounds

end OAI.Algorithms
