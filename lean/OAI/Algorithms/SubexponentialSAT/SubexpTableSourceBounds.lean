import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTableSourceExecution
import OAI.Algorithms.SubexponentialSAT.SubexpTemplateCostBounds

namespace OAI.Algorithms

/-!
# Quadratic byte bounds for the actual Horner/table source constructor

Horner repeats its input once per coefficient. The product of input length
and coefficient count is charged here; no bounded-degree or output-size
premise is imposed on the supplied table.
-/

namespace SubexponentialSAT.SubexpTableSourceBounds

open BitProgram StructuredCalls SubexpTemplateCostBounds

abbrev Bits := List Bool

theorem mass_count_le {α : Type*} (enc : α → Bits) (xs : List α) :
    xs.length ≤ mass enc xs := by
  induction xs with
  | nil => simp [mass]
  | cons x xs ih =>
      simp only [mass, List.map_cons, List.sum_cons, List.length_cons] at *
      omega

/-- The sum of local quadratic costs is bounded by the square of total
encoded mass. Every occurrence is counted, including duplicate records. -/
theorem sum_le_square_mass {α : Type*} (enc : α → Bits) (f : α → ℕ)
    (xs : List α) (K : ℕ)
    (h : ∀ x ∈ xs, f x ≤ K * ((enc x).length + 1)^2) :
    (xs.map f).sum ≤ K * (mass enc xs)^2 := by
  induction xs with
  | nil => simp [mass]
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      have hs : ((enc x).length + 1)^2 + (mass enc xs)^2 ≤
          ((enc x).length + 1 + mass enc xs)^2 := by
        nlinarith only [Nat.zero_le (((enc x).length + 1) * mass enc xs)]
      calc
        ((x :: xs).map f).sum ≤ K * (((enc x).length + 1)^2 + (mass enc xs)^2) := by
          simp only [List.map_cons, List.sum_cons]
          nlinarith only [hx, ht]
        _ ≤ K * ((enc x).length + 1 + mass enc xs)^2 := Nat.mul_le_mul_left K hs
        _ = K * (mass enc (x :: xs))^2 := rfl

theorem encoded_map_square {α : Type*} (enc out : α → Bits) (xs : List α) (K : ℕ)
    (hK : 1 ≤ K)
    (h : ∀ x ∈ xs, (out x).length + 1 ≤ K * ((enc x).length + 1)^2) :
    (Encoding.encodeList out xs).length + 1 ≤
      K * ((Encoding.encodeList enc xs).length + 1)^2 := by
  have hs := sum_le_square_mass enc (fun x => (out x).length + 1) xs K h
  change mass out xs ≤ K * (mass enc xs)^2 at hs
  rw [encoded_length, encoded_length]
  nlinarith only [hs, hK, Nat.zero_le (K * (mass enc xs)^2),
    Nat.zero_le (K * mass enc xs)]

theorem scan_square {α : Type*} (enc : α → Bits) (f : α → ℕ) (xs : List α) (K : ℕ)
    (h : ∀ x ∈ xs, f x ≤ K * ((enc x).length + 1)^2) :
    SubexpTableSource.scanCost enc f xs ≤ (K + 11) * (mass enc xs)^2 := by
  apply sum_le_square_mass
  intro x hx
  have hh := h x hx
  nlinarith

/-- The exact output formula is dominated by its measured Horner execution. -/
theorem horner_length_le_cost (x zero : Bits) (coefficients : List Bits) :
    (SubexpHornerSource.source x zero coefficients).length ≤
      SubexpHornerSource.runCost x zero coefficients := by
  rw [SubexpHornerSource.source_length]
  unfold SubexpHornerSource.runCost
  nlinarith only [Nat.zero_le ((coefficients.map List.length).sum),
    Nat.zero_le (x.length * coefficients.length), Nat.zero_le coefficients.length,
    Nat.zero_le zero.length]

theorem coordinate_size (c : SubexpTableSource.Coordinate) :
    (SubexpTableSource.encodeCoordinate c).length + 1 =
      2 * c.input.length + 2 * (c.coefficients.map List.length).sum +
        2 * c.coefficients.length + 3 := by
  simp only [SubexpTableSource.encodeCoordinate, List.length_append, Encoding.length_frame,
    Subexp.FactorBlueprint.encodeList_length, id_eq]
  change 2 * c.input.length + 1 +
    (2 * (c.coefficients.map List.length).sum + 2 * c.coefficients.length + 1) + 1 = _
  omega

/-- The quadratic term pays for input-length times coefficient-count. -/
theorem horner_cost_le (zero one : Bits) (c : SubexpTableSource.Coordinate) :
    SubexpHornerSource.runCost c.input zero c.coefficients ≤
      128 * (zero.length + one.length + 1) *
        ((SubexpTableSource.encodeCoordinate c).length + 1)^2 := by
  let N := (SubexpTableSource.encodeCoordinate c).length + 1
  let H := zero.length + one.length + 1
  have he := coordinate_size c
  change N = _ at he
  have hN : 1 ≤ N := by omega
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hx : c.input.length ≤ N := by omega
  have hc : c.coefficients.length ≤ N := by omega
  have hs : (c.coefficients.map List.length).sum ≤ N := by omega
  have hp : c.input.length * c.coefficients.length ≤ N^2 := by
    simpa only [pow_two] using Nat.mul_le_mul hx hc
  have hN2 : N ≤ N^2 := by nlinarith only [hN]
  have hHN : H ≤ H * N^2 := by nlinarith only [hN, hN2]
  have hNH : N^2 ≤ H * N^2 := by nlinarith only [hH]
  have hz : 14 * zero.length + 24 ≤ 38 * H := by dsimp [H]; omega
  unfold SubexpHornerSource.runCost
  change _ ≤ 128 * H * N^2
  nlinarith only [hp, hs, hc, hN2, hHN, hNH, hz]

theorem coordinateCost_le (zero one : Bits) (c : SubexpTableSource.Coordinate) :
    SubexpTableSource.coordinateCost zero c ≤
      600 * (zero.length + one.length + 1) *
        ((SubexpTableSource.encodeCoordinate c).length + 1)^2 := by
  have hh := horner_cost_le zero one c
  have hl := horner_length_le_cost c.input zero c.coefficients
  have he := coordinate_size c
  let N := (SubexpTableSource.encodeCoordinate c).length + 1
  let H := zero.length + one.length + 1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hN2 : N ≤ N^2 := by nlinarith only [hN]
  have hx : c.input.length ≤ N := by dsimp [N]; omega
  have hNH : N^2 ≤ H * N^2 := by nlinarith only [hH]
  unfold SubexpTableSource.coordinateCost SubexpTableSource.coordinateCode
  change _ ≤ 600 * H * N^2
  change _ ≤ 128 * H * N^2 at hh
  nlinarith only [hh, hl, hx, hN2, hNH, hN]

theorem rowCost_le (zero one : Bits) (r : SubexpTableSource.Row) :
    SubexpTableSource.rowCost zero one r ≤
      700 * (zero.length + one.length + 1) *
        ((SubexpTableSource.encodeRow r).length + 1)^2 := by
  let N := (SubexpTableSource.encodeRow r).length + 1
  let H := zero.length + one.length + 1
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hl := table_row_length r
  have he := encoded_length SubexpTableSource.encodeCoordinate r.coordinates
  have hc := mass_count_le SubexpTableSource.encodeCoordinate r.coordinates
  have hv : r.value.length ≤ N := by dsimp [N]; omega
  have hm : mass SubexpTableSource.encodeCoordinate r.coordinates ≤ N := by dsimp [N]; omega
  have hcount : r.coordinates.length ≤ N := hc.trans hm
  have hs := scan_square SubexpTableSource.encodeCoordinate
    (SubexpTableSource.coordinateCost zero) r.coordinates (600 * H)
    (fun c _ => coordinateCost_le zero one c)
  have hscan : SubexpTableSource.scanCost SubexpTableSource.encodeCoordinate
      (SubexpTableSource.coordinateCost zero) r.coordinates ≤ 611 * H * N^2 := by
    apply hs.trans
    apply Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hm 2)
  have hN2 : N ≤ N^2 := by nlinarith only [hN]
  have hHN : H ≤ H * N^2 := by nlinarith only [hN, hN2]
  have hNH : N^2 ≤ H * N^2 := by nlinarith only [hH]
  have hone : 8 * one.length + 29 ≤ 37 * H := by dsimp [H]; omega
  unfold SubexpTableSource.rowCost
  change _ ≤ 700 * H * N^2
  nlinarith only [hscan, hv, hcount, hN2, hHN, hNH, hone]

/-- Unrestricted prepared tables have quadratic, rather than linear, cost. -/
theorem tableCost_le (zero one : Bits) (rows : List SubexpTableSource.Row) :
    SubexpTableSource.tableCost zero one rows ≤
      1000 * (zero.length + one.length + 1) *
        ((SubexpTableSource.encodeRows rows).length + 1)^2 := by
  let N := (SubexpTableSource.encodeRows rows).length + 1
  let H := zero.length + one.length + 1
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hN : 1 ≤ N := by dsimp [N]; omega
  have he := encoded_length SubexpTableSource.encodeRow rows
  have hc := mass_count_le SubexpTableSource.encodeRow rows
  have hm : mass SubexpTableSource.encodeRow rows ≤ N := by
    dsimp [N, SubexpTableSource.encodeRows]
    omega
  have hcount : rows.length ≤ N := hc.trans hm
  have hs := scan_square SubexpTableSource.encodeRow (SubexpTableSource.rowCost zero one)
    rows (700 * H) (fun r _ => rowCost_le zero one r)
  have hscan : SubexpTableSource.scanCost SubexpTableSource.encodeRow
      (SubexpTableSource.rowCost zero one) rows ≤ 711 * H * N^2 := by
    apply hs.trans
    apply Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hm 2)
  have hN2 : N ≤ N^2 := by nlinarith only [hN]
  have hHN : H ≤ H * N^2 := by nlinarith only [hN, hN2]
  have hNH : N^2 ≤ H * N^2 := by nlinarith only [hH]
  have hz : 8 * zero.length + 16 ≤ 24 * H := by dsimp [H]; omega
  unfold SubexpTableSource.tableCost
  change _ ≤ 1000 * H * N^2
  nlinarith only [hscan, hcount, hN2, hHN, hNH, hz]

/-- The actual table emitter starts with an empty output stack. -/
theorem tableCode_length_le_cost (zero one : Bits) (rows : List SubexpTableSource.Row) :
    (SubexpTableSource.tableCode zero one rows).length ≤
      SubexpTableSource.tableCost zero one rows := by
  have h := SubexpTableSource.table_eval rows false false [] zero one
    SubexpTableSource.emptyAccumulator rfl rfl rfl
  have hh := eval_output_le 3 h
  change ((SubexpTableSource.tableCode zero one rows).reverse ++ []).length ≤
    [].length + SubexpTableSource.tableCost zero one rows at hh
  simpa only [List.length_append, List.length_reverse, List.length_nil, Nat.add_zero,
    Nat.zero_add] using hh

theorem tableCode_length_le (zero one : Bits) (rows : List SubexpTableSource.Row) :
    (SubexpTableSource.tableCode zero one rows).length ≤
      1000 * (zero.length + one.length + 1) *
        ((SubexpTableSource.encodeRows rows).length + 1)^2 :=
  (tableCode_length_le_cost zero one rows).trans (tableCost_le zero one rows)

theorem constructorCost_le (zero one : Bits) (rows : List SubexpTableSource.Row) :
    SubexpTableSource.tableCost zero one rows +
        3 * (SubexpTableSource.tableCode zero one rows).length + 6 ≤
      5000 * (zero.length + one.length + 1) *
        ((SubexpTableSource.encodeRows rows).length + 1)^2 := by
  have ht := tableCost_le zero one rows
  have hl := tableCode_length_le zero one rows
  have hN : 1 ≤ (SubexpTableSource.encodeRows rows).length + 1 := by omega
  have hH : 1 ≤ zero.length + one.length + 1 := by omega
  have hp : 1 ≤ (zero.length + one.length + 1) *
      ((SubexpTableSource.encodeRows rows).length + 1)^2 := by
    exact Nat.mul_pos hH (Nat.one_le_pow _ _ hN)
  nlinarith only [ht, hl, hp]

/-- The actual finite constructor preserves constants and clears its workspace. -/
theorem program_runsIn (zero one : Bits) (rows : List SubexpTableSource.Row) :
    RunsIn SubexpTableSource.program
      (5000 * (zero.length + one.length + 1) *
        ((SubexpTableSource.encodeRows rows).length + 1)^2)
      ((SubexpTableSource.serviceState (SubexpTableSource.encodeRows rows) zero one).withPC
        (some SubexpTableSource.program.entry))
      ((SubexpTableSource.serviceState (SubexpTableSource.tableCode zero one rows) zero one).withPC none) :=
  ⟨_, constructorCost_le zero one rows, SubexpTableSource.program_trace zero one rows⟩

end SubexponentialSAT.SubexpTableSourceBounds

end OAI.Algorithms
