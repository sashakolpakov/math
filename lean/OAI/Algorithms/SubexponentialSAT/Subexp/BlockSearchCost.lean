import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchOuter

namespace OAI.Algorithms

/-! Quantitative bounds for the actual universal-block search loops. -/

namespace SubexponentialSAT.Subexp.BlockSearchCost

open BlockSearchNested BlockSearchOuter

theorem sum_lengths_le (records : List (List Bool)) (width : ℕ)
    (hw : ∀ bits ∈ records, bits.length ≤ width) :
    (records.map List.length).sum ≤ records.length * width := by
  induction records with
  | nil => simp
  | cons bits records ih =>
      have hb := hw bits (by simp)
      have ht := ih (fun b h => hw b (by simp [h]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith

theorem encoded_length_le (records : List (List Bool)) (width : ℕ)
    (hw : ∀ bits ∈ records, bits.length ≤ width) :
    (ProgramEncoding.encodeRecords records).length ≤ records.length * (2 * width + 2) + 1 := by
  rw [ProgramEncoding.encodeRecords_length]
  have h := sum_lengths_le records width hw
  nlinarith

theorem budget_le (cost : List Bool → ℕ) (records : List (List Bool)) (width bound : ℕ)
    (hw : ∀ bits ∈ records, bits.length ≤ width)
    (hc : ∀ bits ∈ records, cost bits ≤ bound) :
    RecordPrograms.budget cost records ≤ records.length * (6 * width + bound + 7) := by
  induction records with
  | nil => simp [RecordPrograms.budget]
  | cons bits records ih =>
      have hb := hw bits (by simp)
      have hcb := hc bits (by simp)
      have ht := ih (fun b h => hw b (by simp [h])) (fun b h => hc b (by simp [h]))
      simp only [RecordPrograms.budget, List.length_cons]
      nlinarith

theorem coefficientScanCost_le (cost : List Bool → ℕ) (records : List (List Bool))
    (width bound : ℕ) (hw : ∀ bits ∈ records, bits.length ≤ width)
    (hc : ∀ bits ∈ records, cost bits ≤ bound) :
    coefficientScanCost cost records ≤ records.length * (24 * width + bound + 27) + 23 := by
  have he := encoded_length_le records width hw
  have hb := budget_le (fun bits => cost bits + 2) records width (bound + 2)
    hw (fun bits h => Nat.add_le_add_right (hc bits h) 2)
  unfold coefficientScanCost
  calc
    _ ≤ 9 * (records.length * (2 * width + 2) + 1) +
        records.length * (6 * width + (bound + 2) + 7) + 14 := by omega
    _ = _ := by ring

theorem dimensionCost_le (limit width bound : ℕ) (cost : List Bool → ℕ)
    (records : List (List Bool)) (split : List Bool)
    (hs : split.length ≤ limit) (hw : ∀ bits ∈ records, bits.length ≤ width)
    (hc : ∀ bits ∈ records, cost bits ≤ bound) :
    dimensionCost limit cost records split ≤
      records.length * (24 * width + bound + 27) + 11 * limit + 37 := by
  have h := coefficientScanCost_le cost records width bound hw hc
  unfold dimensionCost
  omega

theorem dimensionScanCost_le (limit width bound : ℕ)
    (cost : List Bool → List Bool → ℕ) (coefficients dimensions : List (List Bool))
    (hd : ∀ split ∈ dimensions, split.length ≤ limit)
    (hw : ∀ bits ∈ coefficients, bits.length ≤ width)
    (hc : ∀ split ∈ dimensions, ∀ bits ∈ coefficients, cost split bits ≤ bound) :
    dimensionScanCost limit cost coefficients dimensions ≤
      dimensions.length *
        (coefficients.length * (24 * width + bound + 27) + 35 * limit + 62) + 21 := by
  have he := encoded_length_le dimensions limit hd
  have hb := budget_le (fun split => dimensionCost limit (cost split) coefficients split)
    dimensions limit (coefficients.length * (24 * width + bound + 27) + 11 * limit + 37)
    hd (fun split h => dimensionCost_le limit width bound (cost split) coefficients split
      (hd split h) hw (hc split h))
  unfold dimensionScanCost
  calc
    _ ≤ 9 * (dimensions.length * (2 * limit + 2) + 1) +
        dimensions.length * (6 * limit +
          (coefficients.length * (24 * width + bound + 27) + 11 * limit + 37) + 7) + 12 := by
      omega
    _ = _ := by ring

theorem tableCost_le (limit tableWidth coefficientWidth bound : ℕ)
    (cost : List Bool → List Bool → ℕ) (coefficients dimensions : List (List Bool))
    (table : List Bool) (ht : table.length ≤ tableWidth)
    (hd : ∀ split ∈ dimensions, split.length ≤ limit)
    (hw : ∀ bits ∈ coefficients, bits.length ≤ coefficientWidth)
    (hc : ∀ split ∈ dimensions, ∀ bits ∈ coefficients, cost split bits ≤ bound) :
    tableCost tableWidth limit cost coefficients dimensions table ≤
      dimensions.length * (coefficients.length * (24 * coefficientWidth + bound + 27) +
        35 * limit + 62) + 5 * tableWidth + 30 := by
  have h := dimensionScanCost_le limit coefficientWidth bound cost coefficients dimensions hd hw hc
  unfold tableCost
  omega

/-- The three-loop instruction count is the number of tables times the
number of splits times the number of coefficients, times a local polynomial.
No ambient/global dimension occurs in this bound. -/
theorem searchCost_le (limit tableWidth coefficientWidth bound : ℕ)
    (cost : List Bool → List Bool → List Bool → ℕ)
    (coefficients dimensions tables : List (List Bool))
    (ht : ∀ table ∈ tables, table.length ≤ tableWidth)
    (hd : ∀ split ∈ dimensions, split.length ≤ limit)
    (hw : ∀ bits ∈ coefficients, bits.length ≤ coefficientWidth)
    (hc : ∀ table ∈ tables, ∀ split ∈ dimensions, ∀ bits ∈ coefficients,
      cost table split bits ≤ bound) :
    searchCost limit tableWidth cost coefficients dimensions tables ≤
      tables.length * (dimensions.length *
        (coefficients.length * (24 * coefficientWidth + bound + 27) + 35 * limit + 62) +
        15 * tableWidth + 41) + 8 := by
  have he := encoded_length_le tables tableWidth ht
  have hb := budget_le
    (fun table => tableCost tableWidth limit (cost table) coefficients dimensions table)
    tables tableWidth
    (dimensions.length * (coefficients.length * (24 * coefficientWidth + bound + 27) +
      35 * limit + 62) + 5 * tableWidth + 30)
    ht (fun table h => tableCost_le limit tableWidth coefficientWidth bound (cost table)
      coefficients dimensions table (ht table h) hd hw (hc table h))
  unfold searchCost
  calc
    _ ≤ tables.length * (6 * tableWidth +
        (dimensions.length * (coefficients.length * (24 * coefficientWidth + bound + 27) +
          35 * limit + 62) + 5 * tableWidth + 30) + 7) +
        2 * (tables.length * (2 * tableWidth + 2) + 1) + 6 := by omega
    _ = _ := by ring

end SubexponentialSAT.Subexp.BlockSearchCost

end OAI.Algorithms
