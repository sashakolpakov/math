import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.TypeFiberProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstraintMatrixSizeBasics
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryBudgetBounds

namespace OAI.Algorithms

/-! Polynomial bounds for the actual framed-record filter used to construct
each Joint list. All record frames, index construction and final reversal are
included in the source budget. -/

namespace SubexponentialSAT.Subexp.TypeFiberBudgetBounds

open MulticolorTypes

theorem record_budget_eq (records : List (List Bool)) (index width : ℕ)
    (hwidth : ∀ bits ∈ records, bits.length = width) :
    RecordPrograms.budget (TypeBitFilter.callbackCost index) records =
      records.length * (26 * width + 12 * index + 47) := by
  induction records with
  | nil => simp [RecordPrograms.budget]
  | cons bits records ih =>
      have hb := hwidth bits (by simp)
      have ht := ih (fun b h => hwidth b (List.mem_cons_of_mem _ h))
      simp only [RecordPrograms.budget, TypeBitFilter.callbackCost, hb, ht,
        List.length_cons]
      ring

theorem filter_reverse_encoded_le (records : List (List Bool))
    (test : List Bool → Bool) (width : ℕ)
    (hwidth : ∀ bits ∈ records, bits.length = width) :
    (ProgramEncoding.encodeRecords (records.filter test).reverse).length ≤
      records.length * (2 * width + 2) + 1 := by
  have hw : ∀ bits ∈ (records.filter test).reverse, bits.length = width := by
    intro bits hb
    have hm : bits ∈ records.filter test := by simpa only [List.mem_reverse] using hb
    exact hwidth bits (List.mem_filter.mp hm).1
  rw [ConstraintMatrixSizeBasics.encodeRecords_length_of_uniform _ width hw,
    List.length_reverse]
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_right _ (List.length_filter_le test records)) 1

theorem bit_filter_budget_le (keep : Bool) (records : List (List Bool))
    (index width : ℕ) (hwidth : ∀ bits ∈ records, bits.length = width) :
    TypeBitFilter.budget keep records index ≤
      records.length * (60 * width + 12 * index + 81) + 30 := by
  have hf := filter_reverse_encoded_le records (TypeBitFilter.test keep index) width hwidth
  rw [TypeBitFilter.budget, record_budget_eq records index width hwidth,
    ConstraintMatrixSizeBasics.encodeRecords_length_of_uniform records width hwidth]
  calc
    _ ≤ 7 * (records.length * (2 * width + 2) + 1) +
        records.length * (26 * width + 12 * index + 47) +
        10 * (records.length * (2 * width + 2) + 1) + 13 := by omega
    _ = _ := by ring

variable {r Q Δ : ℕ}

theorem slotIndex_le {U : ℕ} (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (hr : r ≤ U) (hQ : Q ≤ U) (hΔ : Δ ≤ U) :
    TypeEnumeration.slotIndex r (Q * r) t.val g.val i.val ≤ 3 * (U + 1)^3 := by
  let s := U + 1
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hs2 : s ≤ s^2 := by nlinarith
  have hs3 : s^2 ≤ s^3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hi : i.val + 1 ≤ s := by have := i.isLt; dsimp [s]; omega
  have ht : t.val ≤ s := by have := t.isLt; dsimp [s]; omega
  have hg : g.val ≤ s := by have := g.isLt; dsimp [s]; omega
  change _ ≤ 3 * s^3
  calc
    _ ≤ s * (s * s) + (s * s + s) := by
      unfold TypeEnumeration.slotIndex TypeEnumeration.headIndex
      gcongr <;> dsimp [s] at * <;> omega
    _ ≤ _ := by nlinarith only [hs2, hs3]

theorem joint_prepareCost_le {U : ℕ} (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (hr : r ≤ U) (hQ : Q ≤ U) (hΔ : Δ ≤ U) :
    TypeIndexProgram.jointCost r (Q * r) t.val g.val i.val ≤ 100 * (U + 1)^3 := by
  let s := U + 1
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hs2 : s ≤ s^2 := by nlinarith
  have hs3 : s^2 ≤ s^3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hi : i.val + 1 ≤ s := by have := i.isLt; dsimp [s]; omega
  have ht : t.val ≤ s := by have := t.isLt; dsimp [s]; omega
  have hg : g.val ≤ s := by have := g.isLt; dsimp [s]; omega
  change _ ≤ 100 * s^3
  calc
    _ ≤ (7 * s + 7 * s + s * (7 * s + 7) + 16) +
        (7 * s + 5 + (2 + (s * (7 * (s * s) + 7) + 6))) := by
      unfold TypeIndexProgram.jointCost TypeIndexProgram.headCost
      gcongr <;> dsimp [s] at * <;> omega
    _ ≤ _ := by nlinarith only [hs, hs2, hs3]

theorem joint_budget_le (hr : 0 < r) (hQ : 0 < Q)
    (i : Fin Δ) (t : Fin Q) (g : Fin r) (U : ℕ)
    (hrU : r ≤ U) (hQU : Q ≤ U) (hΔU : Δ ≤ U)
    (hN : (TypeEnumeration.sideList (Δ := Δ) hr hQ t g).length ≤ U) :
    TypeFiberProgram.budget true ⟨r, t.val, g.val, Q * r, i.val⟩
      (TypeEnumeration.sideBytes r Q Δ t.val g.val) ≤ 1000 * (U + 1)^4 := by
  let s := U + 1
  let records := TypeEnumeration.sideBytes r Q Δ t.val g.val
  let index := TypeEnumeration.slotIndex r (Q * r) t.val g.val i.val
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hs2 : s ≤ s^2 := by nlinarith
  have hs3 : s^2 ≤ s^3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hs4 : s^3 ≤ s^4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hcount : records.length ≤ s := by
    dsimp [records]
    rw [← TypeEnumeration.sideList_bytes hr hQ t g, List.length_map]
    dsimp [s]; omega
  have htype := MatrixEntryBudgetBounds.typeWidth_le hrU hQU hΔU
  change CollisionProgram.typeWidth r Q Δ ≤ s^3 at htype
  have hoff := slotIndex_le i t g hrU hQU hΔU
  change index ≤ 3 * s^3 at hoff
  have hprep := joint_prepareCost_le i t g hrU hQU hΔU
  change TypeIndexProgram.jointCost r (Q*r) t.val g.val i.val ≤ 100*s^3 at hprep
  have hf := bit_filter_budget_le false records index (CollisionProgram.typeWidth r Q Δ)
    (ConstraintMatrixSizeBasics.sideBytes_width hr hQ t g)
  have hf' : TypeBitFilter.budget false records index ≤
      s * (60 * s^3 + 12 * (3 * s^3) + 81) + 30 := by
    apply hf.trans
    gcongr
  change TypeIndexProgram.jointCost r (Q*r) t.val g.val i.val +
    TypeBitFilter.budget false records index + 2 * index + 4 ≤ 1000 * s^4
  nlinarith only [hprep, hf', hoff, hs, hs2, hs3, hs4]

end SubexponentialSAT.Subexp.TypeFiberBudgetBounds

end OAI.Algorithms
