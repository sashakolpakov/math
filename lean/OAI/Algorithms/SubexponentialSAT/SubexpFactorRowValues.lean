import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorRowStream
import OAI.Algorithms.SubexponentialSAT.SubexpRankedTable
import OAI.Algorithms.SubexponentialSAT.SubexpBasePValues

namespace OAI.Algorithms

/-! Numeric rank and exact ordered-table meaning of the generated row bytes. -/

namespace SubexponentialSAT.SubexpFactorRowStream

open SubexpBasePUnranking

def numericRow (modulus : Word) (k : ℕ) (zero one : Word)
    (rank : ℕ) (answer : Bool) : RawRow :=
  ⟨if answer then one else zero,
    (numericDigits (BinaryArithmetic.toNat modulus) k rank).map
      (SubexpLiftRing.fixedBits modulus.length)⟩

theorem row_eq_numeric (modulus rank : Word) (k : ℕ) (zero one : Word) (answer : Bool)
    (hm : 0 < BinaryArithmetic.toNat modulus) :
    row modulus k zero one rank answer =
      numericRow modulus k zero one (CounterPrograms.value rank) answer := by
  unfold row numericRow
  rw [SubexpBasePValues.digitWords_eq_numeric modulus rank k hm,
    CounterPrograms.value_eq_toNat]

theorem forwardRows_eq_numeric (modulus rank : Word) (k : ℕ) (zero one answers : Word)
    (hm : 0 < BinaryArithmetic.toNat modulus) :
    forwardRows modulus k zero one rank answers =
      (List.range' (CounterPrograms.value rank) answers.length).zipWith
        (numericRow modulus k zero one) answers := by
  induction answers generalizing rank with
  | nil => simp [forwardRows]
  | cons answer answers ih =>
      simp only [forwardRows, row_eq_numeric modulus rank k zero one answer hm, ih,
        CounterPrograms.value_increment, List.length_cons, List.range'_succ,
        List.zipWith_cons_cons]

theorem tableRows_eq_numeric (modulus : Word) (k : ℕ) (zero one answers : Word)
    (hm : 0 < BinaryArithmetic.toNat modulus) :
    tableRows modulus k zero one answers =
      (List.range answers.length).reverse.zipWith (numericRow modulus k zero one) answers := by
  rw [tableRows, forwardRows_eq_numeric modulus [] k zero one answers.reverse hm]
  rw [List.reverse_zipWith (by simp)]
  simp [List.range'_eq_map_range]

def rawOfTable {p k : ℕ} (width : ℕ) (r : SubexpTableInterpolation.Row p k Word) : RawRow :=
  ⟨r.value, r.labels.toList.map (fun d => SubexpLiftRing.fixedBits width d.val)⟩

private theorem zipWith_mapped {A B C D : Type*} (xs : List A) (ys : List B)
    (f : A → C) (g : C → B → D) :
    (xs.map f).zipWith g ys = xs.zipWith (fun x y => g (f x) y) ys := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih => cases ys <;> simp [ih]

theorem tableRows_eq_attachAnswers (modulus : Word) (p k : ℕ) (zero one answers : Word)
    (hp : BinaryArithmetic.toNat modulus = p) (hpos : 0 < p)
    (hlen : answers.length = p ^ k) :
    tableRows modulus k zero one answers =
      (SubexpRankedTable.attachAnswers (p := p) (k := k) zero one answers).map
        (rawOfTable modulus.length) := by
  rw [tableRows_eq_numeric modulus k zero one answers (hp ▸ hpos), hlen]
  have hd := SubexpDigitGrid.descending_values p k
  have hn : (List.range (p ^ k)).reverse.map
      (fun n => (numericDigits p k n).map (SubexpLiftRing.fixedBits modulus.length)) =
      (SubexpDigitGrid.descending p k).map
        (fun v => v.toList.map (fun d => SubexpLiftRing.fixedBits modulus.length d.val)) := by
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (List.map (SubexpLiftRing.fixedBits modulus.length))) hd).symm
  have hs : (SubexpRankedTable.attachAnswers (p := p) (k := k) zero one answers).map
      (rawOfTable modulus.length) =
      ((SubexpDigitGrid.descending p k).map
        (fun v => v.toList.map (fun d => SubexpLiftRing.fixedBits modulus.length d.val))).zipWith
        (fun labels answer => (⟨if answer then one else zero, labels⟩ : RawRow)) answers := by
    clear hlen
    unfold SubexpRankedTable.attachAnswers
    induction SubexpDigitGrid.descending p k generalizing answers with
    | nil => rfl
    | cons v vs ih =>
        cases answers with
        | nil => rfl
        | cons a as => cases a <;> simp [rawOfTable, ih]
  rw [hs, ← hn, zipWith_mapped]
  apply congrArg (fun f : ℕ → Bool → RawRow =>
    (List.range (p ^ k)).reverse.zipWith f answers)
  funext n b
  cases b <;> simp [numericRow, hp]

theorem row_valid (modulus rank : Word) (k : ℕ) (zero one : Word) (answer : Bool)
    (cache : List (List Word)) (prefixes : List Subexp.FactorPacketCoordinates.Prefix)
    (hm : 0 < BinaryArithmetic.toNat modulus)
    (hc : BinaryArithmetic.toNat modulus ≤ cache.length) (hk : prefixes.length = k) :
    Subexp.FactorPacketRows.Valid cache prefixes (row modulus k zero one rank answer) := by
  constructor
  · simpa [row] using hk.symm
  · intro word hw
    have h := digitWords_valid modulus rank k hm word hw
    rw [CounterPrograms.value_eq_toNat]
    exact h.2.trans_le hc

theorem tableRows_valid (modulus : Word) (k : ℕ) (zero one answers : Word)
    (cache : List (List Word)) (prefixes : List Subexp.FactorPacketCoordinates.Prefix)
    (hm : 0 < BinaryArithmetic.toNat modulus)
    (hc : BinaryArithmetic.toNat modulus ≤ cache.length) (hk : prefixes.length = k) :
    ∀ r ∈ tableRows modulus k zero one answers, Subexp.FactorPacketRows.Valid cache prefixes r := by
  have hforward : ∀ rank input r, r ∈ forwardRows modulus k zero one rank input →
      Subexp.FactorPacketRows.Valid cache prefixes r := by
    intro rank input
    induction input generalizing rank with
    | nil => simp [forwardRows]
    | cons answer input ih =>
        intro r hr
        simp only [forwardRows, List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact row_valid modulus rank k zero one answer cache prefixes hm hc hk
        · exact ih _ r hr
  intro r hr
  exact hforward [] answers.reverse r (by simpa only [tableRows, List.mem_reverse] using hr)

end SubexponentialSAT.SubexpFactorRowStream

end OAI.Algorithms
