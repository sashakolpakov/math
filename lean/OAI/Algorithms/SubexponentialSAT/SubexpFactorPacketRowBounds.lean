import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPacketLocalBounds

namespace OAI.Algorithms

/-! Bounds for labels actually generated from the Boolean answer records. -/

namespace SubexponentialSAT.SubexpFactorPacketBounds

open Subexp.FactorPacketCoordinates (Word Prefix cacheBytes)
open Subexp.FactorPacketRows (RawRow Valid)
open SubexpFactorRowStream (row forwardRows tableRows)

theorem generatedRow_bound {B : ℕ} (modulus : Word) (k : ℕ) (zero one rank : Word)
    (answer : Bool) (hm : modulus.length ≤ B) (hk : k ≤ B)
    (hz : zero.length ≤ B) (ho : one.length ≤ B) :
    RowBound B (row modulus k zero one rank answer) := by
  refine ⟨?_, ?_, ?_⟩
  · change (if answer then one else zero).length ≤ B
    split_ifs <;> assumption
  · simpa only [row, SubexpBasePUnranking.digitWords_length] using hk
  · intro w hw
    exact (SubexpFactorLabelProgram.digitWords_width modulus rank k w hw).trans_le hm

theorem generatedRows_bound {B : ℕ} (modulus : Word) (k : ℕ) (zero one answers : Word)
    (hm : modulus.length ≤ B) (hk : k ≤ B) (hz : zero.length ≤ B) (ho : one.length ≤ B) :
    ∀ r ∈ tableRows modulus k zero one answers, RowBound B r := by
  have h : ∀ rank input r, r ∈ forwardRows modulus k zero one rank input → RowBound B r := by
    intro rank input
    induction input generalizing rank with
    | nil => simp [forwardRows]
    | cons answer input ih =>
      intro r hr
      simp only [forwardRows, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact generatedRow_bound modulus k zero one rank answer hm hk hz ho
      · exact ih _ r hr
  intro r hr
  exact h [] answers.reverse r (by simpa only [tableRows, List.mem_reverse] using hr)

theorem labelBudget_le {B : ℕ} (hB : 1 ≤ B) (modulus rank : Word) (k : ℕ)
    (hm : modulus.length ≤ B) (hr : rank.length ≤ B) (hk : k ≤ B) :
    SubexpFactorLabelProgram.budget modulus rank k ≤ 2000 * B^3 := by
  have hs : modulus.length + rank.length + 1 ≤ 3 * B := by omega
  have h12 : B ≤ B^2 := Nat.le_self_pow (by decide) B
  have h23 : B^2 ≤ B^3 := Nat.pow_le_pow_right hB (by decide)
  unfold SubexpFactorLabelProgram.budget SubexpFieldRowPreparation.budget SubexpBasePUnranking.budget
  simp only [List.length_replicate]
  calc
    _ ≤ B * (100 * (3 * B)^2 + 14 * B + 8 * B + 19) + 6 + 9 * B + 7 * B + 13 + 1 +
      (7 * B + 5) + (B * (28 * B + 33) + 11) + 1 := by gcongr
    _ ≤ 2000 * B^3 := by nlinarith only [hB, h12, h23]

theorem generatedRowCost_le {B : ℕ} (hB : 1 ≤ B) (modulus : Word) (k : ℕ)
    (zero one rank : Word) (answer : Bool) (hm : modulus.length ≤ B) (hk : k ≤ B)
    (hz : zero.length ≤ B) (ho : one.length ≤ B) (hr : rank.length ≤ B) :
    SubexpFactorRowStream.rowCost modulus k zero one rank answer ≤ 3000 * B^3 := by
  have hl := labelBudget_le hB modulus rank k hm hr hk
  have hraw := rawRowBytes_le hB _ (generatedRow_bound modulus k zero one rank answer hm hk hz ho)
  have hval : (if answer then one else zero).length ≤ B := by split_ifs <;> assumption
  have hc := (CounterPrograms.rippleCost_le true rank).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 8 hr) 7)
  have h12 : B ≤ B^2 := Nat.le_self_pow (by decide) B
  have h23 : B^2 ≤ B^3 := Nat.pow_le_pow_right hB (by decide)
  unfold SubexpFactorRowStream.rowCost
  omega

theorem rowScanCost_le {B : ℕ} (hB : 1 ≤ B) (modulus : Word) (k : ℕ)
    (zero one rank answers : Word) (hm : modulus.length ≤ B) (hk : k ≤ B)
    (hz : zero.length ≤ B) (ho : one.length ≤ B) (hr : rank.length + answers.length ≤ B) :
    SubexpFactorRowStream.scanCost modulus k zero one rank answers ≤
      answers.length * (3000 * B^3 + 2) + 2 := by
  induction answers generalizing rank with
  | nil => simp [SubexpFactorRowStream.scanCost]
  | cons answer answers ih =>
    have hh := generatedRowCost_le hB modulus k zero one rank answer hm hk hz ho (by
      simp only [List.length_cons] at hr
      omega)
    have hn := CounterPrograms.ripple_length_le true rank
    have ht := ih (CounterPrograms.ripple true rank) (by
      simp only [List.length_cons] at hr
      omega)
    simp only [SubexpFactorRowStream.scanCost, List.length_cons]
    nlinarith only [hh, ht]

theorem finalRank_length_le (rank answers : Word) :
    (SubexpFactorRowStream.finalRank rank answers).length ≤ rank.length + answers.length := by
  induction answers generalizing rank with
  | nil => simp [SubexpFactorRowStream.finalRank]
  | cons answer answers ih =>
    have hn := CounterPrograms.ripple_length_le true rank
    have ht := ih (CounterPrograms.ripple true rank)
    simp only [SubexpFactorRowStream.finalRank, List.length_cons]
    omega

theorem generatedRowsRuntime_le {B : ℕ} (hB : 1 ≤ B) (modulus : Word) (k : ℕ)
    (zero one answers : Word) (hm : modulus.length ≤ B) (hk : k ≤ B)
    (hz : zero.length ≤ B) (ho : one.length ≤ B) (ha : answers.length ≤ B) :
    SubexpFactorRowStream.runtimeBound modulus k zero one answers ≤ 4000 * B^4 := by
  have hs := rowScanCost_le hB modulus k zero one [] answers.reverse hm hk hz ho (by simpa using ha)
  have hf := finalRank_length_le [] answers.reverse
  simp only [List.length_reverse, List.length_nil, zero_add] at hs hf
  have hh := hs.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ ha) 2)
  have h14 : B ≤ B^4 := Nat.le_self_pow (by decide) B
  unfold SubexpFactorRowStream.runtimeBound
  nlinarith only [hh, hf, ha, hB, h14]

theorem localFactorBytes_le {B : ℕ} (hB : 1 ≤ B)
    (m : SubexpFactorPacketControl.Masters) (cache : List (List Word))
    (hc : (cacheBytes cache).length ≤ B) (hm : m.modulus.length ≤ B)
    (hz : m.zero.length ≤ B) (ho : m.one.length ≤ B)
    (hpos : 0 < BinaryArithmetic.toNat m.modulus)
    (hcache : BinaryArithmetic.toNat m.modulus ≤ cache.length)
    (i : SubexpFactorPacketLocal.Input) (hp : PrefixBound B i.prefixes) (ha : i.answers.length ≤ B) :
    (SubexpFactorPacketLocal.factorBytes m cache i).length ≤ 100 * B^3 := by
  apply factorBytes_le hB cache hc i.prefixes hp
    (tableRows m.modulus i.prefixes.length m.zero m.one i.answers)
  · simpa only [SubexpFactorRowStream.tableRows_length] using ha
  · exact generatedRows_bound m.modulus i.prefixes.length m.zero m.one i.answers hm hp.1 hz ho
  · exact SubexpFactorRowStream.tableRows_valid m.modulus i.prefixes.length m.zero m.one
      i.answers cache i.prefixes hpos hcache rfl

theorem localBudget_le {B : ℕ} (hB : 1 ≤ B)
    (m : SubexpFactorPacketControl.Masters) (cache : List (List Word))
    (hc : (cacheBytes cache).length ≤ B) (hm : m.modulus.length ≤ B)
    (hz : m.zero.length ≤ B) (ho : m.one.length ≤ B)
    (hpos : 0 < BinaryArithmetic.toNat m.modulus)
    (hcache : BinaryArithmetic.toNat m.modulus ≤ cache.length)
    (i : SubexpFactorPacketLocal.Input) (hp : PrefixBound B i.prefixes) (ha : i.answers.length ≤ B) :
    SubexpFactorPacketLocal.localBudget m cache i ≤ 20000 * B^4 := by
  have hg := groupBytes_le hB i.prefixes hp
  have hpre := prefixStream_le hB i.prefixes hp
  have hlen := hp.1
  have hrows := generatedRowsRuntime_le hB m.modulus i.prefixes.length m.zero m.one i.answers hm hp.1 hz ho ha
  have hpacket := packetRowsRuntime_le hB cache hc i.prefixes hp
    (tableRows m.modulus i.prefixes.length m.zero m.one i.answers)
    (by simpa only [SubexpFactorRowStream.tableRows_length] using ha)
    (generatedRows_bound m.modulus i.prefixes.length m.zero m.one i.answers hm hp.1 hz ho)
    (SubexpFactorRowStream.tableRows_valid m.modulus i.prefixes.length m.zero m.one i.answers
      cache i.prefixes hpos hcache rfl)
  have hfactor := localFactorBytes_le hB m cache hc hm hz ho hpos hcache i hp ha
  have h12 : B ≤ B^2 := Nat.le_self_pow (by decide) B
  have h24 : B^2 ≤ B^4 := Nat.pow_le_pow_right hB (by decide)
  have h34 : B^3 ≤ B^4 := Nat.pow_le_pow_right hB (by decide)
  unfold SubexpFactorPacketLocal.localBudget SubexpFactorPacketLocal.groupReadCost
    SubexpFactorPacketLocal.groupBytes
  omega

end SubexponentialSAT.SubexpFactorPacketBounds

end OAI.Algorithms
