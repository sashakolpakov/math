import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutCacheArithmetic
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutRowsTrace
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutWordBounds

namespace OAI.Algorithms

/-!
# Actual cache and Lagrange costs from the selected Main input words

Every later word bound follows from an actual bounded stage execution.
Only the selected layout words are bounded; pending leaf streams are absent.
-/

namespace SubexponentialSAT.SubexpMainLayoutCacheBounds

open BitProgram StructuredCalls SubexpMainProgram
open SubexpLiftRing SubexpQuarticRing SubexpMainInvariant
open SubexpLayoutPorts (Allocation)
open SubexpMainLayoutWordBounds
open SubexpMainLayoutCacheArithmetic
open SubexpMainCacheSetupTrace (Run)

structure Numbers (p D S : ℕ) : Prop where
  one : 1 ≤ S
  prime : p ≤ S
  precision : D + 1 ≤ S
  sourceWidth : baseWidth p 1 ≤ S
  targetWidth : baseWidth p (D + 1) ≤ S
  fieldSize : p^4 ≤ S

theorem Numbers.mono {p D S T : ℕ} (h : Numbers p D S) (hst : S ≤ T) : Numbers p D T :=
  ⟨h.one.trans hst, h.prime.trans hst, h.precision.trans hst,
    h.sourceWidth.trans hst, h.targetWidth.trans hst, h.fieldSize.trans hst⟩

def base (W p D : ℕ) : ℕ := (W + p + D + 2)^4

theorem initial_numbers (W p D : ℕ) : Numbers p D (base W p D) := by
  let q := W + p + D + 2
  have hq : 1 ≤ q := by dsimp [q]; omega
  have hq4 : q ≤ q^4 := Nat.le_self_pow (by decide) q
  have hp : p ≤ q := by dsimp [q]; omega
  have hd : D + 1 ≤ q := by dsimp [q]; omega
  have hb : baseWidth p 1 ≤ q := by
    have hlog := Nat.log_le_self 2 p
    simp only [baseWidth, one_mul]
    dsimp [q]
    omega
  have htarget : baseWidth p (D + 1) ≤ q^2 := by
    simpa only [baseWidth, one_mul, pow_two] using Nat.mul_le_mul hd hb
  exact ⟨hq.trans hq4, hp.trans hq4, hd.trans hq4, hb.trans hq4,
    htarget.trans (Nat.pow_le_pow_right hq (by decide)), Nat.pow_le_pow_left hp 4⟩

theorem initial_size (W p D : ℕ) : W ≤ base W p D := by
  have hq4 : W + p + D + 2 ≤ (W + p + D + 2)^4 := Nat.le_self_pow (by decide) _
  unfold base
  omega

theorem after_stage {er es S : ℕ} {a b : MainState er es} {proc : Procedure er es} {budget : ℕ}
    (h : RelevantWordBound S a) (hr : Run proc budget a b) (hb : budget ≤ stage S) :
    RelevantWordBound (grow S) b := by
  apply mono (after_run h hr)
  unfold grow
  omega

theorem rings_relevant {es : ℕ} (alloc : Allocation es) (i : Fin 51) :
    RelevantPort es (SubexpMainPreparedRings.stackMap (SubexpMainCacheSetup.ringAllocation alloc) i) := by
  unfold SubexpMainPreparedRings.stackMap
  split_ifs with hlo hmid
  · left
    change i.val < 672
    omega
  · right
    refine ⟨_, rfl, ?_⟩
    have hall : ∀ j : Fin 9, ParameterPort (SubexpMainPreparedRings.persistentIndex j) ∨
        CachePort (SubexpMainPreparedRings.persistentIndex j) := by simp only [ParameterPort, CachePort]; decide
    rcases hall ⟨i.val - 36, by omega⟩ with hp | hc
    · exact Or.inl hp
    · exact Or.inr (Or.inl hc)
  · left
    change 128 + (i.val - 45) < 672
    omega

theorem nodes_relevant {es : ℕ} (alloc : Allocation es) (i : Fin 25) :
    RelevantPort es (SubexpMainFieldNodes.stackMap (SubexpMainCacheSetup.nodeAllocation alloc) i) := by
  have hhigh : ∀ j : Fin 5,
      RelevantPort es (SubexpMainFieldNodes.highPort (SubexpMainCacheSetup.nodeAllocation alloc) j) := by
    intro j
    fin_cases j
    · exact Or.inr ⟨6, rfl, Or.inl (by simp only [ParameterPort]; decide)⟩
    · exact Or.inl (by change 128 < 672; decide)
    · exact Or.inl (by change 129 < 672; decide)
    · exact Or.inr ⟨13, rfl, Or.inr (Or.inl (by simp only [CachePort]; decide))⟩
    · exact Or.inl (by change 134 < 672; decide)
  unfold SubexpMainFieldNodes.stackMap
  split_ifs with hi
  · left
    change i.val < 672
    omega
  · exact hhigh _

theorem lagrange_relevant {es : ℕ} (alloc : Allocation es) (i : Fin 256) :
    RelevantPort es (SubexpMainLagrangeCache.stackMap alloc i) := by
  cases hi : SubexpMainLagrangeCache.inputIndex i with
  | some j =>
    right
    refine ⟨SubexpMainLagrangeCache.persistentIndex j, ?_, ?_⟩
    · simp only [SubexpMainLagrangeCache.stackMap, hi]
    · have hall : ∀ j : Fin 8, ParameterPort (SubexpMainLagrangeCache.persistentIndex j) ∨
          CachePort (SubexpMainLagrangeCache.persistentIndex j) := by simp only [ParameterPort, CachePort]; decide
      rcases hall j with hp | hc
      · exact Or.inl hp
      · exact Or.inr (Or.inl hc)
  | none =>
    left
    simp only [SubexpMainLagrangeCache.stackMap, hi]
    split_ifs
    · change 668 < 672
      decide
    · change 320 + i.val < 672
      omega

theorem selector_bound {er es p D S : ℕ} {a : MainState er es}
    (h : RelevantWordBound S a) (hn : Numbers p D S) :
    SubexpQuarticSelectorAdapter.bound p
      (a.stacks (persistent es 6)).length (a.stacks (persistent es 15)).length ≤ stage S := by
  apply selector_le p _ _ S hn.prime
  · simpa only [SubexpEnumerationPayload.scalarWidth, baseWidth, one_mul] using hn.sourceWidth
  · exact parameter h 6 (by simp only [ParameterPort]; decide)
  · exact cache h 15 (by simp only [CachePort]; decide)

theorem rings_bound {er es p D S : ℕ} (alloc : Allocation es) {a : MainState er es}
    (h : RelevantWordBound S a) (hn : Numbers p D S)
    (hm : BinaryArithmetic.toNat (a.stacks (persistent es 22)) = D + 1) :
    SubexpMainPreparedRings.runtimeBound (SubexpMainCacheSetup.ringAllocation alloc) a p D ≤ stage S := by
  have hbits := sum_lengths h
    (SubexpMainPreparedRings.stackMap (SubexpMainCacheSetup.ringAllocation alloc))
    (rings_relevant alloc)
  exact rings_le p D S _ _ _ hn.sourceWidth hn.targetWidth
    (parameter h 6 (by simp only [ParameterPort]; decide)) (parameter h 22 (by simp only [ParameterPort]; decide))
    (by change BinaryArithmetic.toNat (a.stacks (persistent es 22)) ≤ S; rw [hm]; exact hn.precision) hn.one hbits

theorem nodes_bound {er es p D S : ℕ} (alloc : Allocation es) {a : MainState er es}
    (h : RelevantWordBound S a) (hn : Numbers p D S) :
    SubexpMainFieldNodes.runtimeBound (SubexpMainCacheSetup.nodeAllocation alloc) a p (D + 1) ≤ stage S := by
  have hbits := sum_lengths h
    (SubexpMainFieldNodes.stackMap (SubexpMainCacheSetup.nodeAllocation alloc))
    (nodes_relevant alloc)
  exact nodes_le p (D + 1) S _ hn.prime hn.fieldSize hn.sourceWidth hn.targetWidth hbits

theorem field_bound {er es p D S : ℕ} (alloc : Allocation es) {a : MainState er es}
    (h : RelevantWordBound S a) (hn : Numbers p D S)
    (he : BinaryArithmetic.toNat (a.stacks (persistent es 29)) = p^4 - 2) :
    SubexpMainFieldCache.runtimeBound (SubexpMainCacheSetup.cacheAllocation alloc) a p ≤ stage S := by
  apply (SubexpMainFieldCache.runtimeBound_le _ a p S hn.sourceWidth
    (ordinary h alloc 14) (parameter h 29 (by simp only [ParameterPort]; decide)) ?_ ?_).trans (field_le S)
  · rw [he]
    exact (Nat.sub_le _ _).trans hn.fieldSize
  · exact (Nat.sub_le _ _).trans hn.fieldSize

theorem inputLength_bound {er es S : ℕ} {a : MainState er es} (h : RelevantWordBound S a) :
    SubexpLagrangeCachePreparation.inputLength (SubexpMainLagrangeCache.sourceInputs a) ≤ 8 * S := by
  have h6 := parameter h 6 (by simp only [ParameterPort]; decide)
  have h30 := cache h 30 (by simp only [CachePort]; decide)
  have h12 := cache h 12 (by simp only [CachePort]; decide)
  have h13 := cache h 13 (by simp only [CachePort]; decide)
  have h14 := cache h 14 (by simp only [CachePort]; decide)
  have h31 := cache h 31 (by simp only [CachePort]; decide)
  have h22 := parameter h 22 (by simp only [ParameterPort]; decide)
  have h29 := parameter h 29 (by simp only [ParameterPort]; decide)
  dsimp only [SubexpLagrangeCachePreparation.inputLength, SubexpMainLagrangeCache.sourceInputs]
  omega

theorem lagrange_bound {er es p D S : ℕ} (alloc : Allocation es) {a : MainState er es}
    (h : RelevantWordBound S a) (hn : Numbers p D S)
    (hp : BinaryArithmetic.toNat (a.stacks (persistent es 6)) = p)
    (hm : BinaryArithmetic.toNat (a.stacks (persistent es 22)) = D + 1)
    (he : BinaryArithmetic.toNat (a.stacks (persistent es 29)) = p^4 - 2) :
    SubexpMainLagrangeCache.runtimeBound alloc a ≤ stage S := by
  apply (SubexpMainLagrangeCache.runtimeBound_le alloc a S
    (fun i _ => h _ (lagrange_relevant alloc i))).trans
  have hi := inputLength_bound h
  have hprime : SubexpLagrangeCachePreparation.primeValue
      (SubexpMainLagrangeCache.sourceInputs a) ≤ S := by
    change CounterPrograms.value (a.stacks (persistent es 6)) ≤ S
    rw [CounterPrograms.value_eq_toNat, hp]
    exact hn.prime
  have hprecision : CounterPrograms.value (SubexpMainLagrangeCache.sourceInputs a).precision ≤ S := by
    change CounterPrograms.value (a.stacks (persistent es 22)) ≤ S
    rw [CounterPrograms.value_eq_toNat, hm]
    exact hn.precision
  have hexponent : BinaryArithmetic.toNat (SubexpMainLagrangeCache.sourceInputs a).exponent ≤ S := by
    change BinaryArithmetic.toNat (a.stacks (persistent es 29)) ≤ S
    rw [he]
    exact (Nat.sub_le _ _).trans hn.fieldSize
  have hscale : 1 + SubexpLagrangeCachePreparation.primeValue
      (SubexpMainLagrangeCache.sourceInputs a) +
      CounterPrograms.value (SubexpMainLagrangeCache.sourceInputs a).precision +
      BinaryArithmetic.toNat (SubexpMainLagrangeCache.sourceInputs a).exponent +
      SubexpLagrangeCachePreparation.inputLength (SubexpMainLagrangeCache.sourceInputs a) ≤ 1 + 11 * S := by omega
  calc
    _ ≤ 248 * (2 * S + 3) + 100000000 * (1 + 11 * S)^8 + 758 := by
      unfold SubexpLagrangeCacheProgram.runtimeBound SubexpLagrangeCacheCost.runtimeBound
      exact Nat.add_le_add_right (Nat.add_le_add_left
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hscale 8)) _) _
    _ ≤ stage S := lagrange_le S

theorem staged_bounds {er es p D W : ℕ} [Fact p.Prime] (alloc : Allocation es)
    {a b c e l : MainState er es} (h : RelevantWordBound W a)
    (ht : SubexpMainCacheSetupTrace.StageTrace alloc a b c e p D)
    (hc : SubexpMainCacheSetup.Result alloc a e p D)
    (hl : Run (SubexpMainLagrangeCache.procedure er alloc)
      (SubexpMainLagrangeCache.runtimeBound alloc e) e l)
    (hp : BinaryArithmetic.toNat (a.stacks (persistent es 6)) = p)
    (hm : BinaryArithmetic.toNat (a.stacks (persistent es 22)) = D + 1)
    (he : BinaryArithmetic.toNat (a.stacks (persistent es 29)) = p^4 - 2) :
    SubexpMainCacheSetup.runtimeBound alloc a b c p D +
        SubexpMainLagrangeCache.runtimeBound alloc e ≤ iterate 5 (base W p D) ∧
      RelevantWordBound (iterate 4 (base W p D)) e ∧
      RelevantWordBound (iterate 5 (base W p D)) l := by
  let S0 := base W p D
  let S1 := grow S0
  let S2 := grow S1
  let S3 := grow S2
  let S4 := grow S3
  let S5 := grow S4
  have n0 : Numbers p D S0 := initial_numbers W p D
  have n1 : Numbers p D S1 := n0.mono (le_grow _)
  have n2 : Numbers p D S2 := n1.mono (le_grow _)
  have n3 : Numbers p D S3 := n2.mono (le_grow _)
  have n4 : Numbers p D S4 := n3.mono (le_grow _)
  have h0 : RelevantWordBound S0 a := mono h (initial_size W p D)
  have hsel := selector_bound h0 n0
  have h1 : RelevantWordBound S1 (SubexpQuarticSelectorAdapter.result a p) :=
    after_stage h0 ht.selectorRun hsel
  have hms : BinaryArithmetic.toNat
      ((SubexpQuarticSelectorAdapter.result a p).stacks (persistent es 22)) = D + 1 := by
    rw [SubexpMainCacheSetup.selector_persistent_frame a p ht.selectorReady 22 (by decide)]
    exact hm
  have hrings := rings_bound alloc h1 n1 hms
  have h2 : RelevantWordBound S2 b := after_stage h1 ht.ringsRun hrings
  have hnodes := nodes_bound alloc h2 n2
  have h3 : RelevantWordBound S3 c := after_stage h2 ht.nodesRun hnodes
  have hec : BinaryArithmetic.toNat (c.stacks (persistent es 29)) = p^4 - 2 := by
    rw [ht.nodesResult.persistent_frame 29, ht.ringsResult.persistent_frame 29 (by decide),
      SubexpMainCacheSetup.selector_persistent_frame a p ht.selectorReady 29 (by decide)]
    exact he
  have hfield := field_bound alloc h3 n3 hec
  have h4 : RelevantWordBound S4 e := after_stage h3 ht.cacheRun hfield
  have hpe : BinaryArithmetic.toNat (e.stacks (persistent es 6)) = p := by rw [hc.prime]; exact hp
  have hme : BinaryArithmetic.toNat (e.stacks (persistent es 22)) = D + 1 := by rw [hc.precision]; exact hm
  have hee : BinaryArithmetic.toNat (e.stacks (persistent es 29)) = p^4 - 2 := by rw [hc.exponent]; exact he
  have hlagrange := lagrange_bound alloc h4 n4 hpe hme hee
  have h5 : RelevantWordBound S5 l := after_stage h4 hl hlagrange
  refine ⟨?_, h4, h5⟩
  change _ ≤ S5
  unfold SubexpMainCacheSetup.runtimeBound
  have g0 : S1 = S0 + stage S0 + 1 := rfl
  have g1 : S2 = S1 + stage S1 + 1 := rfl
  have g2 : S3 = S2 + stage S2 + 1 := rfl
  have g3 : S4 = S3 + stage S3 + 1 := rfl
  have g4 : S5 = S4 + stage S4 + 1 := rfl
  omega

theorem polynomial_bounds {er es p D W : ℕ} [Fact p.Prime] (alloc : Allocation es)
    {a b c e l : MainState er es} (h : RelevantWordBound W a)
    (ht : SubexpMainCacheSetupTrace.StageTrace alloc a b c e p D)
    (hc : SubexpMainCacheSetup.Result alloc a e p D)
    (hl : Run (SubexpMainLagrangeCache.procedure er alloc)
      (SubexpMainLagrangeCache.runtimeBound alloc e) e l)
    (hp : BinaryArithmetic.toNat (a.stacks (persistent es 6)) = p)
    (hm : BinaryArithmetic.toNat (a.stacks (persistent es 22)) = D + 1)
    (he : BinaryArithmetic.toNat (a.stacks (persistent es 29)) = p^4 - 2) :
    let bound := polynomialConstant * (W + p + D + 2)^polynomialDegree
    SubexpMainCacheSetup.runtimeBound alloc a b c p D +
        SubexpMainLagrangeCache.runtimeBound alloc e ≤ bound ∧
      RelevantWordBound bound e ∧ RelevantWordBound bound l := by
  obtain ⟨hb, h4, h5⟩ := staged_bounds alloc h ht hc hl hp hm he
  have hf := iterate_five_le (W + p + D + 2) (by omega)
  exact ⟨hb.trans hf, mono h4 ((le_grow _).trans hf), mono h5 hf⟩

end SubexponentialSAT.SubexpMainLayoutCacheBounds

end OAI.Algorithms
