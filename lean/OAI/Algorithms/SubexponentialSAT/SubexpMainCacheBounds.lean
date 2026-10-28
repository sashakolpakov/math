import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainCacheSetup
import OAI.Algorithms.SubexponentialSAT.SubexpMainInvariant
import OAI.Algorithms.SubexponentialSAT.DyadicParameterBounds

namespace OAI.Algorithms

/-!
# A common bound for the retained Main caches

The bound includes both the initial setup words and the exact words emitted
by the selected-quartic and prepared-ring programs. It only bounds the seven
persistent cache ports; it makes no claim about the pending formula stream
or the ordinary node-table workspace.
-/

namespace SubexponentialSAT.SubexpMainCacheBounds

open BitProgram StructuredCalls SubexpMainProgram SubexpMainInvariant
open SubexpLiftRing SubexpQuarticRing

/-- Covers a modulus, scalar-width word, reduction/zero/one quartets,
minus-one word, and the selected source quartic. -/
def regeneratedBound (p D : ℕ) : ℕ := 4 * (baseWidth p (D + 1) + 1)

/-- Chosen once to cover the initial and regenerated persistent caches. -/
def cacheBound (initial p D : ℕ) : ℕ := max initial (regeneratedBound p D)

theorem initial_le_cacheBound (initial p D : ℕ) : initial ≤ cacheBound initial p D :=
  Nat.le_max_left _ _

theorem regenerated_le_cacheBound (initial p D : ℕ) :
    regeneratedBound p D ≤ cacheBound initial p D := Nat.le_max_right _ _

theorem cachePort_cases (i : Fin 32) (hi : CachePort i) :
    i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 28 ∨ i = 30 ∨ i = 31 := by
  dsimp [CachePort] at hi
  omega

theorem bankLengths_bound {W : ℕ} {words : Fin 6 → List Bool}
    (h : SubexpMainCacheSetup.BankLengths W words) (i : Fin 6) :
    (words i).length ≤ 4 * (W + 1) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  fin_cases i
  · change (words 0).length ≤ 4 * (W + 1)
    omega
  · change (words 1).length ≤ 4 * (W + 1)
    omega
  · change (words 2).length ≤ 4 * (W + 1)
    omega
  · change (words 3).length ≤ 4 * (W + 1)
    omega
  · change (words 4).length ≤ 4 * (W + 1)
    omega
  · change (words 5).length ≤ 4 * (W + 1)
    omega

theorem bankWords_bound (p D : ℕ) [Fact p.Prime]
    (coeff : Quad (Word (baseWidth p 1)))
    (hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p))
    (i : Fin 6) :
    (SubexpPreparedRingStaging.bankWords p D coeff hc i).length ≤ regeneratedBound p D :=
  bankLengths_bound (SubexpMainCacheSetup.bankWords_lengths p D coeff hc) i

theorem selectedBytes_bound (p D : ℕ) [Fact p.Prime] :
    (SubexpQuarticSelectorAdapter.selectedBytes p).length ≤ regeneratedBound p D := by
  have hwidth : SubexpEnumerationPayload.scalarWidth p ≤ baseWidth p (D + 1) := by
    simpa only [one_mul, SubexpEnumerationPayload.scalarWidth, baseWidth] using
      Nat.mul_le_mul_right (Nat.log 2 p + 1) (by omega : (1 : ℕ) ≤ D + 1)
  rw [SubexpQuarticSelectorAdapter.selectedBytes_length]
  unfold regeneratedBound
  omega

/-- Exact target-bank and selected-quartic outputs bound every cache port. -/
theorem caches_of_words {er es p D : ℕ} [Fact p.Prime]
    (after : MainState er es) (coeff : Quad (Word (baseWidth p 1)))
    (hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p))
    (htarget : ∀ j, after.stacks (persistent es (SubexpMainPreparedRings.targetIndex j)) =
      SubexpPreparedRingStaging.bankWords p D coeff hc j)
    (hselected : after.stacks (persistent es 15) = SubexpQuarticSelectorAdapter.selectedBytes p)
    (B : ℕ) (hB : regeneratedBound p D ≤ B) :
    ∀ i : Fin 32, CachePort i → (after.stacks (persistent es i)).length ≤ B := by
  have ht (j : Fin 6) :
      (after.stacks (persistent es (SubexpMainPreparedRings.targetIndex j))).length ≤ B := by
    rw [htarget j]
    exact (bankWords_bound p D coeff hc j).trans hB
  intro i hi
  rcases cachePort_cases i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ht 0
  · exact ht 1
  · exact ht 2
  · rw [hselected]
    exact (selectedBytes_bound p D).trans hB
  · exact ht 3
  · exact ht 4
  · exact ht 5

/-- The prepared-ring execution supplies the six target words; the actual
selector supplies the seventh word on persistent port 15. -/
theorem prepared_caches {er es p D : ℕ} [Fact p.Prime]
    {alloc : SubexpMainPreparedRings.Allocation es} {before after : MainState er es}
    {coeff : Quad (Word (baseWidth p 1))}
    {hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p)}
    (h : SubexpMainPreparedRings.Result alloc before after p D coeff hc)
    (hselected : after.stacks (persistent es 15) = SubexpQuarticSelectorAdapter.selectedBytes p)
    (B : ℕ) (hB : regeneratedBound p D ≤ B) :
    ∀ i : Fin 32, CachePort i → (after.stacks (persistent es i)).length ≤ B :=
  caches_of_words after coeff hc h.target hselected B hB

theorem prepared_caches_common {er es p D : ℕ} [Fact p.Prime]
    {alloc : SubexpMainPreparedRings.Allocation es} {before after : MainState er es}
    {coeff : Quad (Word (baseWidth p 1))}
    {hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p)}
    (h : SubexpMainPreparedRings.Result alloc before after p D coeff hc)
    (hselected : after.stacks (persistent es 15) = SubexpQuarticSelectorAdapter.selectedBytes p)
    (initial : ℕ) :
    ∀ i : Fin 32, CachePort i →
      (after.stacks (persistent es i)).length ≤ cacheBound initial p D :=
  prepared_caches h hselected _ (regenerated_le_cacheBound initial p D)

/-- The complete selector/ring/node/cache execution has the same bound,
using its actual output fields rather than a cache-size premise. -/
theorem setup_caches {er es p D : ℕ} [Fact p.Prime]
    {alloc : SubexpMainCacheSetup.Allocation es} {before after : MainState er es}
    (h : SubexpMainCacheSetup.Result alloc before after p D)
    (B : ℕ) (hB : regeneratedBound p D ≤ B) :
    ∀ i : Fin 32, CachePort i → (after.stacks (persistent es i)).length ≤ B :=
  caches_of_words after (SubexpPreparedQuarticSetup.selectedInputCoefficients p)
    (SubexpPreparedQuarticSetup.selectedInputCoefficients_value p) h.target h.selected B hB

theorem setup_caches_common {er es p D : ℕ} [Fact p.Prime]
    {alloc : SubexpMainCacheSetup.Allocation es} {before after : MainState er es}
    (h : SubexpMainCacheSetup.Result alloc before after p D) (initial : ℕ) :
    ∀ i : Fin 32, CachePort i →
      (after.stacks (persistent es i)).length ≤ cacheBound initial p D :=
  setup_caches h _ (regenerated_le_cacheBound initial p D)

/-- The same chosen cache bound already holds at the initial leaf. -/
theorem after_boot_common {cfg : SubexpSetupProgram.Config} {er n initial : ℕ}
    {hr : 32 ≤ workRegs er} {F : SAT.CNF (Fin n)}
    (run : SubexpMainBoot.Run cfg hr F)
    (hw : SubexpSetupStorage.WordBound initial run.afterSetup) (p D : ℕ) :
    Invariant cfg run.setupOutput (cacheBound initial p D) run.afterSparsify :=
  SubexpMainInvariant.after_boot run
    (fun i => (hw i).trans (initial_le_cacheBound initial p D))

theorem baseWidth_le_square {p D L : ℕ} (hp : p ≤ L) (hD : D ≤ L) :
    baseWidth p (D + 1) ≤ (L + 1)^2 := by
  have hb := Nat.add_le_add_right ((Nat.log_le_self 2 p).trans hp) 1
  simpa only [baseWidth, pow_two] using Nat.mul_le_mul (Nat.add_le_add_right hD 1) hb

theorem regeneratedBound_le_square {p D L : ℕ} (hp : p ≤ L) (hD : D ≤ L) :
    regeneratedBound p D ≤ 8 * (L + 1)^2 := by
  have hw := baseWidth_le_square hp hD
  have hpos : 1 ≤ (L + 1)^2 := Nat.one_le_pow _ _ (by omega)
  unfold regeneratedBound
  omega

theorem cacheBound_le_square (initial : ℕ) {p D L : ℕ} (hp : p ≤ L) (hD : D ≤ L) :
    cacheBound initial p D ≤ max initial (8 * (L + 1)^2) :=
  max_le_max le_rfl (regeneratedBound_le_square hp hD)

/-- Fixed initial polynomial constants give fixed common-bound constants. -/
theorem cacheBound_le_polynomial {initial p D L C d : ℕ}
    (hp : p ≤ L) (hD : D ≤ L) (hinitial : initial ≤ C * (L + 1)^d) :
    cacheBound initial p D ≤ (C + 8) * (L + 1)^(d + 2) := by
  have hbase : 1 ≤ L + 1 := by omega
  have hd : (L + 1)^d ≤ (L + 1)^(d + 2) := Nat.pow_le_pow_right hbase (by omega)
  have htwo : (L + 1)^2 ≤ (L + 1)^(d + 2) := Nat.pow_le_pow_right hbase (by omega)
  apply max_le
  · exact (hinitial.trans (Nat.mul_le_mul_left C hd)).trans
      (Nat.mul_le_mul_right _ (by omega : C ≤ C + 8))
  · exact ((regeneratedBound_le_square hp hD).trans (Nat.mul_le_mul_left 8 htwo)).trans
      (Nat.mul_le_mul_right _ (by omega : 8 ≤ C + 8))

/-- Apply the actual scheduled prime and packed dimension to original
input length. The constants do not depend on the leaf or current state. -/
theorem scheduled_cacheBound_le_polynomial {n L initial C d : ℕ}
    (hn : SubexpPackingParameters.GoodInput n) (hnL : n ≤ L)
    (hinitial : initial ≤ C * (L + 1)^d) :
    cacheBound initial (SubexpPackingParameters.p n) (SubexpPackingParameters.D n) ≤
      (C + 8) * (L + 1)^(d + 2) :=
  cacheBound_le_polynomial ((DyadicParameterBounds.p_le_n hn).trans hnL)
    ((DyadicParameterBounds.D_le_n hn).trans hnL) hinitial

end SubexponentialSAT.SubexpMainCacheBounds

end OAI.Algorithms
