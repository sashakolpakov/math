import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheLoop
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheReverse
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheCleanup
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheSize
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheCost

namespace OAI.Algorithms

/-! A complete fixed program for the target-ring Lagrange coefficient cache.
It accepts eight raw master words, computes every basis row, restores
ascending label order, and clears every non-output working stack. -/

namespace SubexponentialSAT.SubexpLagrangeCacheProgram

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing SubexpLagrangeCacheState
open SubexpLagrangeCachePreparation SubexpLagrangeCacheLoop

def command : Code :=
  .seq SubexpLagrangeCacheControl.prepare
    (.seq (SubexpLagrangeCacheControl.outerLoop SubexpLagrangeInverseCall.command)
      (.seq SubexpLagrangeCacheControl.reverseCache SubexpLagrangeCacheCleanup.command))

def program := compiled command 206 250
def runtimeBound := SubexpLagrangeCacheCost.runtimeBound

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

def outputState (x : Inputs) (rows : List (List (Coefficient p μ))) (regs : Fin 16 → Bool) : Data :=
  ⟨regs, Function.update (rawStore x) 250
    (Subexp.FactorPacketCoordinates.cacheBytes (encodeRows p μ rows))⟩

theorem good_length (rows : List (List (Coefficient p μ))) (i : ℕ)
    (h : Good p μ rows i) : rows.length = i := by
  simpa only [List.length_reverse, List.length_range] using h.length_eq

theorem good_rows (rows : List (List (Coefficient p μ))) (i : ℕ)
    (h : Good p μ rows i) : ∀ row ∈ rows, row.length = p := by
  have aux {rs : List (List (Coefficient p μ))} {labels : List ℕ}
      (hr : List.Forall₂ (SubexpLagrangeCacheRowCorrectness.Correct p μ) rs labels) :
      ∀ row ∈ rs, row.length = p := by
    induction hr with
    | nil => simp
    | @cons a b as bs hab htail ih =>
        intro row hrow
        simp only [List.mem_cons] at hrow
        rcases hrow with rfl | hrow
        · exact hab.1
        · exact ih row hrow
  exact aux h

theorem cache_length (rows : List (List (Coefficient p μ))) (h : Good p μ rows p) :
    (Subexp.FactorPacketCoordinates.cacheBytes (encodeRows p μ rows)).length =
      SubexpLagrangeCacheCost.cacheSize p (baseWidth p μ) := by
  have hr : ∀ r ∈ encodeRows p μ rows, r.length = p := by
    intro r hmem
    obtain ⟨xs, hxs, rfl⟩ := List.mem_map.mp hmem
    simpa using good_rows p μ rows p h xs hxs
  have hw : ∀ r ∈ encodeRows p μ rows, ∀ w ∈ r, w.length = 4 * baseWidth p μ := by
    intro r hr w hw
    obtain ⟨xs, _, rfl⟩ := List.mem_map.mp hr
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hw
    exact SubexpFlatAdd.encode_length x
  rw [SubexpLagrangeCacheSize.cacheBytes_length _ p (4 * baseWidth p μ) hr hw]
  simp only [encodeRows, List.length_map, good_length p μ rows p h]
  unfold SubexpLagrangeCacheCost.cacheSize
  ring

theorem command_correct (hμ : 0 < μ) (x : Inputs) (t zero one : Coefficient p μ)
    (minusOne : Word (baseWidth p μ))
    (H : SubexpLagrangeCacheContext.Valid p μ M x t zero one minusOne)
    (ht : t.map (wordValue p μ) = reductionData (QuarticSearch.liftedCoefficients p μ))
    (hz : SubexpLagrangeInverseCall.denote p μ zero = 0)
    (ho : SubexpLagrangeInverseCall.denote p μ one = 1)
    (hm : wordValue p μ minusOne = -1) (regs : Fin 16 → Bool) :
    ∃ n rf rows, n ≤ SubexpLagrangeCacheCost.exactBound x (baseWidth p μ) ∧
      Eval command n (rawState x regs) (outputState p μ x rows rf) ∧
      List.Forall₂ (SubexpLagrangeCacheRowCorrectness.Correct p μ) rows (List.range p) := by
  obtain ⟨n1, r1, hn1, h1⟩ := SubexpLagrangeCachePreparation.command_correct x regs
  obtain ⟨n2, r2, rows, hn2, h2, hg⟩ := loop_correct p μ M hμ x t zero one minusOne H ht hz ho hm r1
  let cache := encodeRows p μ rows
  let s2 := SubexpLagrangeCacheOuterState.view p μ M (preparedStore x) zero one p cache []
  have he (k : Fin 256) (hk : k ∉ SubexpLagrangeCacheContext.support) (hk248 : k ≠ 248) : s2 k = [] :=
    SubexpLagrangeCacheInvariant.view_empty p μ M x zero one p cache [] k hk hk248
  have hrev := SubexpLagrangeCacheReverse.reverse_run s2 cache
    (by simp [s2, SubexpLagrangeCacheOuterState.view])
    (he 236 (by decide) (by decide)) (he 237 (by decide) (by decide))
    (he 238 (by decide) (by decide)) (he 245 (by decide) (by decide)) r2
  obtain ⟨n3, r3, hn3, h3⟩ := hrev
  let current := SubexpFlatAdd.encode (label p μ M zero one p)
  let index := List.replicate p false
  let outBytes := Subexp.FactorPacketCoordinates.cacheBytes (encodeRows p μ rows.reverse)
  have hs3 : Function.update s2 250 (Subexp.FactorPacketCoordinates.cacheBytes cache.reverse) =
      SubexpLagrangeCacheCleanup.store x current index outBytes := by
    have hc : cache.reverse = encodeRows p μ rows.reverse := by simp [cache, encodeRows]
    rw [hc]
    funext k
    by_cases hk250 : k = 250
    · subst k; simp [SubexpLagrangeCacheCleanup.store, outBytes]
    · by_cases hk246 : k = 246
      · subst k; simp [s2, SubexpLagrangeCacheOuterState.view, SubexpLagrangeCacheCleanup.store]
      · simp [s2, SubexpLagrangeCacheOuterState.view, SubexpLagrangeCacheCleanup.store,
          current, index, hk250, hk246, outBytes]
  rw [hs3] at h3
  obtain ⟨n4, r4, hn4, h4⟩ := SubexpLagrangeCacheCleanup.command_run x current index outBytes r3
  have hall := h1.seq (h2.seq (h3.seq h4))
  have hgood : List.Forall₂ (SubexpLagrangeCacheRowCorrectness.Correct p μ) rows.reverse (List.range p) := by
    simpa only [List.reverse_reverse] using List.rel_reverse hg
  refine ⟨n1 + (n2 + (n3 + n4)), r4, rows.reverse, ?_, hall, hgood⟩
  have hlen : (Subexp.FactorPacketCoordinates.cacheBytes cache).length =
      SubexpLagrangeCacheCost.cacheSize p (baseWidth p μ) := cache_length p μ rows hg
  rw [SubexpLagrangeCacheSize.cacheBytes_reverse_length, hlen] at hn3
  have hc4 : n4 ≤ 8 * baseWidth p μ + 2 * p +
      100 * (primeValue x + 1) * (inputLength x + 1) := by
    simpa only [SubexpLagrangeCacheCleanup.runtimeBound, current, index,
      SubexpFlatAdd.encode_length, List.length_replicate, ← Nat.mul_assoc] using hn4
  change n2 ≤ SubexpLagrangeCacheCost.loopBound (primeValue x) (baseWidth p μ)
    x.exponent x.precision at hn2
  unfold SubexpLagrangeCacheCost.exactBound
  rw [H.prime]
  rw [H.prime] at hn2
  rw [H.prime] at hc4
  omega

/-- The single fixed cache program, including its final halt, has a
polynomial bound in the numeric prime/precision/exponent and raw input size. -/
theorem program_correct (hμ : 0 < μ) (x : Inputs) (t zero one : Coefficient p μ)
    (minusOne : Word (baseWidth p μ))
    (H : SubexpLagrangeCacheContext.Valid p μ M x t zero one minusOne)
    (ht : t.map (wordValue p μ) = reductionData (QuarticSearch.liftedCoefficients p μ))
    (hz : SubexpLagrangeInverseCall.denote p μ zero = 0)
    (ho : SubexpLagrangeInverseCall.denote p μ one = 1)
    (hm : wordValue p μ minusOne = -1) (regs : Fin 16 → Bool) :
    ∃ rf rows, RunsIn program (runtimeBound x)
      ((rawState x regs).withPC (some program.entry))
      ((outputState p μ x rows rf).withPC none) ∧
      List.Forall₂ (SubexpLagrangeCacheRowCorrectness.Correct p μ) rows (List.range p) := by
  obtain ⟨n, rf, rows, hn, he, hg⟩ := command_correct p μ M hμ x t zero one minusOne H ht hz ho hm regs
  have hB : baseWidth p μ ≤ inputLength x := by
    rw [← H.width]
    unfold inputLength
    omega
  refine ⟨rf, rows, ?_, hg⟩
  exact ⟨n + 1,
    (Nat.add_le_add_right hn 1).trans
      (SubexpLagrangeCacheCost.exactBound_add_one_le_runtimeBound x (baseWidth p μ) hB),
    compiled_halt_trace he 206 250⟩

omit [Fact (Nat.Prime p)] in
theorem output_frame (x : Inputs) (rows : List (List (Coefficient p μ)))
    (regs : Fin 16 → Bool) (k : Fin 256) (hk : k ≠ 250) :
    (outputState p μ x rows regs).stacks k = rawStore x k := by
  simp [outputState, hk]

end SubexponentialSAT.SubexpLagrangeCacheProgram

end OAI.Algorithms
