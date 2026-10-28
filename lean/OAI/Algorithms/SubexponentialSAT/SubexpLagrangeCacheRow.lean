import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheOuterState
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheInitialize
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheInner
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheRows
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeNormalize

namespace OAI.Algorithms

/-! A complete, concrete Lagrange row: initialize the two products, run
all integer nodes, normalize, frame the coefficient row, and advance i. -/

namespace SubexponentialSAT.SubexpLagrangeCacheRow

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing SubexpLagrangeCacheWorkspace
open SubexpLagrangeCacheState

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

def products (D : ℕ) (t zero one : Coefficient p μ)
    (minusOne : Word (baseWidth p μ)) (i : ℕ) : Partial p μ D :=
  run p μ M D t zero one minusOne i 0 D
    (SubexpLagrangeCacheInitialize.initial p μ D zero one)

structure Environment (D : ℕ) (t zero one : Coefficient p μ)
    (minusOne : Word (baseWidth p μ)) (width exponent counter : List Bool)
    (s : Store) (i : ℕ) : Prop extends
      SubexpLagrangeCacheInner.Environment p μ M D t zero one minusOne width s i where
  exponent_eq : s 225 = exponent
  counter_eq : s 224 = counter
  fresh : ∀ k ∈ ([205, 215, 216, 218, 226, 229, 230, 231, 232, 233, 234, 235,
    240, 247, 249] : List (Fin 256)), s k = []

def row (D : ℕ) (t zero one : Coefficient p μ) (minusOne : Word (baseWidth p μ))
    (i : ℕ) (inverse : Coefficient p μ) : List (Coefficient p μ) :=
  SubexpLagrangeNormalize.polynomial p μ M t zero inverse D
    (products p μ M D t zero one minusOne i).polynomial

def output (s : Store) (zero one : Coefficient p μ) (i : ℕ)
    (bits : List (List Bool)) (cache : List (List (List Bool))) : Store :=
  Function.update (Function.update (Function.update s 250
    (Subexp.FactorPacketCoordinates.cacheBytes (bits :: cache)))
      217 (SubexpFlatAdd.encode (label p μ M zero one (i + 1))))
        248 (List.replicate (i + 1) false)

def budget (D B i : ℕ) (exponent counter : List Bool) : ℕ :=
  300 * (D + 1) * (B + 1) +
    SubexpLagrangeCacheInner.loopBound D B i 0 D +
    (8 * B + 3) + (2 * D + 3) +
    SubexpLagrangeNormalize.runtimeBound D B exponent counter +
    100 * (D + 1) * (4 * B + 1) + (26000 * (B + 1)^2 + 8 * B) + 2

theorem command_correct (hμ : 0 < μ) (D : ℕ) (t zero one : Coefficient p μ)
    (minusOne : Word (baseWidth p μ)) (width exponent counter : List Bool)
    (s : Store) (i : ℕ) (H : Environment p μ M D t zero one minusOne width exponent counter s i)
    (cache : List (List (List Bool)))
    (hcache : s 250 = Subexp.FactorPacketCoordinates.cacheBytes cache)
    (ht : t.map (wordValue p μ) = reductionData (QuarticSearch.liftedCoefficients p μ))
    (hu : SubexpLagrangeInverseCall.denote p μ one = 1)
    (hm : wordValue p μ minusOne = -1)
    (he : BinaryArithmetic.toNat exponent = p ^ 4 - 2)
    (hc : CounterPrograms.value counter = μ)
    (ha : SubexpActualRing.rho p μ hμ (SubexpLagrangeInverseCall.denote p μ
      (products p μ M D t zero one minusOne i).denominator) ≠ 0)
    (regs : Fin 16 → Bool) :
    ∃ n rf inverse, n ≤ budget D (baseWidth p μ) i exponent counter ∧
      Eval (SubexpLagrangeCacheControl.outerStep SubexpLagrangeInverseCall.command) n
        (⟨regs, s⟩ : Data)
        ⟨rf, output p μ M s zero one i
          ((row p μ M D t zero one minusOne i inverse).map SubexpFlatAdd.encode) cache⟩ ∧
      SubexpLagrangeInverseCall.denote p μ inverse * SubexpLagrangeInverseCall.denote p μ
        (products p μ M D t zero one minusOne i).denominator = 1 ∧
      (row p μ M D t zero one minusOne i inverse).length = D := by
  let B := baseWidth p μ
  let A := products p μ M D t zero one minusOne i
  let s1 := SubexpLagrangeCacheState.view p μ M D s zero one 0
    (SubexpLagrangeCacheInitialize.initial p μ D zero one) (List.replicate D true)
  let s2 := SubexpLagrangeCacheState.view p μ M D s zero one D A []
  let s3 := Function.update s2 218 []
  let s4 := Function.update (Function.update s 205 (SubexpFlatAdd.encode A.denominator))
    240 (encode p μ A.polynomial)
  have h205 := H.fresh 205 (by simp)
  have h218 := H.fresh 218 (by simp)
  have h240 := H.fresh 240 (by simp)
  have h245 := H.empty 245 (by simp)
  have h247 := H.fresh 247 (by simp)
  have h249 := H.fresh 249 (by simp)
  obtain ⟨n1, r1, hn1, h1⟩ := SubexpLagrangeCacheInitialize.initialize_run p μ M s D t zero one
    width H.workspace H.zero_eq H.one_eq H.theta_eq H.dimension h205 h218 h240 h245 h247 h249 regs
  obtain ⟨n2, hn2, r2, h2⟩ := SubexpLagrangeCacheInner.loop_eval p μ M D t zero one minusOne
    width s i 0 D H.toEnvironment (SubexpLagrangeCacheInitialize.initial p μ D zero one) r1
  simp only [Nat.zero_add] at h2
  change Eval SubexpLagrangeCacheControl.initializeRow n1 ⟨regs, s⟩ ⟨r1, s1⟩ at h1
  change Eval SubexpLagrangeCacheControl.innerLoop n2 ⟨r1, s1⟩ ⟨r2, s2⟩ at h2
  have hc3 : ExecutesIn (clear 218) (8 * B + 3) s2 s3 := by
    simpa [s3, s2, SubexpLagrangeCacheState.view, SubexpFlatAdd.encode_length,
      ← Nat.mul_assoc] using clear_run 218 s2
  obtain ⟨n3, r3, hn3, h3⟩ := hc3 r2
  have hs4 : Function.update s3 249 [] = s4 :=
    SubexpLagrangeCacheOuterState.inner_finished p μ M s zero one D D A h218 h247 h249
  have hc4 : ExecutesIn (clear 249) (2 * D + 3) s3 s4 := by
    have q := clear_run 249 s3
    rw [hs4] at q
    simpa [s3, s2, SubexpLagrangeCacheState.view] using q
  obtain ⟨n4, r4, hn4, h4⟩ := hc4 r3
  have H4 : Ready M.bits width (SubexpQuarticFlatMul.flat t) B s4 :=
    (H.workspace.update 205 (by decide) _).update 240 (by decide) _
  have hnorm := SubexpLagrangeNormalize.command_correct p μ M hμ (⟨r4, s4⟩ : Data)
    D A.polynomial t zero A.denominator one minusOne width exponent counter H.width_eq H4 H.zero_eq
    (by simp [s4]) (by simpa [s4] using H.one_eq) (by simpa [s4] using H.minus_eq)
    (by simpa [s4] using H.counter_eq) (by simpa [s4] using H.exponent_eq)
    (by simpa [s4] using H.empty 214 (by simp))
    (by simpa [s4] using H.fresh 215 (by simp))
    (by simpa [s4] using H.fresh 216 (by simp))
    (by simpa [s4] using H.empty 219 (by simp))
    A.length_eq (by rfl) (by simpa [s4] using H.empty 241 (by simp))
    (by simpa [s4, SubexpLagrangeNormalize.encode,
      SubexpLagrangeCacheState.encode] using H.zero_array)
    (by simpa [s4] using H.dimension)
    (by simpa [s4] using H.empty 244 (by simp)) (by simpa [s4] using h245)
    ht hu hm he hc ha
  obtain ⟨n5, r5, inverse, hn5, h5, hinverse, hlen, H5⟩ := hnorm
  let R := row p μ M D t zero one minusOne i inverse
  let bits := R.map SubexpFlatAdd.encode
  let s5 := Function.update s 240 (encode p μ R)
  have hs5 : SubexpLagrangeNormalize.finalStore s4
      (SubexpLagrangeNormalize.encode p μ
        (SubexpLagrangeNormalize.polynomial p μ M t zero inverse D A.polynomial)) = s5 := by
    funext k
    by_cases hk : k = 205 <;> by_cases hk240 : k = 240 <;>
      simp [SubexpLagrangeNormalize.finalStore, s4, s5, Function.update_apply, hk, hk240,
        h205, R, row, A, SubexpLagrangeNormalize.encode, encode]
  rw [hs5] at h5 H5
  have hR : R.length = D := hlen
  have hbits : ∀ w ∈ bits, w.length = (s 104).length := by
    intro w hw
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hw
    rw [SubexpFlatAdd.encode_length, H.workspace 104 (by decide)]
    exact List.length_replicate.symm
  have hrow := SubexpLagrangeCacheRows.writeRow_run s5 (s 104) bits cache hbits
    (by rfl) (by simp [s5]) (by simpa [s5, bits, hR] using H.dimension)
    (by simpa [s5] using hcache)
    (by simpa [s5, SubexpLagrangeCacheWorkspace.layout] using H.workspace 120 (by decide))
    (by
      intro k hk
      have hmem : k ∈ ([205, 215, 216, 218, 226, 229, 230, 231, 232, 233, 234, 235,
          240, 247, 249] : List (Fin 256)) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      have hfresh := H.fresh k hmem
      have hk240 : k ≠ 240 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simpa [s5, hk240] using hfresh) r5
  obtain ⟨n6, r6, hn6, h6⟩ := hrow
  let s6 := Function.update s 250 (Subexp.FactorPacketCoordinates.cacheBytes (bits :: cache))
  have hs6 : SubexpLagrangeCacheRows.rowOutput s5 bits cache = s6 := by
    funext k
    by_cases hk : k = 240 <;> simp [SubexpLagrangeCacheRows.rowOutput, s6, s5,
      Function.update_apply, hk, h240]
  rw [hs6] at h6
  have hn6' : n6 ≤ 100 * (D + 1) * (4 * B + 1) := by
    have h := hn6.trans (SubexpLagrangeCacheRows.rowCost_le (s 104) bits hbits)
    simpa [bits, hR, H.workspace 104 (by decide), layout, B] using h
  have H6 : Ready M.bits width (SubexpQuarticFlatMul.flat t) B s6 :=
    H.workspace.update 250 (by decide) _
  have hadd := SubexpLagrangeScalarCalls.addTo_run p μ M s6 217 207 217
    (by decide) (by decide) (by decide) (by decide)
    (label p μ M zero one i) one width (fun _ => []) H.width_eq
    (by simpa [s6] using H.label_eq) (by simpa [s6] using H.one_eq)
    H6.low (H6 120 (by decide)) (by simpa [s6] using h245) r6
  obtain ⟨n7, r7, hn7, h7⟩ := hadd
  let s7 := Function.update s6 217 (SubexpFlatAdd.encode (label p μ M zero one (i + 1)))
  change Eval (SubexpLagrangeCacheControl.increment 217) n7 ⟨r6, s6⟩ ⟨r7, s7⟩ at h7
  obtain ⟨n8, r8, hn8, h8⟩ := appendIndex_run 248 s7 r7
  have hs8 : Function.update s7 248 (false :: s7 248) = output p μ M s zero one i bits cache := by
    simp only [s7, s6, Function.update_of_ne (show (248 : Fin 256) ≠ 217 by decide),
      Function.update_of_ne (show (248 : Fin 256) ≠ 250 by decide), H.index_eq,
      output, List.replicate_succ]
  rw [hs8] at h8
  have hall := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq h8))))))
  refine ⟨n1 + (n2 + (n3 + (n4 + (n5 + (n6 + (n7 + n8)))))), r8, inverse,
    ?_, hall, hinverse, hR⟩
  have hsize : (s6 217).length = 4 * B := by
    simp [s6, H.label_eq, SubexpFlatAdd.encode_length, B]
  rw [hsize] at hn7
  unfold budget
  dsimp only [B] at hn3 hn6' hn7
  omega

end SubexponentialSAT.SubexpLagrangeCacheRow

end OAI.Algorithms
