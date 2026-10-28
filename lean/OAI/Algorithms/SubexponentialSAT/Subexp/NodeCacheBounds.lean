import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTaylorCacheMap
import OAI.Algorithms.SubexponentialSAT.SubexpOriginMap

namespace OAI.Algorithms

/-! Explicit polynomial bounds for the actual Taylor-cache and origin-map
programs before template construction. No template iteration count occurs. -/
namespace SubexponentialSAT.Subexp.NodeCacheBounds

def scale (m C R N B b modulusLen : ℕ) : ℕ :=
  m+C+R+N+B+b+modulusLen+1

private theorem taylor_diagonal (S : ℕ) :
    SubexpTaylorCacheMap.tableBudget S S S S S =
      500000*S^6+1500132*S^5+1500967*S^4+500189*S^3+201*S^2+103*S+24 := by
  unfold SubexpTaylorCacheMap.tableBudget SubexpTaylorCacheMap.incidenceIterationBudget
    SubexpTaylorCacheMap.incidenceCallbackBudget SubexpTaylorCacheMap.coordinateBudget
    SubexpTaylorCacheMap.incidenceInputBound SubexpTaylorCacheMap.incidenceOutputBound
    SubexpTaylorCacheCalls.rowCallbackBudget SubexpTaylorRow.budget
    SubexpTaylorProgram.scalarBound
  ring

theorem tableBudget_le_uniform {m C R N B S : ℕ}
    (hm : m ≤ S) (hC : C ≤ S) (hR : R ≤ S) (hN : N ≤ S) (hB : B ≤ S) (hS : 1 ≤ S) :
    SubexpTaylorCacheMap.tableBudget m C R N B ≤ 4001616*S^6 := by
  have hmono : SubexpTaylorCacheMap.tableBudget m C R N B ≤
      SubexpTaylorCacheMap.tableBudget S S S S S := by
    unfold SubexpTaylorCacheMap.tableBudget SubexpTaylorCacheMap.incidenceIterationBudget
      SubexpTaylorCacheMap.incidenceCallbackBudget SubexpTaylorCacheMap.coordinateBudget
      SubexpTaylorCacheMap.incidenceInputBound SubexpTaylorCacheMap.incidenceOutputBound
      SubexpTaylorCacheCalls.rowCallbackBudget SubexpTaylorRow.budget
      SubexpTaylorProgram.scalarBound
    gcongr
  rw [taylor_diagonal] at hmono
  have h0 : 1 ≤ S^6 := Nat.one_le_pow _ _ hS
  have h1 : S ≤ S^6 := by simpa using Nat.pow_le_pow_right hS (by decide : 1 ≤ 6)
  have h2 : S^2 ≤ S^6 := Nat.pow_le_pow_right hS (by decide)
  have h3 : S^3 ≤ S^6 := Nat.pow_le_pow_right hS (by decide)
  have h4 : S^4 ≤ S^6 := Nat.pow_le_pow_right hS (by decide)
  have h5 : S^5 ≤ S^6 := Nat.pow_le_pow_right hS (by decide)
  omega

/-- The row input degree is `R+1`, exactly as used by the node worker. -/
theorem tableBudget_le (m C R N B b modulusLen : ℕ) :
    SubexpTaylorCacheMap.tableBudget m C (R+1) N B ≤
      4001616*(scale m C R N B b modulusLen)^6 := by
  apply tableBudget_le_uniform <;> unfold scale <;> omega

def cacheOutputBound (m C N B : ℕ) : ℕ :=
  1+4*m+((32*B+8)*N+8)*(m*C)

private theorem sum_lengths_le {A : Type*} (rows : List (List A)) (C : ℕ)
    (hC : ∀ row ∈ rows, row.length ≤ C) :
    (rows.map List.length).sum ≤ rows.length*C := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
      have hr := hC row (by simp)
      have ht := ih (fun xs hx => hC xs (by simp [hx]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith

section CacheBytes

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
variable (t theta : SubexpTaylorRow.Code p μ)

omit [Fact p.Prime] in
/-- Exact bytes of the nested cache produced by the physical Taylor map.
Each coordinate contributes precisely `N` coefficients. -/
theorem cacheBytes_length (N : ℕ)
    (rows : List (List (List (SubexpTaylorRow.Code p μ)))) :
    (SubexpTaylorCacheControl.encodeCache SubexpTaylorRow.flat
      (SubexpTaylorCacheMap.caches p μ M t theta N rows)).length =
      1+4*rows.length+((32*SubexpLiftRing.baseWidth p μ+8)*N+8)*
        (rows.map List.length).sum := by
  rw [SubexpTaylorCacheMap.encoded_caches]
  induction rows with
  | nil => simp
  | cons coordinates rows ih =>
      rw [Encoding.length_encodeList_cons,
        SubexpTaylorCacheMap.incidenceCacheBytes_length,ih]
      simp only [List.length_cons,List.map_cons,List.sum_cons,
        SubexpTaylorCacheMap.incidenceOutputBound]
      ring

omit [Fact p.Prime] in
theorem cacheBytes_le_counts (m C N B : ℕ)
    (rows : List (List (List (SubexpTaylorRow.Code p μ))))
    (hm : rows.length ≤ m) (hC : ∀ coordinates ∈ rows, coordinates.length ≤ C)
    (hB : SubexpLiftRing.baseWidth p μ ≤ B) :
    (SubexpTaylorCacheControl.encodeCache SubexpTaylorRow.flat
      (SubexpTaylorCacheMap.caches p μ M t theta N rows)).length ≤
      cacheOutputBound m C N B := by
  have hs : (rows.map List.length).sum ≤ m*C :=
    (sum_lengths_le rows C hC).trans (Nat.mul_le_mul_right C hm)
  rw [cacheBytes_length]
  unfold cacheOutputBound
  gcongr

end CacheBytes

theorem cacheOutputBound_le_uniform {m C N B S : ℕ}
    (hm : m ≤ S) (hC : C ≤ S) (hN : N ≤ S) (hB : B ≤ S) (hS : 1 ≤ S) :
    cacheOutputBound m C N B ≤ 53*S^4 := by
  have hmono : cacheOutputBound m C N B ≤ cacheOutputBound S S S S := by
    unfold cacheOutputBound
    gcongr
  have heq : cacheOutputBound S S S S = 32*S^4+8*S^3+8*S^2+4*S+1 := by
    unfold cacheOutputBound
    ring
  rw [heq] at hmono
  have h0 : 1 ≤ S^4 := Nat.one_le_pow _ _ hS
  have h1 : S ≤ S^4 := by simpa using Nat.pow_le_pow_right hS (by decide : 1 ≤ 4)
  have h2 : S^2 ≤ S^4 := Nat.pow_le_pow_right hS (by decide)
  have h3 : S^3 ≤ S^4 := Nat.pow_le_pow_right hS (by decide)
  omega

theorem cacheOutputBound_le (m C R N B b modulusLen : ℕ) :
    cacheOutputBound m C N B ≤ 53*(scale m C R N B b modulusLen)^4 := by
  apply cacheOutputBound_le_uniform <;> unfold scale <;> omega

/-- Input row lengths do not enter this bound: the actual cache operation
retains exactly `N` coefficients in every output coordinate. -/
theorem cacheBytes_le (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (t theta : SubexpTaylorRow.Code p μ) (m C R N B b modulusLen : ℕ)
    (rows : List (List (List (SubexpTaylorRow.Code p μ))))
    (hm : rows.length ≤ m) (hC : ∀ coordinates ∈ rows, coordinates.length ≤ C)
    (hB : SubexpLiftRing.baseWidth p μ ≤ B) :
    (SubexpTaylorCacheControl.encodeCache SubexpTaylorRow.flat
      (SubexpTaylorCacheMap.caches p μ M t theta N rows)).length ≤
      53*(scale m C R N B b modulusLen)^4 :=
  (cacheBytes_le_counts p μ M t theta m C N B rows hm hC hB).trans
    (cacheOutputBound_le m C R N B b modulusLen)

private theorem origin_diagonal (S : ℕ) :
    SubexpOriginMap.polynomialBound S = 2056*S^4+2582*S^3+815*S^2+103*S+24 := by
  unfold SubexpOriginMap.polynomialBound SubexpOriginMap.tableBound
    SubexpOriginMap.iterationsBound SubexpOriginMap.incidenceBound
    SubexpOriginMap.incidenceInputBound SubexpOriginMap.incidenceOutputBound
    SubexpOriginMap.coordinatesBound SubexpOriginMap.coordinateBound
    SubexpOriginMap.rowBound SubexpOriginMap.tailBound
    SubexpOriginQuadProgram.cost SubexpFlatLift.wordCost SubexpWordLiftMachine.runtimeBound
  ring

theorem originTableBound_le_uniform {m C B b modulusLen R S : ℕ}
    (hm : m ≤ S) (hC : C ≤ S) (hB : B ≤ S) (hb : b ≤ S)
    (hmod : modulusLen ≤ S) (hR : R ≤ S) (hS : 1 ≤ S) :
    SubexpOriginMap.tableBound m C B b modulusLen R ≤ 5580*S^4 := by
  have hmono := SubexpOriginMap.tableBound_le hm hC hB hb hmod hR
  rw [origin_diagonal] at hmono
  have h0 : 1 ≤ S^4 := Nat.one_le_pow _ _ hS
  have h1 : S ≤ S^4 := by simpa using Nat.pow_le_pow_right hS (by decide : 1 ≤ 4)
  have h2 : S^2 ≤ S^4 := Nat.pow_le_pow_right hS (by decide)
  have h3 : S^3 ≤ S^4 := Nat.pow_le_pow_right hS (by decide)
  omega

/-- The origin map sees the `N-1` tail of each retained Taylor row. -/
theorem originTableBound_le (m C R N B b modulusLen : ℕ) :
    SubexpOriginMap.tableBound m C B b modulusLen (N-1) ≤
      5580*(scale m C R N B b modulusLen)^4 := by
  apply originTableBound_le_uniform <;> unfold scale <;> omega

end SubexponentialSAT.Subexp.NodeCacheBounds

#print axioms SubexponentialSAT.Subexp.NodeCacheBounds.tableBudget_le
#print axioms SubexponentialSAT.Subexp.NodeCacheBounds.cacheBytes_le
#print axioms SubexponentialSAT.Subexp.NodeCacheBounds.originTableBound_le

end OAI.Algorithms
