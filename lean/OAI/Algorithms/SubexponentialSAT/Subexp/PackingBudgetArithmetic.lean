import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpVertexPairComplexity

namespace OAI.Algorithms

/-! Numerical envelopes for the actual packing stages. Every argument below
is a size of an input or a bound established for a generated value. -/

namespace SubexponentialSAT.Subexp.PackingBudgetArithmetic

theorem le_power {S k : ℕ} (hS : 1 ≤ S) (hk : 1 ≤ k) : S ≤ S ^ k := by
  simpa only [pow_one] using Nat.pow_le_pow_right hS hk

theorem plan_wordBound_le (D Δ S : ℕ) (scopes : List (List ℕ))
    (h : D + scopes.length + Δ + (SubexpPlanAlphabetBase.scopeBytes scopes).length + 1 ≤ S) :
    SubexpPlanAlphabetBase.planWordBound D Δ scopes ≤ 7 * S ^ 3 := by
  have hS : 1 ≤ S := by omega
  have hD : D ≤ S := by omega
  have hE : scopes.length ≤ S := by omega
  have hd : Δ + 1 ≤ S := by omega
  have h2 : S ≤ S ^ 2 := le_power hS (by decide)
  have h3 : S ≤ S ^ 3 := le_power hS (by decide)
  have hm : scopes.length + (Δ + 1) * D ≤ 2 * S ^ 2 := by
    have hp : (Δ + 1) * D ≤ S ^ 2 := by
      simpa only [pow_two] using Nat.mul_le_mul hd hD
    omega
  calc
    _ ≤ 1 + (2 * (2 * S ^ 2) + 2) * S := by
      unfold SubexpPlanAlphabetBase.planWordBound
      gcongr
    _ ≤ 7 * S ^ 3 := by ring_nf; omega

theorem plan_totalBound_le (D Δ S : ℕ) (scopes : List (List ℕ))
    (h : D + scopes.length + Δ + (SubexpPlanAlphabetBase.scopeBytes scopes).length + 1 ≤ S)
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    SubexpPlanAlphabetBase.totalBound D Δ scopes ≤ 10100 * S ^ 4 := by
  have hS : 1 ≤ S := by omega
  have hD : D ≤ S := by omega
  have hE : scopes.length ≤ S := by omega
  have hdS : Δ ≤ S := by omega
  have h2 : S ≤ S ^ 2 := le_power hS (by decide)
  have h3 : S ≤ S ^ 3 := le_power hS (by decide)
  have h4 : S ≤ S ^ 4 := le_power hS (by decide)
  have h23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by decide)
  have h24 : S ^ 2 ≤ S ^ 4 := Nat.pow_le_pow_right hS (by decide)
  have hp := plan_wordBound_le D Δ S scopes h
  have hi : SubexpIncidencePlanProgram.inputSize D Δ D scopes ≤ 2 * S := by
    change (SubexpPlanAlphabetBase.scopeBytes scopes).length + D + Δ + D + 1 ≤ 2 * S
    omega
  have hc : (SubexpPlanAlphabetBase.scopeBytes scopes).length + D + Δ + D ≤ 2 * S := by
    change (SubexpPlanAlphabetBase.scopeBytes scopes).length + D + Δ + D + 1 ≤ 2 * S at hi
    omega
  have hm : D * Δ ≤ S ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul hD hdS
  have he : 2 * scopes.length + 2 * D + D * Δ + 3 * Δ + 3 * D + 1 ≤ 12 * S ^ 2 := by
    omega
  have hu : SubexpPlanAlphabetBase.uniformCallbackBound D Δ scopes ≤ 10000 * S ^ 3 := by
    calc
      _ ≤ 1000 * (2 * S) ^ 3 + 7 * (2 * S) + 34 * (7 * S ^ 3) +
          2 * (12 * S ^ 2) + 106 := by
        unfold SubexpPlanAlphabetBase.uniformCallbackBound
        gcongr
      _ ≤ 10000 * S ^ 3 := by ring_nf; omega
  apply (SubexpPlanAlphabetBase.totalBound_le_polynomial D Δ scopes hd).trans
  calc
    _ ≤ 6 * S ^ 2 + 17 * S + 15 + S * (6 * S + 10000 * S ^ 3 + 7) := by
      unfold SubexpPlanAlphabetBase.polynomialBound
      gcongr
    _ ≤ 10100 * S ^ 4 := by ring_nf; omega

theorem plan_stream_le (S D H : ℕ) (hS : 1 ≤ S) (hD : D ≤ S) (hH : H ≤ 7 * S ^ 3) :
    1 + (4 * H + 4) * D ≤ 33 * S ^ 4 := by
  have h4 : S ≤ S ^ 4 := le_power hS (by decide)
  calc
    _ ≤ 1 + (4 * (7 * S ^ 3) + 4) * S := by gcongr
    _ ≤ 33 * S ^ 4 := by ring_nf; omega

theorem label_trace_le (S D W H : ℕ) (hS : 1 ≤ S) (hD : D ≤ S)
    (hW : W ≤ S) (hH : H ≤ 7 * S ^ 3) :
    4 + D * (12 * H + 13 + 200 * (W + H + 0 + D + 1) ^ 2) ≤ 21000 * S ^ 7 := by
  have h3 : S ≤ S ^ 3 := le_power hS (by decide)
  have h7 : S ≤ S ^ 7 := le_power hS (by decide)
  have h47 : S ^ 4 ≤ S ^ 7 := Nat.pow_le_pow_right hS (by decide)
  have hh : W + H + 0 + D + 1 ≤ 10 * S ^ 3 := by omega
  calc
    _ ≤ 4 + S * (12 * (7 * S ^ 3) + 13 + 200 * (10 * S ^ 3) ^ 2) := by gcongr
    _ ≤ 21000 * S ^ 7 := by ring_nf; omega

theorem type_stream_le (S N : ℕ) (hS : 1 ≤ S) (hN : N ≤ S) :
    1 + (2 * S ^ 2 + 2) * N ≤ 5 * S ^ 3 := by
  have h3 : S ≤ S ^ 3 := le_power hS (by decide)
  calc
    _ ≤ 1 + (2 * S ^ 2 + 2) * S := by gcongr
    _ ≤ 5 * S ^ 3 := by ring_nf; omega

theorem type_cost_le (S n N W : ℕ) (hS : 1 ≤ S) (hn : n ≤ S)
    (hN : N ≤ S) (hW : W ≤ S) :
    800 * (n + 1) * (N + 1) * ((n + 1) * W + 1) + 12 ≤ 10012 * S ^ 4 := by
  have h2 : S ≤ S ^ 2 := le_power hS (by decide)
  have h4 : S ≤ S ^ 4 := le_power hS (by decide)
  have hn' : n + 1 ≤ 2 * S := by omega
  have hN' : N + 1 ≤ 2 * S := by omega
  have hh : (n + 1) * W + 1 ≤ 3 * S ^ 2 := by
    calc
      _ ≤ (2 * S) * S + 1 := by gcongr
      _ ≤ 3 * S ^ 2 := by ring_nf; omega
  calc
    _ ≤ 800 * (2 * S) * (2 * S) * (3 * S ^ 2) + 12 := by gcongr
    _ ≤ 10012 * S ^ 4 := by ring_nf; omega

theorem frontend_le (S B D Δ W F A P L C T : ℕ) (hS : 1 ≤ S)
    (hB : B ≤ S) (hD : D ≤ S) (hd : Δ ≤ S) (hW : W ≤ S) (hF : F ≤ S) (hA : A ≤ S)
    (hP : P ≤ 33 * S ^ 4) (hL : L ≤ 21000 * S ^ 7)
    (hC : C ≤ 10012 * S ^ 4) (hT : T ≤ 5 * S ^ 3) :
    (10100 * S ^ 4 + 9 * B + 11 * D + 9 * Δ + 6 * P + 34) +
    (21000 * S ^ 7 + 9 * F + 9 * W + 6 * P + 6 * L + 2 * D + 31) +
    (C + 9 * A + 7 * Δ + 6 * T + 24) ≤ 200000 * S ^ 7 := by
  have h7 : S ≤ S ^ 7 := le_power hS (by decide)
  have h37 : S ^ 3 ≤ S ^ 7 := Nat.pow_le_pow_right hS (by decide)
  have h47 : S ^ 4 ≤ S ^ 7 := Nat.pow_le_pow_right hS (by decide)
  calc
    _ ≤ (10100 * S ^ 4 + 9 * S + 11 * S + 9 * S + 6 * (33 * S ^ 4) + 34) +
        (21000 * S ^ 7 + 9 * S + 9 * S + 6 * (33 * S ^ 4) + 6 * (21000 * S ^ 7) + 2 * S + 31) +
        (10012 * S ^ 4 + 9 * S + 7 * S + 6 * (5 * S ^ 3) + 24) := by gcongr
    _ ≤ 200000 * S ^ 7 := by omega

theorem bucket_payload_le (S L : ℕ) (hS : 1 ≤ S) (hL : L ≤ 21000 * S ^ 7) :
    2 * S ^ 2 + 1 + L ≤ 21003 * S ^ 7 := by
  have h7 : S ≤ S ^ 7 := le_power hS (by decide)
  have h27 : S ^ 2 ≤ S ^ 7 := Nat.pow_le_pow_right hS (by decide)
  omega

theorem bucket_table_le (S N L : ℕ) (hS : 1 ≤ S) (hN : N ≤ S)
    (hL : L ≤ 21000 * S ^ 7) :
    1 + (2 * (2 * S ^ 2 + 1 + L) + 2) * N ≤ 43000 * S ^ 8 := by
  have h8 : S ≤ S ^ 8 := le_power hS (by decide)
  have hp := bucket_payload_le S L hS hL
  calc
    _ ≤ 1 + (2 * (21003 * S ^ 7) + 2) * S := by gcongr
    _ ≤ 43000 * S ^ 8 := by ring_nf; omega

theorem bucket_core_le (S N L : ℕ) (hS : 1 ≤ S) (hN : N ≤ S)
    (hL : L ≤ 21000 * S ^ 7) :
    9 + N * (6 * S ^ 2 + 100 * (L + 1) * (S ^ 2 + 1) + 7) +
      3 * (1 + (2 * (2 * S ^ 2 + 1 + L) + 2) * N) ≤ 4400000 * S ^ 10 := by
  have h7 : S ≤ S ^ 7 := le_power hS (by decide)
  have h2 : S ≤ S ^ 2 := le_power hS (by decide)
  have h10 : S ≤ S ^ 10 := le_power hS (by decide)
  have h310 : S ^ 3 ≤ S ^ 10 := Nat.pow_le_pow_right hS (by decide)
  have h810 : S ^ 8 ≤ S ^ 10 := Nat.pow_le_pow_right hS (by decide)
  have hL' : L + 1 ≤ 21001 * S ^ 7 := by omega
  have hW : S ^ 2 + 1 ≤ 2 * S ^ 2 := by omega
  have ht := bucket_table_le S N L hS hN hL
  calc
    _ ≤ 9 + S * (6 * S ^ 2 + 100 * (21001 * S ^ 7) * (2 * S ^ 2) + 7) +
        3 * (43000 * S ^ 8) := by gcongr
    _ ≤ 4400000 * S ^ 10 := by ring_nf; omega

theorem bucket_stage_le (S L T D K M C : ℕ) (hS : 1 ≤ S)
    (hL : L ≤ 21000 * S ^ 7) (hT : T ≤ 5 * S ^ 3) (hD : D ≤ S)
    (hK : K ≤ 43000 * S ^ 8) (hM : M ≤ S) (hC : C ≤ 4400000 * S ^ 10) :
    8 * L + 6 * T + 7 * D + 6 * K + 6 * M + 32 + C ≤ 5000000 * S ^ 10 := by
  have h10 : S ≤ S ^ 10 := le_power hS (by decide)
  have h310 : S ^ 3 ≤ S ^ 10 := Nat.pow_le_pow_right hS (by decide)
  have h710 : S ^ 7 ≤ S ^ 10 := Nat.pow_le_pow_right hS (by decide)
  have h810 : S ^ 8 ≤ S ^ 10 := Nat.pow_le_pow_right hS (by decide)
  omega

theorem extraction_loop_le (S n N K B : ℕ) (hS : 1 ≤ S) (hn : n ≤ S) (hN : N ≤ S)
    (hK : K ≤ 43000 * S ^ 8) (hB : B ≤ 21003 * S ^ 7) :
    1 + n * (7 * K + N * (106 * B + 100 * S + 100 * S ^ 2 + 207) + 13) ≤
      2700000 * S ^ 9 := by
  have h7 : S ≤ S ^ 7 := le_power hS (by decide)
  have h9 : S ≤ S ^ 9 := le_power hS (by decide)
  have h27 : S ^ 2 ≤ S ^ 7 := Nat.pow_le_pow_right hS (by decide)
  have hu : 106 * B + 100 * S + 100 * S ^ 2 + 207 ≤ 2300000 * S ^ 7 := by omega
  calc
    _ ≤ 1 + S * (7 * (43000 * S ^ 8) + S * (2300000 * S ^ 7) + 13) := by gcongr
    _ ≤ 2700000 * S ^ 9 := by ring_nf; omega

theorem metadata_le (S D T : ℕ) (hS : 1 ≤ S) (hD : D ≤ S) (hT : T ≤ 5 * S ^ 3) :
    D * (6 * D + 4 * T + 8) ≤ 34 * S ^ 4 := by
  have h4 : S ≤ S ^ 4 := le_power hS (by decide)
  have h24 : S ^ 2 ≤ S ^ 4 := Nat.pow_le_pow_right hS (by decide)
  calc
    _ ≤ S * (6 * S + 4 * (5 * S ^ 3) + 8) := by gcongr
    _ ≤ 34 * S ^ 4 := by ring_nf; omega

theorem extraction_stage_le (S C n K M : ℕ) (hS : 1 ≤ S)
    (hC : C ≤ 2700000 * S ^ 9) (hn : n ≤ S)
    (hK : K ≤ 43000 * S ^ 8) (hM : M ≤ 34 * S ^ 4) :
    C + 6 * n + 2 * K + 7 * M + 16 ≤ 2800000 * S ^ 9 := by
  have h9 : S ≤ S ^ 9 := le_power hS (by decide)
  have h49 : S ^ 4 ≤ S ^ 9 := Nat.pow_le_pow_right hS (by decide)
  have h89 : S ^ 8 ≤ S ^ 9 := Nat.pow_le_pow_right hS (by decide)
  omega

theorem tail_le (S D T : ℕ) (hS : 1 ≤ S) (hD : D ≤ S) (hT : T ≤ 5 * S ^ 3) :
    30000 * (D + T + 1) ^ 4 ≤ 72030000 * S ^ 12 := by
  have h3 : S ≤ S ^ 3 := le_power hS (by decide)
  have hb : D + T + 1 ≤ 7 * S ^ 3 := by omega
  calc
    _ ≤ 30000 * (7 * S ^ 3) ^ 4 := by gcongr
    _ = _ := by ring

theorem final_le (S F B E V T : ℕ) (hS : 1 ≤ S)
    (hF : F ≤ 200000 * S ^ 7) (hB : B ≤ 5000000 * S ^ 10)
    (hE : E ≤ 2800000 * S ^ 9) (hV : V ≤ 400 * S ^ 2)
    (hT : T ≤ 72030000 * S ^ 12) :
    F + B + E + V + T + 1 ≤ 81000000 * S ^ 12 := by
  have h12 : S ≤ S ^ 12 := le_power hS (by decide)
  have h212 : S ^ 2 ≤ S ^ 12 := Nat.pow_le_pow_right hS (by decide)
  have h712 : S ^ 7 ≤ S ^ 12 := Nat.pow_le_pow_right hS (by decide)
  have h912 : S ^ 9 ≤ S ^ 12 := Nat.pow_le_pow_right hS (by decide)
  have h1012 : S ^ 10 ≤ S ^ 12 := Nat.pow_le_pow_right hS (by decide)
  omega

end SubexponentialSAT.Subexp.PackingBudgetArithmetic

end OAI.Algorithms
