import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter

/-! Fixed polynomial overhead for the actual marked-mass command. The query
cost bound is charged for every original clause reference, including the last. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassBounds

open SqrtLog HashMassAdapter

/-- The actual generated unary index has at most m bits when its index is
strictly below m. No exponential reference table is present. -/
theorem reference_length (m : ℕ) (bits : List Bool)
    (hb : bits ∈ RowSelectionProgram.Index.alphabet m) : bits.length ≤ m := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
  have hj' : j < m := by simpa using hj
  simp only [Encoding.length_encodeNat]
  omega

theorem reference_bound (f : List Bool → ℕ) (m B : ℕ)
    (hf : ∀ e : Fin m, f (Encoding.encodeNat e.val) ≤ B) :
    ∀ bits ∈ RowSelectionProgram.Index.alphabet m, f bits ≤ B := by
  intro bits hb
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
  exact hf ⟨j, by simpa using hj⟩

theorem input_size_le (width : List Bool → ℕ) (m W : ℕ)
    (hw : ∀ e : Fin m, width (Encoding.encodeNat e.val) ≤ W) :
    valueInputSize width (RowSelectionProgram.Index.alphabet m) ≤ m * (m + W + 1) := by
  have h := List.sum_le_length_nsmul
    ((RowSelectionProgram.Index.alphabet m).map fun bits => bits.length + width bits + 1)
    (m + W + 1) (by
      intro x hx
      obtain ⟨bits, hb, rfl⟩ := List.mem_map.mp hx
      have hl := reference_length m bits hb
      have hw' := reference_bound width m W hw bits hb
      omega)
  simp only [valueInputSize, List.length_map, RowSelectionProgram.Index.alphabet_length,
    nsmul_eq_mul] at h ⊢
  omega

theorem query_sum_le (queryCost : List Bool → ℕ) (m T : ℕ)
    (ht : ∀ e : Fin m, queryCost (Encoding.encodeNat e.val) ≤ T) :
    ((RowSelectionProgram.Index.alphabet m).map queryCost).sum ≤ m * T := by
  have h := List.sum_le_length_nsmul
    ((RowSelectionProgram.Index.alphabet m).map queryCost) T
    (by
      intro x hx
      obtain ⟨bits, hb, rfl⟩ := List.mem_map.mp hx
      exact reference_bound queryCost m T ht bits hb)
  simpa using h

/-- A fixed cube suffices for all paid reference production, parser, additions,
normalization, routing and cleanup around the uniformly charged query cost. -/
theorem massBudget_le (a : HashMassAdapter.Data) (queryCost width : List Bool → ℕ)
    (m W D T : ℕ) (hm : CounterPrograms.value (a.stacks 782) = m)
    (h0 : (a.stacks 0).length ≤ D) (h782 : (a.stacks 782).length ≤ D)
    (h769 : (a.stacks 769).length ≤ D)
    (hw : ∀ e : Fin m, width (Encoding.encodeNat e.val) ≤ W)
    (ht : ∀ e : Fin m, queryCost (Encoding.encodeNat e.val) ≤ T) :
    massBudget a queryCost width m ≤ 1000 * (m + W + D + 1) ^ 3 * (T + 1) := by
  let S := m + W + D + 1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hmS : m ≤ S := by dsimp [S]; omega
  have hm1S : m + 1 ≤ S := by dsimp [S]; omega
  have hWS : W + 1 ≤ S := by dsimp [S]; omega
  have hDS : D + 1 ≤ S := by dsimp [S]; omega
  have hsumS : m + W + 1 ≤ S := by dsimp [S]; omega
  have hS2 : S ≤ S ^ 2 := by nlinarith
  have hS3 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by decide)
  have h1S3 : 1 ≤ S ^ 3 := hS.trans (hS2.trans hS3)
  have hLS : (a.stacks 782).length + 1 ≤ S := by omega
  have hcore : CounterConversions.coreBound (a.stacks 782) ≤ 26 * S ^ 2 := by
    have hprod : (m + 1) * ((a.stacks 782).length + 1) ≤ S ^ 2 := by
      simpa only [pow_two] using Nat.mul_le_mul hm1S hLS
    rw [CounterConversions.coreBound, hm]
    nlinarith only [hprod, hS2, hS, hmS, hLS]
  have hroute : LeafOuterProgram.routeCost (782,0) a ≤ 17 * S ^ 2 := by
    simp only [LeafOuterProgram.routeCost]
    nlinarith only [h0, h782, hDS, hS2, hS]
  have hreference : LeafOuterNative.References.budget (a.stacks 782) ≤ 78 * S ^ 2 := by
    have hmsquare : m * m ≤ S * S := Nat.mul_le_mul hmS hmS
    unfold LeafOuterNative.References.budget
    rw [hm]
    nlinarith only [hcore, hmsquare, hmS, hS2, hS]
  have hsetup : LeafOuterProgram.routeCost (782,0) a +
      LeafOuterNative.References.budget (a.stacks 782) + 1 ≤ 100 * S ^ 2 := by nlinarith only [hroute, hreference, hS, hS2]
  have hin := input_size_le width m W hw
  have hinput : valueInputSize width (RowSelectionProgram.Index.alphabet m) ≤ S ^ 2 := by
    have hp : m * (m + W + 1) ≤ S * S := Nat.mul_le_mul hmS hsumS
    exact hin.trans (by simpa only [pow_two] using hp)
  have hq := query_sum_le queryCost m T ht
  have hqS : ((RowSelectionProgram.Index.alphabet m).map queryCost).sum ≤ S * T :=
    hq.trans (Nat.mul_le_mul_right T hmS)
  have hval : valueBudget queryCost width (RowSelectionProgram.Index.alphabet m) [] ≤
      4 + S * T + S * (22 * S ^ 2 + 26) := by
    unfold valueBudget
    simp only [List.length_nil, Nat.zero_add, RowSelectionProgram.Index.alphabet_length]
    have hp : m * (22 * valueInputSize width (RowSelectionProgram.Index.alphabet m) + 26) ≤
        S * (22 * S ^ 2 + 26) := Nat.mul_le_mul hmS (by omega)
    exact Nat.add_le_add (Nat.add_le_add_left hqS 4) hp
  have hg := outputGrowth_le width (RowSelectionProgram.Index.alphabet m) W
    (reference_bound width m W hw)
  have hgS : outputGrowth width (RowSelectionProgram.Index.alphabet m) ≤ S ^ 2 := by
    have hp : m * (W + 1) ≤ S * S := Nat.mul_le_mul hmS hWS
    simp only [RowSelectionProgram.Index.alphabet_length] at hg
    exact hg.trans (by simpa only [pow_two] using hp)
  have hfinish : 50 * (outputGrowth width (RowSelectionProgram.Index.alphabet m) +
      (a.stacks 769).length + 1) ≤ 150 * S ^ 2 := by
    nlinarith only [hgS, h769, hDS, hS2, hS]
  have hST : S * T ≤ S ^ 3 * T := Nat.mul_le_mul_right T (hS2.trans hS3)
  change massBudget a queryCost width m ≤ 1000 * S ^ 3 * (T + 1)
  unfold massBudget
  nlinarith only [hsetup, hval, hfinish, hST, hS2, hS3, h1S3, hS]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassBounds
