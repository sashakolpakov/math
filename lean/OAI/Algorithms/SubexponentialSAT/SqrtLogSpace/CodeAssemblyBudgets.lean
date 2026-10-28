import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchNativeBudgets

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeAssemblyBudgets
open SqrtLog NativeCodeAssembly CodeSearchNativeBudgets

/-- The serializer is polynomial in the physical metadata boundary, including
its unary vertex word and both complete retained code matrices. -/
theorem afterBoundary_le (A m B : ℕ) (dword mword width : List Bool)
    (hA : 1 ≤ A) (hr : SparseCode.dimension m B ≤ A)
    (hD : SparseCode.degree m B ≤ A) (ht : SparseCode.localRows m B ≤ A)
    (hdword : dword.length ≤ A) (hmword : mword.length ≤ A)
    (hwidth : width.length ≤ A) (hvertices : 2 ^ SparseCode.dimension m B ≤ A)
    (hg : SparseCode.degree m B * SparseCode.dimension m B ≤ A)
    (hl : SparseCode.localRows m B * SparseCode.degree m B ≤ A) :
    afterBoundary A m B dword mword width ≤ 10000000000000000 * A ^ 5 := by
  have hb := (searchBoundary_le A m B hg hl).2
  have h := serializerTime_polynomial (r := SparseCode.dimension m B)
    (D := SparseCode.degree m B) (t := SparseCode.localRows m B)
    (W := NativeCode.searchBoundary A m B) (S := 15 * A) dword mword width
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  change afterBoundary A m B dword mword width ≤ _ at h
  nlinarith only [h]

/-- Actual unary metadata discharges every code-dimension premise. -/
theorem metadata_afterSpace_le {m B A : ℕ} (a : LeafOuterProgram.Data)
    (hmeta : LeafOuterProgram.Metadata m B a)
    (ha : ∀ i, (a.stacks i).length ≤ A) :
    afterSpace A m B (a.stacks 800).length (a.stacks 801)
      (a.stacks 782) (a.stacks 768) ≤ 20000000000000000 * A ^ 5 := by
  have hA := metadata_bound_pos a hmeta ha
  have hD := metadata_value_bound a hmeta ha 0
  have ht := metadata_value_bound a hmeta ha 1
  have hl := metadata_value_bound a hmeta ha 2
  have hd := metadata_value_bound a hmeta ha 3
  have hr := metadata_value_bound a hmeta ha 4
  have hg := metadata_value_bound a hmeta ha 5
  have hv := metadata_value_bound a hmeta ha 6
  change SparseCode.degree m B ≤ A at hD
  change SparseCode.localRows m B ≤ A at ht
  change SparseCode.localRows m B * SparseCode.degree m B ≤ A at hl
  change SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1 ≤ A at hd
  change SparseCode.dimension m B ≤ A at hr
  change SparseCode.dimension m B * SparseCode.degree m B ≤ A at hg
  rw [Nat.mul_comm] at hg
  change 2 ^ SparseCode.dimension m B ≤ A at hv
  have hs := searchesSpace_le A m B (a.stacks 800).length (a.stacks 801).length
    hA hD ht hd hr (ha 800) (ha 801) hg hl
  have hb := afterBoundary_le A m B (a.stacks 801) (a.stacks 782) (a.stacks 768)
    hA hr hD ht (ha 801) (ha 782) (ha 768) hv hg hl
  have hp : A ^ 2 ≤ A ^ 5 := Nat.pow_le_pow_right hA (by decide)
  unfold afterSpace
  exact max_le (hs.trans (Nat.mul_le_mul_left _ hp)) (by omega)

open SqrtLog.CodeSetupCost in
/-- Both full searches and serialization fit one fixed fifth power of the
original explicit code envelope and the physical metadata size. -/
theorem afterTime_le_envelope (A m B qlen H W : ℕ) (dword mword width : List Bool)
    (hA : 1 ≤ A) (hrA : SparseCode.dimension m B ≤ A)
    (hDA : SparseCode.degree m B ≤ A) (htA : SparseCode.localRows m B ≤ A)
    (hdword : dword.length ≤ A) (hmword : mword.length ≤ A)
    (hwidth : width.length ≤ A) (hvertices : 2 ^ SparseCode.dimension m B ≤ A)
    (hg : SparseCode.degree m B * SparseCode.dimension m B ≤ A)
    (hl : SparseCode.localRows m B * SparseCode.degree m B ≤ A)
    (ht : SparseCode.localRows m B ≤ H) (hD : SparseCode.degree m B ≤ H)
    (hd : SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1 ≤ H)
    (hr : SparseCode.dimension m B ≤ H) (hq : qlen ≤ W) (hDl : dword.length ≤ W) :
    afterTime A m B qlen dword mword width ≤
      20000000000000000 * (A + envelope 3000000000000 H W + 1) ^ 5 := by
  have hs := searchesTime_le_envelope A m B qlen dword.length H W ht hD hd hr hq hDl hg hl
  have hb := afterBoundary_le A m B dword mword width hA hrA hDA htA
    hdword hmword hwidth hvertices hg hl
  let X := A + envelope 3000000000000 H W + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hAX : A ≤ X := by dsimp [X]; omega
  have hp : X ^ 3 ≤ X ^ 5 := Nat.pow_le_pow_right hX (by decide)
  have hpA := Nat.pow_le_pow_left hAX 5
  change _ ≤ 20000000000000000 * X ^ 5
  unfold afterTime
  unfold afterBoundary at hb
  change NativeCode.searchesTime A m B qlen dword.length ≤ 5000000000 * X ^ 3 at hs
  nlinarith only [hs, hb, hp, hpA]

open SqrtLog.Statement
open Filter
open scoped Topology

/-- A fixed fifth power preserves the unchanged exponent scale. -/
theorem fifth_cost_runtimeBound (cost A E n C : ℕ)
    (hc : cost ≤ C * (A + E + 1) ^ 5)
    (he : (E : ℝ) ≤ (2 : ℝ) ^ runtimeScale n) :
    (cost : ℝ) ≤ runtimeBound (32 * (C : ℝ)) 5 5 A n := by
  let R : ℝ := (2 : ℝ) ^ runtimeScale n
  have hr1 : 1 ≤ R := Real.one_le_rpow (by norm_num) (runtimeScale_nonneg n)
  have hsum : (A : ℝ) + E + 1 ≤ 2 * ((A : ℝ) + 1) * R := by
    have hA : 0 ≤ (A : ℝ) := Nat.cast_nonneg A
    change (E : ℝ) ≤ R at he
    nlinarith
  have hc' : (cost : ℝ) ≤ (C : ℝ) * ((A : ℝ) + E + 1) ^ 5 := by exact_mod_cast hc
  calc
    _ ≤ (C : ℝ) * ((A : ℝ) + E + 1) ^ 5 := hc'
    _ ≤ (C : ℝ) * (2 * ((A : ℝ) + 1) * R) ^ 5 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀
        (add_nonneg (add_nonneg (Nat.cast_nonneg A) (Nat.cast_nonneg E)) zero_le_one) hsum 5)
        (Nat.cast_nonneg C)
    _ = runtimeBound (32 * (C : ℝ)) 5 5 A n := by
      unfold runtimeBound R
      rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast (by norm_num)]
      norm_num
      rw [mul_comm (runtimeScale n) 5]
      ring

open SqrtLog.Asymptotic SqrtLog.CodeSetupCost in
/-- One fixed cutoff covers every actual produced code metadata boundary.
Only its measured physical cap remains as the polynomial factor. -/
theorem eventually_produced_afterTime (q wordDegree : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (A m B : ℕ) (a : LeafOuterProgram.Data),
      0 < m → 0 < B → m ≤ n * B → B ≤ L n ^ q →
      LeafOuterProgram.Metadata m B a → (∀ i, (a.stacks i).length ≤ A) →
      (a.stacks 800).length ≤ (n + 1) ^ wordDegree →
      (a.stacks 801).length ≤ (n + 1) ^ wordDegree →
      (afterTime A m B (a.stacks 800).length (a.stacks 801)
        (a.stacks 782) (a.stacks 768) : ℝ) ≤
          runtimeBound 640000000000000000 5 5 A n := by
  filter_upwards [eventually_envelope 3000000000000
    (320000 * (q + 2) ^ 3 + q + 4) (2 * q + 3) wordDegree]
    with n hn A m B a hm hB hmn hBn hmeta ha hq hDl
  obtain ⟨ht, hD, hd, hr⟩ := produced_dimensions_le n m B q hm hB hmn hBn
  have hA := metadata_bound_pos a hmeta ha
  have hDA := metadata_value_bound a hmeta ha 0
  have htA := metadata_value_bound a hmeta ha 1
  have hl := metadata_value_bound a hmeta ha 2
  have hrA := metadata_value_bound a hmeta ha 4
  have hg := metadata_value_bound a hmeta ha 5
  have hv := metadata_value_bound a hmeta ha 6
  change SparseCode.degree m B ≤ A at hDA
  change SparseCode.localRows m B ≤ A at htA
  change SparseCode.localRows m B * SparseCode.degree m B ≤ A at hl
  change SparseCode.dimension m B ≤ A at hrA
  change SparseCode.dimension m B * SparseCode.degree m B ≤ A at hg
  rw [Nat.mul_comm] at hg
  change 2 ^ SparseCode.dimension m B ≤ A at hv
  let H := (320000 * (q + 2) ^ 3 + q + 4) * L n ^ (2 * q + 3)
  let W := max (a.stacks 800).length (a.stacks 801).length
  have hc := afterTime_le_envelope A m B (a.stacks 800).length H W
    (a.stacks 801) (a.stacks 782) (a.stacks 768) hA hrA hDA htA
    (ha 801) (ha 782) (ha 768) hv hg hl ht hD hd hr
    (le_max_left _ _) (le_max_right _ _)
  have h := fifth_cost_runtimeBound _ A (envelope 3000000000000 H W) n
    20000000000000000 hc (hn H W le_rfl (max_le hq hDl))
  norm_num only [Nat.cast_ofNat] at h
  exact h

/-- Metadata preparation and the complete code command have a single
ordinary-polynomial source-space bound. The constants precede every input,
and the numerical occurrence value is never substituted for its word length. -/
theorem complete_space_polynomial :
    ∃ C degree : ℕ, ∀ m B W ml Bl : ℕ,
      0 < m → 0 < B → ml ≤ W → Bl ≤ W →
      let A := W + NativeLeafSetup.parameterTime m B W ml Bl
      ∀ a : LeafOuterProgram.Data, LeafOuterProgram.Metadata m B a →
        (∀ i, (a.stacks i).length ≤ A) →
        max (A + 1) (afterSpace A m B (a.stacks 800).length
          (a.stacks 801) (a.stacks 782) (a.stacks 768)) ≤
            C * (m + W + 16) ^ degree := by
  obtain ⟨C, degree, hparameter⟩ := NativeLeafSetup.parameterTime_polynomial
  refine ⟨20000000000000000 * C ^ 5, degree * 5, ?_⟩
  intro m B W ml Bl hm hB hml hBl A a hmeta ha
  have hp := hparameter m B W ml Bl hm hB hml hBl
  change A + 1 ≤ C * (m + W + 16) ^ degree at hp
  have hA : A ≤ C * (m + W + 16) ^ degree := by omega
  have hs := metadata_afterSpace_le a hmeta ha
  have hpow := Nat.pow_le_pow_left hA 5
  have hleft : A + 1 ≤ 20000000000000000 * (C * (m + W + 16) ^ degree) ^ 5 :=
    hp.trans ((Nat.le_self_pow (by decide) _).trans
      (Nat.le_mul_of_pos_left _ (by decide)))
  have hright := hs.trans (Nat.mul_le_mul_left 20000000000000000 hpow)
  have h := max_le hleft hright
  simpa only [mul_pow, ← pow_mul, Nat.mul_assoc] using h

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeAssemblyBudgets
