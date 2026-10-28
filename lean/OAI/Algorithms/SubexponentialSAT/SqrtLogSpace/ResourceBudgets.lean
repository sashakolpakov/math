import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Asymptotics
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSBoundarySpace
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyTrialGuards

/-! Fixed-degree numerical closure for measured streaming costs. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open SqrtLog.Statement

/-- A fixed polynomial in an old measured cost and the input length preserves
exactly the supplied runtime scale. This assigns no cost to an implementation. -/
theorem fixedPolynomialCost_bound {C A K : ℝ} (hC : 1 ≤ C) (hA : 0 ≤ A)
    (hK : 0 ≤ K) {d : ℕ} (hd : 1 ≤ d) (L n p oldCost newCost : ℕ)
    (hold : (oldCost : ℝ) ≤ runtimeBound C A d L n)
    (hnew : (newCost : ℝ) ≤ K * ((oldCost : ℝ) + L + 1) ^ p) :
    (newCost : ℝ) ≤ runtimeBound (K * (2 * C) ^ p) ((p : ℝ) * A) (d * p) L n := by
  have hbase : (1 : ℝ) ≤ (L : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) L
    linarith
  have hinput : (L : ℝ) + 1 ≤ runtimeBound C A d L n := by
    have hp : (L : ℝ) + 1 ≤ ((L : ℝ) + 1) ^ d := by
      simpa using pow_le_pow_right₀ hbase hd
    have he : 1 ≤ (2 : ℝ) ^ (A * runtimeScale n) :=
      Real.one_le_rpow (by norm_num) (mul_nonneg hA (runtimeScale_nonneg n))
    exact hp.trans ((le_mul_of_one_le_left (by positivity) hC).trans
      (le_mul_of_one_le_right (by positivity) he))
  have hsum : (oldCost : ℝ) + L + 1 ≤ runtimeBound (2 * C) A d L n := by
    rw [runtimeBound_mul_constant]
    linarith
  calc
    (newCost : ℝ) ≤ K * ((oldCost : ℝ) + L + 1) ^ p := hnew
    _ ≤ K * runtimeBound (2 * C) A d L n ^ p :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsum p) hK
    _ = _ := by rw [runtimeBound_pow, runtimeBound_mul_constant]

/-- The literal manuscript exponent follows from the same measured bound. -/
theorem runtimeBound_le_rho {C A : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A)
    (d L : ℕ) {n : ℕ} (hn : 20 ≤ n) :
    runtimeBound C A d L n ≤
      C * ((L : ℝ) + 1) ^ d * (2 : ℝ) ^ ((4 * A) * rho n) := by
  apply mul_le_mul_of_nonneg_left
  · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left (runtimeScale_le_four_rho hn) hA]
  · positivity

/-- Squaring the support count and the assignment factor costs only a fixed
square of their combined nonnegative budget, uniformly in all parameters. -/
theorem streamingFactors_le_square (M K H : ℕ) :
    M ^ 2 * K * H ^ 2 ≤ (M * K * H) ^ 2 := by
  have hK : K ≤ K ^ 2 := by nlinarith
  nlinarith [Nat.mul_le_mul_left (M ^ 2 * H ^ 2) hK]

/-- Generator traversal and complete-tuple visitors are additive. A visitor
rescans one head at a time, so its assignment factor never multiplies the
predecessor-rescan factor of the generator. -/
theorem streamedTupleCost_le (P C r K H visitor : ℕ) (hK : 1 ≤ K)
    (hvisitor : visitor ≤ C * (r + 1) * 2 ^ H) :
    2 * P * r * K * 4 ^ H + K * visitor + 1 ≤
      (2 * P + C + 1) * (r + 1) * K * 4 ^ H := by
  have hpow : 2 ^ H ≤ 4 ^ H := Nat.pow_le_pow_left (by decide) H
  have hv := Nat.mul_le_mul_left K
    (hvisitor.trans (Nat.mul_le_mul_left (C * (r + 1)) hpow))
  have hgen := Nat.mul_le_mul_right (2 * P * K * 4 ^ H) (Nat.le_succ r)
  have hlast : 1 ≤ (r + 1) * K * 4 ^ H := by
    have hp : 1 ≤ 4 ^ H := Nat.one_le_pow _ _ (by decide)
    exact Nat.mul_pos (Nat.mul_pos (by omega) hK) hp
  nlinarith only [hv, hgen, hlast]

/-- The support-pair square and additive signature traversal are a fixed
square of the original combined combinatorial envelope. -/
theorem streamedPairTupleCost_le (P C r K H M visitor : ℕ) (hK : 1 ≤ K)
    (hvisitor : visitor ≤ C * (r + 1) * 2 ^ H) :
    M ^ 2 * (2 * P * r * K * 4 ^ H + K * visitor + 1) ≤
      (2 * P + C + 1) * (r + 1) * (M * K * 2 ^ H) ^ 2 := by
  have ht := Nat.mul_le_mul_left (M ^ 2) (streamedTupleCost_le P C r K H visitor hK hvisitor)
  have hs := Nat.mul_le_mul_left ((2 * P + C + 1) * (r + 1))
    (streamingFactors_le_square M K (2 ^ H))
  have heq : 4 ^ H = (2 ^ H) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rw [heq] at ht ⊢
  calc
    _ ≤ M ^ 2 * ((2 * P + C + 1) * (r + 1) * K * (2 ^ H) ^ 2) := ht
    _ = (2 * P + C + 1) * (r + 1) * (M ^ 2 * K * (2 ^ H) ^ 2) := by ring
    _ ≤ _ := hs

/-- The native dyadic parameter program returns exactly this larger cap,
which bounds leaf occurrences and remains polynomial in the ceiling log. -/
theorem chosen_sparseBound_le_lambda (k : ℕ) :
    ∃ C : ℕ, ∀ n : ℕ, 1 ≤ sparsifySchedule n →
      4 * DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1) ≤
        C * sparsifyLambda n ^ (2 * (k - 1)) := by
  obtain ⟨K, T, hK⟩ := DisjointReuse.SparseBudget.choose_encoding_bounds k
  refine ⟨4 * K ^ (k - 1), ?_⟩
  intro n hs
  have hM := (hK 1 (sparsifySchedule n) (by omega) (by omega)).1
  calc
    _ ≤ 4 * (K * sparsifySchedule n ^ 2) ^ (k - 1) := by gcongr
    _ ≤ 4 * (K * sparsifyLambda n ^ 2) ^ (k - 1) := by
      gcongr
      exact sparsifySchedule_le_lambda n
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

theorem chosen_occurrence_le_lambda (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℕ, ∀ n : ℕ, 1 ≤ sparsifySchedule n →
      DisjointReuse.SparseBudget.occurrenceCap k
        (DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega)) ≤
          C * sparsifyLambda n ^ (2 * (k - 1)) := by
  obtain ⟨C, hC⟩ := chosen_sparseBound_le_lambda k
  refine ⟨C, fun n hs => ?_⟩
  exact (DisjointReuse.SparseBudget.occurrenceCap_le _ _ (by omega)
    (DisjointReuse.SparseBudget.chooseM_spec k 1 (sparsifySchedule n) (by omega)).1).trans
      (hC n hs)

/-- The depth factor in the disjoint tree bound is a fixed-degree input
polynomial for the actual selected threshold. -/
theorem chosen_depth_polynomial (k : ℕ) :
    ∃ C : ℕ, ∀ n : ℕ, 1 ≤ sparsifySchedule n →
      DisjointReuse.SparseCharging.depthConstant k
        (DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega)) * n + 1 ≤
          C * (n + 1) ^ (2 * (k - 2) + 1) := by
  obtain ⟨K, T, hK⟩ := DisjointReuse.SparseBudget.choose_encoding_bounds k
  let A := 4 * (k - 1) * 3 ^ (k - 2)
  refine ⟨A * K ^ (k - 2) + 1, ?_⟩
  intro n hs
  have hM := (hK 1 (sparsifySchedule n) (by omega) (by omega)).1
  have hsle : sparsifySchedule n ≤ n + 1 := (sparsify_parameters_le_input n).2.2.trans
    (Nat.le_succ n)
  have hM' : DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ≤
      K * (n + 1) ^ 2 := hM.trans (Nat.mul_le_mul_left K (Nat.pow_le_pow_left hsle 2))
  have hdepth := DisjointReuse.SparseBudget.depthConstant_le k
    (DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega))
    (DisjointReuse.SparseBudget.chooseM_spec k 1 (sparsifySchedule n) (by omega)).1
  have hpow : 1 ≤ (n + 1) ^ (2 * (k - 2) + 1) := Nat.one_le_pow' _ n
  calc
    _ ≤ (A * (K * (n + 1) ^ 2) ^ (k - 2)) * (n + 1) + 1 := by
      apply Nat.add_le_add_right
      exact Nat.mul_le_mul (hdepth.trans (Nat.mul_le_mul_left A
        (Nat.pow_le_pow_left hM' _))) (Nat.le_succ n)
    _ = A * K ^ (k - 2) * (n + 1) ^ (2 * (k - 2) + 1) + 1 := by
      rw [mul_pow, ← pow_mul, pow_succ]
      ring
    _ ≤ _ := by nlinarith

/-- The chosen occurrence cap satisfies the original incidence algorithm's
integer logarithm hypothesis above a cutoff depending only on the width. -/
theorem chosen_sparseBound_eventually_le_log2_power (k : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      4 * DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1) ≤
          (Nat.log2 (n + 16) + 1) ^ (2 * (k - 1) + 1) := by
  obtain ⟨C, hC⟩ := chosen_sparseBound_le_lambda k
  filter_upwards [sparsifySchedule_tendsto.eventually (Filter.eventually_ge_atTop 1),
    Filter.eventually_ge_atTop (2 ^ C)] with n hs hn
  have hlog : C ≤ Nat.log2 (n + 16) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.le_log_of_pow_le (by norm_num) (hn.trans (Nat.le_add_right n 16))
  calc
    _ ≤ C * sparsifyLambda n ^ (2 * (k - 1)) := hC n hs
    _ ≤ (Nat.log2 (n + 16) + 1) *
        (Nat.log2 (n + 16) + 1) ^ (2 * (k - 1)) :=
      Nat.mul_le_mul (by omega)
        (Nat.pow_le_pow_left (sparsifyLambda_le_log2_shift n) _)
    _ = _ := by rw [pow_succ]; ac_rfl

/-- The existing precision also separates the full ambient assignment count
when the raw formula has no clauses. -/
theorem count_lt_precision_modulus (n m : ℕ) :
    2 ^ n < 3 ^ SqrtLog.LeafParametersProgram.precision n m := by
  exact (Nat.pow_le_pow_left (by decide) n).trans_lt
    (Nat.pow_lt_pow_right (by decide) (by
      unfold SqrtLog.LeafParametersProgram.precision
      omega))

open SqrtLog SqrtLog.Asymptotic SqrtLog.HashSelectProgram
  SqrtLog.LeafStatisticsProgram SqrtLog.LeafParametersProgram in
/-- One width-dependent cutoff validates every original selector trial for
the actual dyadic sparsification bound, including losing scores and marks. -/
theorem chosen_trial_guards_cutoff (k : ℕ) (hk : 2 ≤ k) :
    ∃ cutoff : ℕ, ∀ n ≥ cutoff,
      let B := 4 * DisjointReuse.SparseBudget.chooseM k 1
        (sparsifySchedule n) (by omega) ^ (k - 1)
      ∀ (t d round : ℕ) (clauses : List (List Bool))
        (codes : Fin clauses.length → List ℕ)
        (shifts : SparseCode.SuppliedShifts clauses.length B)
        (localCode : SparseCode.SuppliedLocal clauses.length B)
        (decode : List Bool → List (Fin clauses.length × ZMod 3))
        (score : Records → List Bool → List Bool) (seed : List Bool)
        (rest initial : Records) (bits : List Bool) (mark : Option (Fin clauses.length))
        (nb tb : List Bool),
      (∀ i, (codes i).length ≤ k) →
      initial.map decode = CodeRowsProgram.serializedRows clauses.length shifts localCode →
      (∀ b ∈ seed :: rest, (decode b).length ≤ SparseCode.distanceDenom clauses.length B) →
      bits ∈ seed :: rest → 0 < clauses.length → clauses.length ≤ n * B →
      round ≤ HashSelect.loopCap n clauses.length →
      BinaryArithmetic.toNat nb = n → BinaryArithmetic.toNat tb = Nat.sqrt (L n) + 1 →
      let rows := LeafScopeResourceBounds.trial decode score seed rest initial round bits
      let scopes := HashScopeProgram.Complete.scopes t d codes rows mark
      let mask := LeafScopeResourceBounds.forwardMask scopes
        (HighIncidenceProgram.Prepare.cut scopes nb tb) n
      let x := SqrtLog.CostAssembly.measuredParameterInput scopes mask clauses.length k
      Guard x ∧ passes x = true ∧ dispatch x = .sparse ∧
        x.freeCount ≤ n ∧ n ≤ 2 * x.freeCount ∧
        x.factors ≤ 4 * n + HashSelect.loopCap n clauses.length + 2 ∧
        x.occurrence ≤ L x.freeCount ^ (4 * k + 3) ∧
        x.arity ≤ L x.freeCount ^ (4 * k + 3) := by
  have hq : LeafScopeResourceBounds.resourceExponent (2 * (k - 1) + 1) + 1 =
      4 * k + 3 := by unfold LeafScopeResourceBounds.resourceExponent; omega
  obtain ⟨cutoff, hcutoff⟩ := Filter.eventually_atTop.mp
    ((SqrtLog.CostAssembly.eventually_supplied_trial_guards k (2 * (k - 1) + 1)).and
      (chosen_sparseBound_eventually_le_log2_power k))
  refine ⟨cutoff, ?_⟩
  intro n hn B t d round clauses codes shifts localCode decode score seed rest initial bits mark nb tb
    hcodes hdecode hfamily hbits hm hmb hr hnb htb
  obtain ⟨hguard, hBbound⟩ := hcutoff n hn
  have hB : 0 < B := by
    have hM := (DisjointReuse.SparseBudget.chooseM_spec k 1
      (sparsifySchedule n) (by omega)).1
    dsimp [B]
    positivity
  simpa only [hq] using hguard B t d round clauses codes shifts localCode decode score seed rest
    initial bits mark nb tb hcodes hdecode hfamily hbits hm hB hmb hBbound hr hnb htb

/-- The returned dyadic word has this polynomial length, even though its
numeric value is not charged as a unary representation. -/
theorem chosen_exponent_length_le_input (k : ℕ) :
    ∃ T : ℕ, ∀ n : ℕ, 1 ≤ sparsifySchedule n →
      DisjointReuse.SparseBudget.chooseExponent k 1 (sparsifySchedule n) (by omega) + 1 ≤
        T + 2 * (n + 1) := by
  obtain ⟨K, T, hT⟩ := DisjointReuse.SparseBudget.choose_encoding_bounds k
  refine ⟨T + 1, ?_⟩
  intro n hs
  have he := (hT 1 (sparsifySchedule n) (by omega) (by omega)).2
  have hlog : Nat.log 2 (sparsifySchedule n) ≤ n := by
    rw [← Nat.log2_eq_log_two]
    exact (Nat.log2_le_self _).trans (sparsify_parameters_le_input n).2.2
  omega

/-- Numerical tree size for the actual reciprocal schedule. The result is
an envelope for visits; each native visit still needs its measured cost. -/
theorem chosen_treeBudget_runtimeBound (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n inputBits : ℕ, 20 ≤ n → 1 ≤ sparsifySchedule n → n ≤ inputBits →
      (((DisjointReuse.SparseCharging.depthConstant k
        (DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega)) * n + 1 : ℕ) : ℝ) ^ 2 *
          (2 : ℝ) ^ ((n : ℝ) / sparsifySchedule n)) ≤
        runtimeBound C 256 (4 * (k - 2) + 2) inputBits n := by
  obtain ⟨C, hC⟩ := chosen_depth_polynomial k
  refine ⟨((C : ℝ) + 1) ^ 2, by nlinarith [Nat.cast_nonneg (α := ℝ) C], ?_⟩
  intro n inputBits hn hs hinput
  have hdepth :
      ((DisjointReuse.SparseCharging.depthConstant k
        (DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega)) * n + 1 : ℕ) : ℝ) ≤
          ((C : ℝ) + 1) * ((inputBits : ℝ) + 1) ^ (2 * (k - 2) + 1) := by
    have h := hC n hs
    have h' :
        DisjointReuse.SparseCharging.depthConstant k
          (DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega)) * n + 1 ≤
            (C + 1) * (inputBits + 1) ^ (2 * (k - 2) + 1) :=
      h.trans (Nat.mul_le_mul (Nat.le_succ C)
        (Nat.pow_le_pow_left (Nat.add_le_add_right hinput 1) _))
    exact_mod_cast h'
  unfold runtimeBound
  calc
    _ ≤ (((C : ℝ) + 1) * ((inputBits : ℝ) + 1) ^ (2 * (k - 2) + 1)) ^ 2 *
        (2 : ℝ) ^ (256 * runtimeScale n) := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ (by positivity) hdepth 2
      · exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (inverse_sparsifySchedule_target hn hs)
      · positivity
      · positivity
    _ = _ := by
      rw [mul_pow, ← pow_mul, show (2 * (k - 2) + 1) * 2 = 4 * (k - 2) + 2 by omega]

open SqrtLog SqrtLog.Asymptotic SqrtLog.CostAssembly in
/-- The exact chosen occurrence bound discharges the initial polylogarithm
field of the original worst-case envelope. All remaining fields below are
pointwise numerical obligations for the actual streamed construction. -/
theorem chosen_nativeEnvelope_cutoff (k d power ordinaryPower : ℕ) :
    ∃ cutoff : ℕ, ∀ n ≥ cutoff, ∀ p : Resources,
      p.initialOccurrence = 4 * DisjointReuse.SparseBudget.chooseM k 1
        (sparsifySchedule n) (by omega) ^ (k - 1) →
      p.residual ≤ n ∧ n ≤ 2 * p.residual →
      p.clauses ≤ n * p.initialOccurrence →
      p.localOccurrence ≤ L p.residual ^ (4 * k + 3) →
      p.factors ≤ 4 * n + HashSelect.loopCap n p.clauses + 2 →
      (p.branchVars : ℝ) ≤ (n : ℝ) / Real.sqrt (L n : ℝ) →
      0 < p.labelBase →
      16 * (layoutR p.residual : ℝ) * (L p.residual : ℝ) ^ 2 * (p.labelRows : ℝ) ≤ p.residual →
      Real.log (p.labelBase : ℝ) ≤ 4 * (L p.residual : ℝ) ^ 2 →
      p.heads ≤ n + 1 → (p.headSize : ℝ) ≤ 2 * (n : ℝ) / layoutR p.residual →
      (p.setup : ℝ) ≤ (2 : ℝ) ^ runtimeScale n →
      p.bits * (p.ordinary + 1) ^ 8 ≤ (n + 1) ^ d →
      (nativeEnvelope k n power ordinaryPower p : ℝ) ≤
        (18 : ℝ) ^ power * (2 : ℝ) ^
          ((1 + (power : ℝ) * exponentConstant k (4 * k + 3)) * runtimeScale n) := by
  obtain ⟨cutoff, hcutoff⟩ := Filter.eventually_atTop.mp
    ((eventually_nativeEnvelope_bound k (2 * (k - 1) + 1) (4 * k + 3) d power ordinaryPower).and
      (chosen_sparseBound_eventually_le_log2_power k))
  refine ⟨cutoff, ?_⟩
  intro n hn p hchosen hres hcl hocc hfac hbranch hbase hrows hheight hheads hsize hsetup hordinary
  obtain ⟨hbound, hB⟩ := hcutoff n hn
  apply hbound p
  refine ⟨hres, hcl, ?_, hocc, hfac, hbranch, hbase, hrows, hheight,
    hheads, hsize, hsetup, hordinary⟩
  simpa only [hchosen, L] using hB

/-- Fixed polynomial local budgets compose without allowing the exponent
to depend on the runtime input or the number of streamed iterations. -/
theorem polynomialBudget_substitute (work size inputBits C d K e : ℕ)
    (hwork : work ≤ C * (size + 1) ^ d)
    (hsize : size ≤ K * (inputBits + 1) ^ e) :
    work ≤ C * (K + 1) ^ d * (inputBits + 1) ^ (e * d) := by
  have hbase : 1 ≤ (inputBits + 1) ^ e := Nat.one_le_pow' _ _
  have hs : size + 1 ≤ (K + 1) * (inputBits + 1) ^ e := by nlinarith
  calc
    _ ≤ C * ((K + 1) * (inputBits + 1) ^ e) ^ d :=
      hwork.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hs d))
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

/-- Polynomial source-stack bounds remain polynomial under the actual guarded
compiler's all-tape, all-prefix visited-cell envelope. -/
theorem compiledSpace_polynomial (tapeCount bound inputBits C d : ℕ)
    (hbound : bound ≤ C * (inputBits + 1) ^ d) :
    tapeCount * (bound + inputBits + 15) ≤
      tapeCount * (C + 16) * (inputBits + 1) ^ (d + 1) := by
  have hbase : 1 ≤ inputBits + 1 := by omega
  have hp : (inputBits + 1) ^ d ≤ (inputBits + 1) ^ (d + 1) :=
    Nat.pow_le_pow_right hbase (by omega)
  have hi : inputBits + 1 ≤ (inputBits + 1) ^ (d + 1) := by
    simpa using Nat.pow_le_pow_right hbase (show 1 ≤ d + 1 by omega)
  have hinner : bound + inputBits + 15 ≤ (C + 16) * (inputBits + 1) ^ (d + 1) := by
    nlinarith [Nat.mul_le_mul_left C hp]
  exact (Nat.mul_le_mul_left tapeCount hinner).trans_eq (by ring)

theorem formulaBound_polynomial (n k : ℕ) :
    DisjointReuse.SparseCountProgram.formulaBound n k ≤
      (2 + (4 + 8 * k) * (k + 1) * 2 ^ k) * (n + 1) ^ (k + 1) := by
  have hbase : 1 ≤ n + 1 := by omega
  have hp : n + 1 ≤ (n + 1) ^ (k + 1) := by
    simpa using Nat.pow_le_pow_right hbase (show 1 ≤ k + 1 by omega)
  have hcoef : 4 + (8 * n + 8) * k ≤ (4 + 8 * k) * (n + 1) := by nlinarith
  have hpow : (2 * n + 1) ^ k ≤ 2 ^ k * (n + 1) ^ k := by
    simpa [mul_pow] using Nat.pow_le_pow_left (show 2 * n + 1 ≤ 2 * (n + 1) by omega) k
  unfold DisjointReuse.SparseCountProgram.formulaBound
  calc
    _ ≤ 2 * (n + 1) ^ (k + 1) +
        ((4 + 8 * k) * (n + 1)) * ((k + 1) * (2 ^ k * (n + 1) ^ k)) := by
      apply Nat.add_le_add
      · omega
      · exact Nat.mul_le_mul hcoef (Nat.mul_le_mul_left (k + 1) hpow)
    _ = _ := by rw [pow_succ]; ring

/-- The canonical finite-set input itself has a fixed polynomial size in
ambient n, including unused variables and the empty formula. -/
theorem canonical_input_length_polynomial {n k : ℕ} (F : SAT.CNF (Fin n))
    (hw : SAT.WidthAtMost k F) :
    Encoding.formulaBitLength F + 1 ≤
      (3 + (4 + 8 * k) * (k + 1) * 2 ^ k) * (n + 1) ^ (k + 1) := by
  have h := (DisjointReuse.SparseCountProgram.formulaBitLength_le F k hw).trans
    (formulaBound_polynomial n k)
  have hp : 1 ≤ (n + 1) ^ (k + 1) := Nat.one_le_pow' _ _
  nlinarith only [h, hp]

/-- A physical input-polynomial word cap yields the polynomial-in-n word
premise of the old explicit time envelope above one fixed cutoff. Constants,
degree and cutoff are all chosen before the input formula. -/
theorem inputPolynomial_ambient_power (k C degree : ℕ) :
    ∃ ambientDegree cutoff : ℕ, ∀ n ≥ cutoff, ∀ F : SAT.CNF (Fin n),
      SAT.WidthAtMost k F → C * (Encoding.formulaBitLength F + 1) ^ degree ≤
        (n + 1) ^ ambientDegree := by
  let K := 3 + (4 + 8 * k) * (k + 1) * 2 ^ k
  refine ⟨(k + 1) * degree + 1, C * K ^ degree, ?_⟩
  intro n hn F hw
  have h := canonical_input_length_polynomial F hw
  change Encoding.formulaBitLength F + 1 ≤ K * (n + 1) ^ (k + 1) at h
  calc
    _ ≤ C * (K * (n + 1) ^ (k + 1)) ^ degree :=
      Nat.mul_le_mul_left C (Nat.pow_le_pow_left h degree)
    _ = (C * K ^ degree) * (n + 1) ^ ((k + 1) * degree) := by
      rw [mul_pow, ← pow_mul, Nat.mul_assoc]
    _ ≤ (n + 1) * (n + 1) ^ ((k + 1) * degree) :=
      Nat.mul_le_mul_right _ (by omega)
    _ = _ := by rw [pow_succ']

/-- A common bound on simultaneous physical fields gives a quadratic bound
on the entire DFS boundary, including the framed frontier and accumulator. -/
theorem boundaryStorage_le_square (body depth threshold n P : ℕ)
    (hbody : body ≤ P) (hdepth : depth ≤ P) (hthreshold : threshold ≤ P)
    (hn : n + 1 ≤ P) :
    DisjointReuse.SparseDFSBoundarySpace.storageBound body depth threshold n ≤ 220 * P ^ 2 := by
  have hP : 1 ≤ P := by omega
  have hfront : (2 * body + 2) * (depth + 2) ≤ 12 * P ^ 2 := by
    calc
      _ ≤ (4 * P) * (3 * P) := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have hdata : 100 * (body + n + 1) ≤ 200 * P := by omega
  unfold DisjointReuse.SparseDFSBoundarySpace.storageBound
    DisjointReuse.SparseDFSBoundarySpace.frontierBound
  nlinarith

private theorem dfs_fields_polynomial (k K e : ℕ) :
    ∃ A D : ℕ, ∀ n m inputBits threshold : ℕ,
      n ≤ inputBits → m ≤ inputBits → threshold ≤ K * (inputBits + 1) ^ e →
      let P := A * (inputBits + 1) ^ D
      DisjointReuse.SparseCountProgram.formulaBound n k ≤ P ∧ m * k ≤ P ∧
        threshold ≤ P ∧ n + 1 ≤ P := by
  let c := 2 + (4 + 8 * k) * (k + 1) * 2 ^ k
  let A := c + k + K + 1
  let D := k + e + 2
  refine ⟨A, D, ?_⟩
  intro n m inputBits threshold hn hm ht
  let P := A * (inputBits + 1) ^ D
  have hbase : 1 ≤ inputBits + 1 := by omega
  have hinput : inputBits + 1 ≤ (inputBits + 1) ^ D := by
    simpa only [pow_one] using Nat.pow_le_pow_right hbase (show 1 ≤ D by dsimp [D]; omega)
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hnP : n + 1 ≤ P := by
    exact (Nat.add_le_add_right hn 1).trans
      (hinput.trans (Nat.le_mul_of_pos_left _ hA))
  have hbody : DisjointReuse.SparseCountProgram.formulaBound n k ≤ P := by
    apply (formulaBound_polynomial n k).trans
    apply Nat.mul_le_mul (show c ≤ A by dsimp [A]; omega)
    exact (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) _).trans
      (Nat.pow_le_pow_right hbase (show k + 1 ≤ D by dsimp [D]; omega))
  have hdepth : m * k ≤ P := by
    rw [Nat.mul_comm m k]
    exact Nat.mul_le_mul (show k ≤ A by dsimp [A]; omega)
      (hm.trans ((Nat.le_succ inputBits).trans hinput))
  have hthreshold : threshold ≤ P := ht.trans
    (Nat.mul_le_mul (show K ≤ A by dsimp [A]; omega)
      (Nat.pow_le_pow_right hbase (show e ≤ D by dsimp [D]; omega)))
  exact ⟨hbody, hdepth, hthreshold, hnP⟩

/-- The concrete framed DFS boundary is polynomial in the original input
length: its depth is the original clause count times the fixed width, not
the number of visited nodes. The threshold field includes retained setup. -/
theorem dfsBoundary_polynomial (k K e : ℕ) :
    ∃ C d : ℕ, ∀ n m inputBits threshold : ℕ,
      n ≤ inputBits → m ≤ inputBits → threshold ≤ K * (inputBits + 1) ^ e →
      DisjointReuse.SparseDFSBoundarySpace.storageBound
        (DisjointReuse.SparseCountProgram.formulaBound n k) (m * k) threshold n ≤
          C * (inputBits + 1) ^ d := by
  obtain ⟨A, D, h⟩ := dfs_fields_polynomial k K e
  refine ⟨220 * A ^ 2, D * 2, ?_⟩
  intro n m inputBits threshold hn hm ht
  obtain ⟨hb, hd, ht, hn⟩ := h n m inputBits threshold hn hm ht
  calc
    _ ≤ 220 * (A * (inputBits + 1) ^ D) ^ 2 :=
      boundaryStorage_le_square _ _ _ _ _ hb hd ht hn
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

/-- The exact four summands of `DFSCountProgram.visitSpace`. The selector
coefficient is fixed by the clause width; no exponential visit count appears. -/
theorem dfsVisitSpace_le_fourth (coefficient n body depth threshold S : ℕ)
    (hn : n + 1 ≤ S) (hb : body ≤ S) (hd : depth ≤ S) (ht : threshold ≤ S) :
    let Q := DisjointReuse.SparseDFSBoundarySpace.frontierBound body depth
    (n + 1 + Q + 11 * body + 13) + (coefficient + 24) * (body + threshold + 1) ^ 4 +
      (Q + (n + 1) + 620001 * (4 * body + 3) ^ 2) + 100 * (n + 1) ≤
        32000000 * (coefficient + 1) * S ^ 4 := by
  have hS : 1 ≤ S := by omega
  have h1 : S ≤ S ^ 4 := Nat.le_self_pow (by decide) _
  have h2 : S ^ 2 ≤ S ^ 4 := Nat.pow_le_pow_right hS (by decide)
  have hQ : DisjointReuse.SparseDFSBoundarySpace.frontierBound body depth ≤ 13 * S ^ 2 := by
    have hprod : (2 * body + 2) * (depth + 2) ≤ 12 * S ^ 2 := by
      calc
        _ ≤ (4 * S) * (3 * S) := Nat.mul_le_mul (by omega) (by omega)
        _ = _ := by ring
    unfold DisjointReuse.SparseDFSBoundarySpace.frontierBound
    nlinarith
  have hselect : (coefficient + 24) * (body + threshold + 1) ^ 4 ≤
      81 * (coefficient + 24) * S ^ 4 := by
    calc
      _ ≤ (coefficient + 24) * (3 * S) ^ 4 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
      _ = _ := by ring
  have hsplit : 620001 * (4 * body + 3) ^ 2 ≤ 30380049 * S ^ 2 := by
    calc
      _ ≤ 620001 * (7 * S) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      _ = _ := by ring
  dsimp only
  nlinarith

theorem dfsVisitSpace_polynomial (k coefficient K e : ℕ) :
    ∃ C d : ℕ, ∀ n m inputBits threshold : ℕ,
      n ≤ inputBits → m ≤ inputBits → threshold ≤ K * (inputBits + 1) ^ e →
      let P := DisjointReuse.SparseCountProgram.formulaBound n k
      let Q := DisjointReuse.SparseDFSBoundarySpace.frontierBound P (m * k)
      (n + 1 + Q + 11 * P + 13) + (coefficient + 24) * (P + threshold + 1) ^ 4 +
        (Q + (n + 1) + 620001 * (4 * P + 3) ^ 2) + 100 * (n + 1) ≤
          C * (inputBits + 1) ^ d := by
  obtain ⟨A, D, h⟩ := dfs_fields_polynomial k K e
  refine ⟨32000000 * (coefficient + 1) * A ^ 4, D * 4, ?_⟩
  intro n m inputBits threshold hn hm ht
  obtain ⟨hb, hd, ht, hn⟩ := h n m inputBits threshold hn hm ht
  calc
    _ ≤ 32000000 * (coefficient + 1) * (A * (inputBits + 1) ^ D) ^ 4 :=
      dfsVisitSpace_le_fourth _ _ _ _ _ _ hn hb hd ht
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

/-- The actual DFS visit budget is polynomial in its retained fields times
the leaf budget, including splitter maxima and all cleanup passes. -/
theorem dfsVisitTime_le (coefficient n body threshold leafTime bound S : ℕ)
    (hn : n + 1 ≤ S) (hb : body ≤ S) (ht : threshold ≤ S) (hbound : bound ≤ S) :
    9 * body + 11 +
      (coefficient * (body + threshold + 1) ^ 4 + 1 +
        (max (621000 * (4 * body + 3) ^ 2) (leafTime + 100 * (n + 1)) + 1 +
          ((2 * bound + 3) * 257 + 1))) ≤
      32000000 * (coefficient + 1) * S ^ 4 * (leafTime + 1) := by
  have hS : 1 ≤ S := by omega
  have h1 : S ≤ S ^ 4 := Nat.le_self_pow (by decide) _
  have h2 : S ^ 2 ≤ S ^ 4 := Nat.pow_le_pow_right hS (by decide)
  have hselect : coefficient * (body + threshold + 1) ^ 4 ≤ 81 * coefficient * S ^ 4 := by
    calc
      _ ≤ coefficient * (3 * S) ^ 4 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
      _ = _ := by ring
  have hsplit : 621000 * (4 * body + 3) ^ 2 ≤ 30429000 * S ^ 2 := by
    calc
      _ ≤ 621000 * (7 * S) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      _ = _ := by ring
  have hmax : max (621000 * (4 * body + 3) ^ 2) (leafTime + 100 * (n + 1)) ≤
      30429000 * S ^ 2 + leafTime + 100 * S := max_le (by omega) (by omega)
  have hbig : 1 ≤ 32000000 * (coefficient + 1) * S ^ 4 := by
    have hp : 1 ≤ S ^ 4 := one_le_pow₀ hS
    nlinarith
  have hpay : leafTime ≤ 32000000 * (coefficient + 1) * S ^ 4 * leafTime :=
    Nat.le_mul_of_pos_left _ hbig
  calc
    _ ≤ leafTime + (81 * coefficient + 31000000) * S ^ 4 := by nlinarith
    _ ≤ _ := by nlinarith


/-- Startup, all visits and full count-word export fit the product of the
visit count, the leaf budget and one fixed retained-field polynomial. -/
theorem dfsCommandTime_le (coefficient n body threshold leafTime bound visits S : ℕ)
    (hn : n + 1 ≤ S) (hb : body ≤ S) (ht : threshold ≤ S) (hbound : bound ≤ S) :
    let visitTime := 9 * body + 11 +
      (coefficient * (body + threshold + 1) ^ 4 + 1 +
        (max (621000 * (4 * body + 3) ^ 2) (leafTime + 100 * (n + 1)) + 1 +
          ((2 * bound + 3) * 257 + 1)))
    8 * body + 16 + (visits * (visitTime + 1) + 1) + (2 * bound + 7 * n + 18) ≤
      32000100 * (coefficient + 1) * S ^ 4 * (visits + 1) * (leafTime + 1) := by
  have hS : 1 ≤ S := by omega
  have hp : S ≤ S ^ 4 := Nat.le_self_pow (by decide) _
  have hpow : 1 ≤ S ^ 4 := one_le_pow₀ hS
  have hv := dfsVisitTime_le coefficient n body threshold leafTime bound S hn hb ht hbound
  have hcap : S ≤ (coefficient + 1) * S ^ 4 * (leafTime + 1) :=
    hp.trans ((Nat.le_mul_of_pos_left _ (by omega)).trans
      (Nat.le_mul_of_pos_right _ (by omega)))
  have hcap0 : 1 ≤ (coefficient + 1) * S ^ 4 * (leafTime + 1) := hS.trans hcap
  have hvisit : 9 * body + 11 +
      (coefficient * (body + threshold + 1) ^ 4 + 1 +
        (max (621000 * (4 * body + 3) ^ 2) (leafTime + 100 * (n + 1)) + 1 +
          ((2 * bound + 3) * 257 + 1))) + 1 ≤
      32000001 * (coefficient + 1) * S ^ 4 * (leafTime + 1) := by nlinarith
  have hstartup : 8 * body + 16 + 1 + (2 * bound + 7 * n + 18) ≤
      100 * (coefficient + 1) * S ^ 4 * (leafTime + 1) := by
    have hstart : 8 * body + 16 + 1 + (2 * bound + 7 * n + 18) ≤ 100 * S := by omega
    exact hstart.trans ((Nat.mul_le_mul_left 100 hcap).trans_eq (by ring))
  dsimp only
  have hpaid := Nat.mul_le_mul_left visits hvisit
  nlinarith


/-- The actual disjoint occurrence choice is bounded in original input
length, with coefficients and degree fixed by the width. -/
theorem chosen_sparseBound_le_input (k : ℕ) :
    ∃ K : ℕ, ∀ n inputLength : ℕ, n ≤ inputLength → 1 ≤ sparsifySchedule n →
      4 * DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1) ≤
        K * (inputLength + 1) ^ (2 * (k - 1)) := by
  obtain ⟨K, hK⟩ := chosen_sparseBound_le_lambda k
  refine ⟨K, ?_⟩
  intro n inputLength hn hs
  apply (hK n hs).trans
  apply Nat.mul_le_mul_left K
  apply Nat.pow_le_pow_left
  exact (sparsify_parameters_le_input n).1.trans (by omega)

/-- The complete ordinary size used by native leaf preparation is a fixed
input polynomial for the actual occurrence choice and sparse leaf count.
Physical input words remain independently bounded by their proved producer. -/
theorem chosen_leaf_input_cap (k wordCoefficient wordDegree : ℕ) :
    ∃ C degree : ℕ, ∀ n inputLength m W : ℕ,
      n ≤ inputLength → 1 ≤ sparsifySchedule n →
      let B := 4 * DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
      m ≤ n * B → W ≤ wordCoefficient * (inputLength + 1) ^ wordDegree →
      n + m + B + W + 16 ≤ C * (inputLength + 1) ^ degree := by
  obtain ⟨K, hK⟩ := chosen_sparseBound_le_input k
  refine ⟨2 * K + wordCoefficient + 17, 2 * (k - 1) + wordDegree + 1, ?_⟩
  intro n inputLength m W hn hs B hm hW
  let X := inputLength + 1
  let degree := 2 * (k - 1) + wordDegree + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hB : B ≤ K * X ^ (2 * (k - 1)) := hK n inputLength hn hs
  have hm' : m ≤ K * X ^ (2 * (k - 1) + 1) := by
    calc
      _ ≤ n * B := hm
      _ ≤ X * (K * X ^ (2 * (k - 1))) :=
        Nat.mul_le_mul (by dsimp [X]; omega) hB
      _ = _ := by rw [pow_succ']; ring
  have hB' : B ≤ K * X ^ degree := hB.trans
    (Nat.mul_le_mul_left K (Nat.pow_le_pow_right hX (by dsimp [degree]; omega)))
  have hm'' : m ≤ K * X ^ degree := hm'.trans
    (Nat.mul_le_mul_left K (Nat.pow_le_pow_right hX (by dsimp [degree]; omega)))
  have hW' : W ≤ wordCoefficient * X ^ degree := hW.trans
    (Nat.mul_le_mul_left wordCoefficient (Nat.pow_le_pow_right hX (by dsimp [degree]; omega)))
  have hlin : X ≤ X ^ degree := by
    simpa using Nat.pow_le_pow_right hX (show 1 ≤ degree by dsimp [degree]; omega)
  have h1 : 1 ≤ X ^ degree := Nat.one_le_pow _ _ hX
  change _ ≤ (2 * K + wordCoefficient + 17) * X ^ degree
  have hn' : n ≤ X := by dsimp [X]; omega
  nlinarith only [hB', hm'', hW', hlin, h1, hn']

/-- A physical input cap enters a measured time bound with a fixed degree,
independently of the size of the old exponential work counter. -/
theorem polynomialCost_input_substitute (oldCost newCost size inputBits C p K e : ℕ)
    (hwork : newCost ≤ C * (oldCost + size + 1) ^ p)
    (hsize : size ≤ K * (inputBits + 1) ^ e) :
    newCost ≤ C * (K + 1) ^ p * (oldCost + inputBits + 1) ^ ((e + 1) * p) := by
  let X := oldCost + inputBits + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hinput : inputBits + 1 ≤ X := by dsimp [X]; omega
  have hsize' : size ≤ K * X ^ (e + 1) := hsize.trans
    (Nat.mul_le_mul_left K ((Nat.pow_le_pow_left hinput e).trans
      (Nat.pow_le_pow_right hX (by omega))))
  have hlinear : oldCost + 1 ≤ X ^ (e + 1) :=
    (show oldCost + 1 ≤ X by dsimp [X]; omega).trans (Nat.le_self_pow (by omega) X)
  have hsum : oldCost + size + 1 ≤ (K + 1) * X ^ (e + 1) := by
    nlinarith only [hsize', hlinear]
  have h := hwork.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hsum p))
  simpa only [mul_pow, ← pow_mul, Nat.mul_assoc] using h

/-- Physical local storage may be substituted before a fixed-power time
comparison; the original runtime scale is unchanged. -/
theorem fixedPolynomialCost_with_input {C A : ℝ} (hC : 1 ≤ C) (hA : 0 ≤ A)
    {d : ℕ} (hd : 1 ≤ d) (inputBits n oldCost newCost size coefficient p K e : ℕ)
    (hold : (oldCost : ℝ) ≤ runtimeBound C A d inputBits n)
    (hnew : newCost ≤ coefficient * (oldCost + size + 1) ^ p)
    (hsize : size ≤ K * (inputBits + 1) ^ e) :
    (newCost : ℝ) ≤ runtimeBound
      (((coefficient * (K + 1) ^ p : ℕ) : ℝ) * (2 * C) ^ ((e + 1) * p))
      (((e + 1) * p : ℕ) * A) (d * ((e + 1) * p)) inputBits n := by
  apply fixedPolynomialCost_bound hC hA (Nat.cast_nonneg _) hd
    inputBits n ((e + 1) * p) oldCost newCost hold
  exact_mod_cast polynomialCost_input_substitute oldCost newCost size inputBits
    coefficient p K e hnew hsize

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
