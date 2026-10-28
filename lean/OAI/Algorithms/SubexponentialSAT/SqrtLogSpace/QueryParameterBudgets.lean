import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ResourceBudgets
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryModelBudgets
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryScopeBudgets
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResourcesOrigin
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResourcesScalars
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyParameterValues

/-! Uniform input-polynomial numeric caps for every actually produced query.
These bounds quantify over every physical padding, while physical word-length
bounds are supplied separately by the concrete producers. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open Filter SqrtLog SqrtLog.Asymptotic SqrtLog.ProducedQueryResources
  SqrtLog.LeafQueryFrontend SqrtLog.LeafScopeResourceBounds in
/-- Actual raw scope resources imply the sharp scan bounds for every marked
or unmarked query, without an identity with the old selector history. -/
theorem eventually_scan_bounds_of_scope_resources (k qi : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (q : Query) (B : ℕ), q.Valid → ambient q = n →
      0 < q.clauses.length → q.clauses.length ≤ n * B → B ≤ L n ^ qi →
      q.scopeRows.length ≤ 3 * n + HashSelect.loopCap n q.clauses.length + 2 →
      HighIncidenceProgram.Prepare.mass q.scopeRows ≤
        (3 * n * SparseCode.degreeBound q.clauses.length B +
          (HashSelect.loopCap n q.clauses.length + 1) *
            SparseCode.distanceDenom q.clauses.length B + 1) * k →
      (∀ row ∈ q.scopeRows, row.length ≤
        (SparseCode.degreeBound q.clauses.length B + SparseCode.distanceDenom q.clauses.length B + 1) * k) →
      ScanBounds q k (resourceExponent qi + 1) := by
  filter_upwards [eventually_raw_scope_guards k qi] with n hg q B hv hn hm hmb hB hlen hmass har
  have hforward : q.forward = CostAssembly.forwardHighMask q.scopeRows n (Nat.sqrt (L n) + 1) := by
    dsimp [ambient] at hn
    simp only [Query.forward, highMask, CostAssembly.forwardHighMask,
      EarlyThreshold.threshold, HighIncidenceProgram.Prepare.mass, hn]
  have hinput := q.input_eq_measured k hv.2.2.2.2.2.1
  rw [hforward] at hinput
  obtain ⟨hguard,hfree,hhalf,hfactors,hocc,harity⟩ :=
    hg q.scopeRows q.clauses.length B hm hmb hB hlen hmass har
      (scopes_nodup 1 0 q.codes q.rows q.mark)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hinput] using hguard
  · simpa only [hinput, hn] using And.intro hfree hhalf
  · simpa only [hinput, hn] using hfactors
  · simpa only [hinput] using hocc
  · simpa only [hinput] using harity
  · exact CostAssembly.highBranchCount_le_sqrt q.scopeRows (ambient q) hv.2.1

open Filter SqrtLog SqrtLog.Asymptotic SqrtLog.ProducedQueryResources
  SqrtLog.LeafQueryFrontend SqrtLog.LeafScopeResourceBounds in
/-- The same raw structural bounds also supply the small scalar inputs;
all cutoffs are fixed before the query, mark, and candidate history. -/
theorem eventually_small_inputs_of_scope_resources (k qi : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (q : Query) (B : ℕ), q.Valid → ambient q = n →
      0 < q.clauses.length → q.clauses.length ≤ n * B → B ≤ L n ^ qi →
      q.scopeRows.length ≤ 3 * n + HashSelect.loopCap n q.clauses.length + 2 →
      HighIncidenceProgram.Prepare.mass q.scopeRows ≤
        (3 * n * SparseCode.degreeBound q.clauses.length B +
          (HashSelect.loopCap n q.clauses.length + 1) *
            SparseCode.distanceDenom q.clauses.length B + 1) * k →
      (∀ row ∈ q.scopeRows, row.length ≤
        (SparseCode.degreeBound q.clauses.length B + SparseCode.distanceDenom q.clauses.length B + 1) * k) →
      ScanBounds q k (resourceExponent qi + 1) ∧ SmallInputs q k n := by
  let ql := resourceExponent qi + 1
  filter_upwards [eventually_scan_bounds_of_scope_resources k qi,
    CostAssembly.eventually_sparse_parameter_bounds qi,
    eventually_L_power_le_n qi (by norm_num : (0 : ℝ) < 1),
    eventually_uniform_half (eventually_L_power_le_n ql (by norm_num : (0 : ℝ) < 1)),
    Filter.eventually_ge_atTop (max 16 k)] with n hscan hpar hLn hLm hn q B hv hqn hm hmb hB hlen hmass har
  have hs := hscan q B hv hqn hm hmb hB hlen hmass har
  have hhalf : n ≤ 2 * (q.input k).freeCount := by simpa only [hqn] using hs.residual.2
  have hlm : L (q.input k).freeCount ^ ql ≤ (q.input k).freeCount := by
    exact_mod_cast (by simpa using hLm (q.input k).freeCount hhalf :
      (L (q.input k).freeCount : ℝ) ^ ql ≤ (q.input k).freeCount)
  have hln : L n ^ qi ≤ n := by exact_mod_cast (by simpa using hLn : (L n : ℝ) ^ qi ≤ n)
  exact ⟨hs, small_inputs k n qi ql q B hv hqn (by omega) (by omega) hs hmb hB hln hlm
    (hpar q.clauses.length B hmb hB).1⟩

open SqrtLog SqrtLog.Asymptotic SqrtLog.ProducedQueryResources in
/-- The actual reciprocal sparsification choice satisfies the existing query
scalar estimates above one fixed cutoff. The three literal raw-scope bounds cover every attained history and trial;
no old selector provenance is required. -/
theorem chosen_query_scalars_cutoff_of_scope_resources (k : ℕ) (hk : 2 ≤ k) :
    ∃ cutoff : ℕ, ∀ n ≥ cutoff,
      20 ≤ n ∧ 2 ≤ sparsifySchedule n ∧
      let B := 4 * DisjointReuse.SparseBudget.chooseM k 1
        (sparsifySchedule n) (by omega) ^ (k - 1)
      ∀ q : LeafQueryFrontend.Query, q.Valid → ambient q = n →
        0 < q.clauses.length → q.clauses.length ≤ n * B →
        q.scopeRows.length ≤ 3 * n + HashSelect.loopCap n q.clauses.length + 2 →
        HighIncidenceProgram.Prepare.mass q.scopeRows ≤
          (3 * n * SparseCode.degreeBound q.clauses.length B +
            (HashSelect.loopCap n q.clauses.length + 1) *
              SparseCode.distanceDenom q.clauses.length B + 1) * k →
        (∀ row ∈ q.scopeRows, row.length ≤
          (SparseCode.degreeBound q.clauses.length B + SparseCode.distanceDenom q.clauses.length B + 1) * k) →
        ScanBounds q k (4 * k + 3) ∧ SmallInputs q k n := by
  have hq : LeafScopeResourceBounds.resourceExponent (2 * (k - 1) + 1) + 1 =
      4 * k + 3 := by unfold LeafScopeResourceBounds.resourceExponent; omega
  obtain ⟨cutoff, hcutoff⟩ := Filter.eventually_atTop.mp
    ((((eventually_small_inputs_of_scope_resources k (2 * (k - 1) + 1)).and
      (chosen_sparseBound_eventually_le_log2_power k)).and
      (sparsifySchedule_tendsto.eventually (Filter.eventually_ge_atTop 2))).and
      (Filter.eventually_ge_atTop 20))
  refine ⟨cutoff, ?_⟩
  intro n hn
  obtain ⟨⟨⟨hsmall, hBbound⟩, hs⟩, hlarge⟩ := hcutoff n hn
  refine ⟨hlarge, hs, ?_⟩
  intro B q hvalid hambient hnonempty hclauses hlen hmass harity
  simpa only [hq] using hsmall q B hvalid hambient hnonempty hclauses hBbound hlen hmass harity


open SqrtLog SqrtLog.Asymptotic SqrtLog.ProducedQueryResources in
/-- One fixed polynomial bounds every serialized numeric bank value of every
large query with the actual disjoint occurrence choice. Padding lengths remain
arbitrary; this is a bound on values, not on the padded words. -/
theorem chosen_serialized_values_cutoff_of_scope_resources (k : ℕ) (hk : 2 ≤ k) :
    ∃ C degree cutoff : ℕ, ∀ n ≥ cutoff,
      let B := 4 * DisjointReuse.SparseBudget.chooseM k 1
        (sparsifySchedule n) (by omega) ^ (k - 1)
      ∀ q : LeafQueryFrontend.Query, q.Valid → ambient q = n →
        0 < q.clauses.length → q.clauses.length ≤ n * B →
        q.scopeRows.length ≤ 3 * n + HashSelect.loopCap n q.clauses.length + 2 →
        HighIncidenceProgram.Prepare.mass q.scopeRows ≤
          (3 * n * SparseCode.degreeBound q.clauses.length B +
            (HashSelect.loopCap n q.clauses.length + 1) *
              SparseCode.distanceDenom q.clauses.length B + 1) * k →
        (∀ row ∈ q.scopeRows, row.length ≤
          (SparseCode.degreeBound q.clauses.length B + SparseCode.distanceDenom q.clauses.length B + 1) * k) →
        ∀ (padding : Fin 8 → ℕ) (j : Fin 64),
          (LeafParametersProgram.Circuit.result LeafParametersProgram.Serialization.code
            (LeafParametersProgram.Execute.guardedModel (q.input k) padding)).val j ≤
              C * (n + 1) ^ degree := by
  obtain ⟨C, degree, hvalues⟩ :=
    CostAssembly.ParameterValues.serialized_values_of_fourth_power
  obtain ⟨cutoff, hcutoff⟩ := chosen_query_scalars_cutoff_of_scope_resources k hk
  refine ⟨C, degree, cutoff, ?_⟩
  intro n hn B q hvalid hambient hnonempty hclauses hlen hmass harity padding j
  have hsmall := ((hcutoff n hn).2.2 q hvalid hambient hnonempty hclauses hlen hmass harity).2
  exact hvalues (q.input k) padding n hsmall.magnitude j

open SqrtLog SqrtLog.Asymptotic SqrtLog.ProducedQueryResources in
/-- Numeric source dimensions and all produced bank entries share a fixed
polynomial in the original input length. The actual native scan identifies
incidences, so the full raw row count is included without using rank. -/
theorem chosen_scalar_input_cap_of_scope_resources (k : ℕ) (hk : 2 ≤ k) :
    ∃ C degree cutoff : ℕ, ∀ n inputLength : ℕ, cutoff ≤ n → n ≤ inputLength →
      let B := 4 * DisjointReuse.SparseBudget.chooseM k 1
        (sparsifySchedule n) (by omega) ^ (k - 1)
      ∀ q : LeafQueryFrontend.Query, q.Valid → ambient q = n →
        0 < q.clauses.length → q.clauses.length ≤ n * B →
        q.scopeRows.length ≤ 3 * n + HashSelect.loopCap n q.clauses.length + 2 →
        HighIncidenceProgram.Prepare.mass q.scopeRows ≤
          (3 * n * SparseCode.degreeBound q.clauses.length B +
            (HashSelect.loopCap n q.clauses.length + 1) *
              SparseCode.distanceDenom q.clauses.length B + 1) * k →
        (∀ row ∈ q.scopeRows, row.length ≤
          (SparseCode.degreeBound q.clauses.length B + SparseCode.distanceDenom q.clauses.length B + 1) * k) →
        let S := C * (inputLength + 1) ^ degree
        1 ≤ S ∧ n ^ 2 ≤ S ∧ (q.input k).incidences ≤ S ∧
        ∀ (padding : Fin 8 → ℕ) (j : Fin 64),
          (LeafParametersProgram.Circuit.result LeafParametersProgram.Serialization.code
            (LeafParametersProgram.Execute.guardedModel (q.input k) padding)).val j ≤ S := by
  obtain ⟨C, degree, cutoff₁, hvalues⟩ := chosen_serialized_values_cutoff_of_scope_resources k hk
  obtain ⟨cutoff₂, hsmall⟩ := chosen_query_scalars_cutoff_of_scope_resources k hk
  refine ⟨C + 1, degree + 2, max cutoff₁ cutoff₂, ?_⟩
  intro n inputLength hn hinput B q hvalid hambient hnonempty hclauses hlen hmass harity S
  have hbase : 1 ≤ inputLength + 1 := by omega
  have hpow : 1 ≤ (inputLength + 1) ^ (degree + 2) := Nat.one_le_pow _ _ hbase
  have hS : 1 ≤ S := hpow.trans (Nat.le_mul_of_pos_left _ (by omega))
  have hnS : n ^ 2 ≤ S := by
    calc
      _ ≤ (inputLength + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ (inputLength + 1) ^ (degree + 2) := Nat.pow_le_pow_right hbase (by omega)
      _ ≤ _ := Nat.le_mul_of_pos_left _ (by omega)
  have hs := ((hsmall n (by omega)).2.2 q hvalid hambient hnonempty hclauses hlen hmass harity).2
  refine ⟨hS, hnS, hs.incidences.trans hnS, ?_⟩
  intro padding j
  apply (hvalues n (by omega) q hvalid hambient hnonempty hclauses hlen hmass harity padding j).trans
  apply Nat.mul_le_mul (by omega)
  exact (Nat.pow_le_pow_left (by omega) degree).trans
    (Nat.pow_le_pow_right hbase (by omega))

open SqrtLog SqrtLog.Asymptotic SqrtLog.ProducedQueryResources in
/-- A coarse polynomial bounds every serialized numeric value from literal
history and trial sizes, without guard success or a large-input cutoff. -/
theorem raw_query_serialized_values_polynomial :
    ∃ C degree : ℕ, ∀ (q : LeafQueryFrontend.Query) (n k D P rounds S : ℕ),
      q.Valid → ambient q = n → 1 ≤ S → n ≤ S → q.clauses.length ≤ S →
      k ≤ S → D ≤ S → P ≤ S → rounds ≤ S →
      q.scopeRows.length ≤ 3 * n + rounds + 2 →
      HighIncidenceProgram.Prepare.mass q.scopeRows ≤
        (3 * n * D + (rounds + 1) * P + 1) * k →
      (∀ row ∈ q.scopeRows, row.length ≤ (D + P + 1) * k) →
      ∀ (padding : Fin 8 → ℕ) (j : Fin 64),
        (LeafParametersProgram.Circuit.result LeafParametersProgram.Serialization.code
          (LeafParametersProgram.Execute.guardedModel (q.input k) padding)).val j ≤
            C * (S + 1) ^ degree := by
  obtain ⟨C, degree, hvalues⟩ := CostAssembly.ParameterValues.serialized_values_polynomial
  refine ⟨C * 10401 ^ degree, 6 * degree, ?_⟩
  intro q n k D P rounds S hv hamb hS hn hm hk hD hP hr hcount hmass harity padding j
  have hforward : q.forward = CostAssembly.forwardHighMask q.scopeRows n (Nat.sqrt (L n) + 1) := by
    dsimp [ambient] at hamb
    simp only [LeafQueryFrontend.Query.forward, LeafQueryFrontend.highMask,
      CostAssembly.forwardHighMask, EarlyThreshold.threshold, HighIncidenceProgram.Prepare.mass, hamb]
  have hinput := q.input_eq_measured k hv.2.2.2.2.2.1
  rw [hforward] at hinput
  have hnpos : 0 < n := by simpa only [ambient, hamb] using hv.2.1
  have hmag : LeafParametersProgram.magnitude (q.input k) ≤ 10400 * S ^ 6 := by
    rw [hinput]
    exact raw_resources_magnitude_polynomial q.scopeRows n q.clauses.length k D P rounds S
      hnpos hS hn hm hk hD hP hr hcount hmass harity
  have hp : 1 ≤ (S + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hbase : 10400 * S ^ 6 + 1 ≤ 10401 * (S + 1) ^ 6 := by
    have hpow := Nat.pow_le_pow_left (show S ≤ S + 1 by omega) 6
    omega
  calc
    _ ≤ C * (10400 * S ^ 6 + 1) ^ degree := hvalues (q.input k) padding _ hmag j
    _ ≤ C * (10401 * (S + 1) ^ 6) ^ degree :=
      Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase degree)
    _ = _ := by rw [mul_pow, ← pow_mul, Nat.mul_assoc]

/-- Simultaneous dense source rows, full multiplication and inverse caches,
raw specialized records and the complete n-entry factor table are polynomial
in the actual scalar cap. The truncation parameter is the actual precision t. -/
theorem scalar_storage_polynomial (n Q t d J R S : ℕ)
    (hS : 1 ≤ S) (hn : n ≤ S) (hQ : Q ≤ S) (ht : t ≤ S)
    (hd : d ≤ S) (hJ : J ≤ S) (hR : R ≤ S) :
    2 * d ^ 3 * t + 4 * Q * d * t + 2 * Q ^ 2 * d * t + 6 * t ^ 2 +
      (n * (2 * ((R + 1) * (d * (2 * t))) + 2) + 1) +
      ((1 + n * (J - 1)) * (2 * (t + J + n) + 2 * d * (2 * t) + 2)) +
      n * (2 * n + 2 * (t * J * (2 * (t + J + n) + 2 * d * (2 * t) + 2)) + 4) ≤
        100 * S ^ 5 := by
  have hS2 : S ≤ S ^ 2 := Nat.le_self_pow (by decide) S
  have h25 : S ^ 2 ≤ S ^ 5 := Nat.pow_le_pow_right hS (by decide)
  have h35 : S ^ 3 ≤ S ^ 5 := Nat.pow_le_pow_right hS (by decide)
  have h45 : S ^ 4 ≤ S ^ 5 := Nat.pow_le_pow_right hS (by decide)
  have h14 : 1 ≤ S ^ 4 := Nat.one_le_pow _ _ hS
  have h24 : S ^ 2 ≤ S ^ 4 := Nat.pow_le_pow_right hS (by decide)
  have hdt : d * t ≤ S ^ 2 := by simpa [pow_two] using Nat.mul_le_mul hd ht
  have hpiece : 2 * (t + J + n) + 2 * d * (2 * t) + 2 ≤ 12 * S ^ 2 := by
    nlinarith only [ht, hJ, hn, hdt, hS, hS2]
  have htable : 2 * d ^ 3 * t ≤ 2 * S ^ 4 := by
    have h := Nat.mul_le_mul (Nat.pow_le_pow_left hd 3) ht
    nlinarith only [h]
  have hinverse : 4 * Q * d * t ≤ 4 * S ^ 3 := by
    have h := Nat.mul_le_mul hQ hdt
    nlinarith only [h]
  have hdifference : 2 * Q ^ 2 * d * t ≤ 2 * S ^ 4 := by
    have h := Nat.mul_le_mul (Nat.pow_le_pow_left hQ 2) hdt
    nlinarith only [h]
  have hpower : 6 * t ^ 2 ≤ 6 * S ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ht 2)
  have hrow : n * (2 * ((R + 1) * (d * (2 * t))) + 2) + 1 ≤ 11 * S ^ 4 := by
    have hR' : R + 1 ≤ 2 * S := by omega
    have hprod := Nat.mul_le_mul hR' hdt
    have hinner : 2 * ((R + 1) * (d * (2 * t))) + 2 ≤ 8 * S ^ 3 + 2 := by
      nlinarith only [hprod]
    have houter := Nat.mul_le_mul hn hinner
    nlinarith only [houter, h14, hS2, h24]
  have hraw : (1 + n * (J - 1)) *
      (2 * (t + J + n) + 2 * d * (2 * t) + 2) ≤ 24 * S ^ 4 := by
    have hnj := Nat.mul_le_mul hn (show J - 1 ≤ S by omega)
    have hrecords : 1 + n * (J - 1) ≤ 2 * S ^ 2 := by nlinarith only [hnj, hS, hS2]
    have h := Nat.mul_le_mul hrecords hpiece
    nlinarith only [h]
  have hretained : t * J * (2 * (t + J + n) + 2 * d * (2 * t) + 2) ≤ 12 * S ^ 4 := by
    have htj : t * J ≤ S ^ 2 := by simpa [pow_two] using Nat.mul_le_mul ht hJ
    have h := Nat.mul_le_mul htj hpiece
    nlinarith only [h]
  have hall : n * (2 * n + 2 * (t * J *
      (2 * (t + J + n) + 2 * d * (2 * t) + 2)) + 4) ≤ 30 * S ^ 5 := by
    have hinner : 2 * n + 2 * (t * J *
        (2 * (t + J + n) + 2 * d * (2 * t) + 2)) + 4 ≤ 30 * S ^ 4 := by
      nlinarith only [hn, hretained, hS2, h24, h14]
    have h := Nat.mul_le_mul hn hinner
    nlinarith only [h]
  nlinarith only [htable, hinverse, hdifference, hpower, hrow, hraw, hall, h25, h35, h45]


/-- Every polynomial physical producer cap can share one retained input cap;
no transient service bound is recursively fed into the next loop iteration. -/
theorem finite_caps_polynomial {ι : Type*} [Fintype ι]
    (C degree : ι → ℕ) (length : ℕ) :
    ∀ i, C i * (length + 1) ^ degree i ≤
      (∑ j, C j) * (length + 1) ^ (∑ j, degree j) := by
  intro i
  apply Nat.mul_le_mul
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  · exact Nat.pow_le_pow_right (by omega)
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))



open SqrtLog SqrtLog.ProducedQueryResources in
/-- The actual chosen disjoint occurrence schedule bounds every pre-serialization
numeric model port by one original-input polynomial, uniformly over padding.
The narrow model bridge then supplies all concrete packing and ring dimensions. -/
theorem chosen_guarded_input_cap_of_scope_resources (k : ℕ) (hk : 2 ≤ k) :
    ∃ C degree cutoff : ℕ, ∀ n inputLength : ℕ, cutoff ≤ n → n ≤ inputLength →
      let B := 4 * DisjointReuse.SparseBudget.chooseM k 1
        (sparsifySchedule n) (by omega) ^ (k - 1)
      ∀ q : LeafQueryFrontend.Query, q.Valid → ambient q = n →
        0 < q.clauses.length → q.clauses.length ≤ n * B →
        q.scopeRows.length ≤ 3 * n + HashSelect.loopCap n q.clauses.length + 2 →
        HighIncidenceProgram.Prepare.mass q.scopeRows ≤
          (3 * n * SparseCode.degreeBound q.clauses.length B +
            (HashSelect.loopCap n q.clauses.length + 1) *
              SparseCode.distanceDenom q.clauses.length B + 1) * k →
        (∀ row ∈ q.scopeRows, row.length ≤
          (SparseCode.degreeBound q.clauses.length B + SparseCode.distanceDenom q.clauses.length B + 1) * k) →
        ∀ (padding : Fin 8 → ℕ) (j : Fin 64),
          (LeafParametersProgram.Execute.guardedModel (q.input k) padding).val j ≤
            C * (inputLength + 1) ^ degree := by
  obtain ⟨C, degree, cutoff, hcap⟩ := chosen_scalar_input_cap_of_scope_resources k hk
  refine ⟨C, degree, cutoff, ?_⟩
  intro n inputLength hn hinput B q hvalid hambient hnonempty hclauses hlen hmass harity padding j
  have h := (hcap n inputLength hn hinput q hvalid hambient hnonempty hclauses hlen hmass harity).2.2.2 padding
  exact QueryModelBudgets.serialized_model_values_le (q.input k) padding _ h j

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
