import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryParameterBudgets
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResourcesBounds

/-! The original explicit resource record for the actual packing has the
sqrt-log bound from the new literal scope estimates. No identity with the old
selector history is used. These are numerical bounds on that record; a caller
still composes and bounds the actual streamed execution. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets

open Filter OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic
  OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources
  OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open scoped Topology

noncomputable section

/-- Every sharp resource field follows from the actual scan and the two
geometric quantities. The cutoff is independent of all query inputs. -/
theorem eventually_make_bounds_of_scan (k qi ql C d e : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (q : Query) (B rows size : ℕ), ambient q = n →
      ScanBounds q k ql → q.clauses.length ≤ n * B → B ≤ L n ^ qi →
      (16 * (layoutR (q.input k).freeCount : ℝ) *
        (L (q.input k).freeCount : ℝ)^2 * (rows : ℝ) ≤ (q.input k).freeCount) →
      ((size : ℝ) ≤ 2 * (n : ℝ) / layoutR (q.input k).freeCount) →
      Bounds qi ql (9*e+8) n (make q k B rows size C d qi e) := by
  filter_upwards [eventually_ambient_commonBase_log ql,
    CodeSetupOuterCost.setupMajorant_target C d qi, eventually_ge_atTop (1 : ℕ)]
    with n hbase hsetup hn q B rows size hqn hs hc hBL hrows hsize
  have hb := hs.guard.2.2.2.1
  have hnfree : n ≤ 2 * (q.input k).freeCount := by
    simpa only [hqn] using hs.residual.2
  refine ⟨?_, hc, hBL, hs.occurrence, ?_, ?_, by dsimp [make]; omega,
    hrows, ?_, ?_, hsize, ?_, ?_⟩
  · simpa only [make, hqn] using hs.residual
  · simpa only [make, hqn] using hs.factors
  · simpa only [make, hqn] using hs.branch
  · simpa only [make, matrixHeight, hqn] using
      hbase (q.input k).freeCount (q.input k).occurrence hnfree hb hs.occurrence
  · simpa only [make, hqn] using heads_le_ambient q k hs.guard
  · simpa only [make, hqn] using hsetup
  · simpa only [hqn] using make_ordinary_bound q k B rows size C d qi e (by omega)

/-- The searched complete alphabet supplies both actual selected-rank and
balanced-head bounds; neither number is an additional certificate input. -/
theorem eventually_ofPacking_bounds_of_scan (k qi ql C d e : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (q : Query) (B : ℕ), ambient q = n →
      ScanBounds q k ql → q.clauses.length ≤ n * B → B ≤ L n ^ qi →
      ∀ (hg : LeafParametersProgram.Guard (q.input k))
        (a : Word (problem q k hg).r (problem q k hg).Q)
        (tail : List (Word (problem q k hg).r (problem q k hg).Q)),
        (a :: tail).Nodup → (∀ z, z ∈ a :: tail) →
        Bounds qi ql (9*e+8) n (ofPacking q k B C d qi e hg a tail) := by
  filter_upwards [eventually_make_bounds_of_scan k qi ql C d e]
    with n hbound q B hqn hs hc hBL hg a tail haN haC
  apply hbound q B _ _ hqn hs hc hBL
  · exact rank_budget q k hg a tail haN haC
  · simpa only [hqn] using headSize_budget q k hg a tail haN haC

/-- The fixed-power envelope of this very same resource record retains the
unchanged runtime scale. The real native cost must be bounded by this envelope
in the execution composition, separately from this numerical statement. -/
theorem eventually_ofPacking_envelope_of_scan (k qi ql C d e power ordinaryPower : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (q : Query) (B : ℕ), ambient q = n →
      ScanBounds q k ql → q.clauses.length ≤ n * B → B ≤ L n ^ qi →
      ∀ (hg : LeafParametersProgram.Guard (q.input k))
        (a : Word (problem q k hg).r (problem q k hg).Q)
        (tail : List (Word (problem q k hg).r (problem q k hg).Q)),
        (a :: tail).Nodup → (∀ z, z ∈ a :: tail) →
        (nativeEnvelope k n power ordinaryPower (ofPacking q k B C d qi e hg a tail) : ℝ) ≤
          (18 : ℝ)^power * (2 : ℝ)^((1 + (power : ℝ) * exponentConstant k ql) *
            Statement.runtimeScale n) := by
  filter_upwards [eventually_ofPacking_bounds_of_scan k qi ql C d e,
    eventually_nativeEnvelope_bound k qi ql (9*e+8) power ordinaryPower]
    with n hrecord hbound q B hqn hs hc hBL hg a tail haN haC
  exact hbound _ (hrecord q B hqn hs hc hBL hg a tail haN haC)

/-- The original jet order is exactly the order of the actual serialized
parameter producer, including ambient precision and neutral factors. -/
theorem produced_order_eq (q : Query) (k B C d qi e : ℕ)
    (hg : LeafParametersProgram.Guard (q.input k))
    (a : Word (problem q k hg).r (problem q k hg).Q)
    (tail : List (Word (problem q k hg).r (problem q k hg).Q)) (hv : q.Valid) :
    (LeafParametersProgram.produce (q.input k)).J =
      jetOrder k (ambient q) (ofPacking q k B C d qi e hg a tail) := by
  unfold LeafParametersProgram.produce jetOrder jetNumerator ofPacking make
  dsimp only
  rw [input_ambient, input_width, input_clauses q k hv]

/-- One width-dependent cutoff closes every sharp field and its fixed-power
bound for every literal history, losing trial, optional mark, and complete
alphabet. Physical padding and measured execution costs are separate. -/
theorem chosen_ofPacking_cutoff (k C d e power ordinaryPower : ℕ) (hk : 2 ≤ k) :
    ∃ cutoff : ℕ, ∀ n ≥ cutoff,
      let B := 4 * DisjointReuse.SparseBudget.chooseM k 1
        (sparsifySchedule n) (by omega) ^ (k - 1)
      ∀ q : Query, q.Valid → ambient q = n →
        0 < q.clauses.length → q.clauses.length ≤ n * B →
        q.scopeRows.length ≤ 3 * n + HashSelect.loopCap n q.clauses.length + 2 →
        HighIncidenceProgram.Prepare.mass q.scopeRows ≤
          (3 * n * SparseCode.degreeBound q.clauses.length B +
            (HashSelect.loopCap n q.clauses.length + 1) *
              SparseCode.distanceDenom q.clauses.length B + 1) * k →
        (∀ row ∈ q.scopeRows, row.length ≤
          (SparseCode.degreeBound q.clauses.length B +
            SparseCode.distanceDenom q.clauses.length B + 1) * k) →
        ScanBounds q k (4*k+3) ∧ SmallInputs q k n ∧
        ∀ (hg : LeafParametersProgram.Guard (q.input k))
          (a : Word (problem q k hg).r (problem q k hg).Q)
          (tail : List (Word (problem q k hg).r (problem q k hg).Q)),
          (a :: tail).Nodup → (∀ z, z ∈ a :: tail) →
          let p := ofPacking q k B C d (2*(k-1)+1) e hg a tail
          Bounds (2*(k-1)+1) (4*k+3) (9*e+8) n p ∧
          (nativeEnvelope k n power ordinaryPower p : ℝ) ≤
            (18 : ℝ)^power * (2 : ℝ)^((1 + (power : ℝ) * exponentConstant k (4*k+3)) *
              Statement.runtimeScale n) := by
  obtain ⟨N, hN⟩ := chosen_query_scalars_cutoff_of_scope_resources k hk
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    (((eventually_ofPacking_bounds_of_scan k (2*(k-1)+1) (4*k+3) C d e).and
      (eventually_nativeEnvelope_bound k (2*(k-1)+1) (4*k+3) (9*e+8) power ordinaryPower)).and
      (chosen_sparseBound_eventually_le_log2_power k))
  refine ⟨max N M, ?_⟩
  intro n hn B q hv hqn hm hc hlen hmass har
  obtain ⟨hs, hsmall⟩ := (hN n (by omega)).2.2 q hv hqn hm hc hlen hmass har
  obtain ⟨⟨hrecord, hbound⟩, hB⟩ := hM n (by omega)
  refine ⟨hs, hsmall, ?_⟩
  intro hg a tail haN haC
  have hb : B ≤ L n ^ (2*(k-1)+1) := by simpa only [B, L] using hB
  have hp := hrecord q B hqn hs hc hb hg a tail haN haC
  exact ⟨hp, hbound _ hp⟩

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets
