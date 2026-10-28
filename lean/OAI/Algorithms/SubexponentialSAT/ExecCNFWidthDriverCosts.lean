import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNFWidthDriver
import OAI.Algorithms.SubexponentialSAT.DyadicMaskedSearchBounds

namespace OAI.Algorithms

/-! Total actual instruction bound for the fixed-k width scan. -/

namespace SubexponentialSAT.ExecCNFWidthDriver

open BitProgram StructuredCalls
open scoped BigOperators

/-- Relate the complete per-width command to the masked-loop estimate. The
initializer and final tuple cleanup are retained as explicit additive costs. -/
theorem widthSearch_bound_le_masked (k m r budget initBudget : ℕ) :
    ExecCNFWidthSearch.bound k r (DyadicWidth.width m) budget initBudget ≤
      initBudget + DyadicMaskedSearchBounds.sourceBudget k m r budget +
        4 * (k + r * DyadicWidth.width m) + 4 * (r + 1) + 4 := by
  have hcount : 2 ^ (k + r * DyadicWidth.width m) ≤ 2 ^ k * (2 * (m + 1)) ^ r := by
    simpa only [List.singleton_append, List.sum_cons, List.sum_replicate, smul_eq_mul]
      using ExecCNFTupleEnumeration.masked_tuple_count_le m r k
  have hfactor : budget + 7 * (2 * (k + r * DyadicWidth.width m) + 2 * (r + 1) + 1) + 5 =
      budget + 14 * (k + r * DyadicWidth.width m) + 14 * (r + 1) + 12 := by ring
  have hmul := Nat.mul_le_mul_right
    (budget + 14 * (k + r * DyadicWidth.width m) + 14 * (r + 1) + 12) hcount
  simp only [ExecCNFWidthSearch.bound, DyadicMaskedSearchBounds.sourceBudget]
  rw [hfactor]
  omega

def widthCap (k : ℕ) (a : Data k) : ℕ :=
  (a.stacks (low k 14)).length + ∑ d : Width k, (dimension d).bits.length

def rowCap (k : ℕ) (a : Data k) : ℕ :=
  (a.stacks (low k 15)).length +
    ∑ d : Width k, (a.stacks (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d))).length

def searchCost (k : ℕ) (d : Width k) (F : Formula) (limit : List Bool) (a : Data k) : ℕ :=
  let rows := a.stacks (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d))
  let width := a.stacks (low k 20)
  let r := CounterPrograms.value rows
  let w := CounterPrograms.value width
  ExecCNFWidthSearch.bound k r w (callbackBudget F limit (dimension d).bits rows k r w)
    (ExecCNFTupleInitialize.bound k rows width)

def uniformStageBound (k : ℕ) (d : Width k) (F : Formula) (limit : List Bool) (a : Data k) : ℕ :=
  2 * widthCap k a + 2 * rowCap k a + 2 * (dimension d).bits.length +
    7 * (a.stacks (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d))).length + 12 +
    searchCost k d F limit a + 1

def CostFrame (k : ℕ) (base a : Data k) : Prop :=
  StageFrame k base a ∧ (a.stacks (low k 14)).length ≤ widthCap k base ∧
    (a.stacks (low k 15)).length ≤ rowCap k base

theorem costFrame_refl (k : ℕ) (a : Data k) : CostFrame k a a := by
  exact ⟨fun _ _ _ _ _ _ _ => rfl, Nat.le_add_right _ _, Nat.le_add_right _ _⟩

theorem StageFrame.bank {k : ℕ} {a b : Data k} (h : StageFrame k a b) (d : Width k) :
    b.stacks (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d)) =
      a.stacks (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d)) :=
  h _ (ExecCNFWidthLoad.bank_ne_low k _ _ 8) (ExecCNFWidthLoad.bank_ne_low k _ _ 13)
    (ExecCNFWidthLoad.bank_ne_low k _ _ 14) (ExecCNFWidthLoad.bank_ne_low k _ _ 15)
    (ExecCNFWidthLoad.bank_ne_low k _ _ 17) (ExecCNFWidthLoad.bank_ne_low k _ _ 21)

theorem StageFrame.indexWidth {k : ℕ} {a b : Data k} (h : StageFrame k a b) :
    b.stacks (low k 20) = a.stacks (low k 20) :=
  h _ ((ExecCNFWidthLoad.low_injective k).ne (by decide))
    ((ExecCNFWidthLoad.low_injective k).ne (by decide))
    ((ExecCNFWidthLoad.low_injective k).ne (by decide))
    ((ExecCNFWidthLoad.low_injective k).ne (by decide))
    ((ExecCNFWidthLoad.low_injective k).ne (by decide))
    ((ExecCNFWidthLoad.low_injective k).ne (by decide))

theorem dimension_length_le_cap (k : ℕ) (base : Data k) (d : Width k) :
    (dimension d).bits.length ≤ widthCap k base := by
  have h := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Nat.zero_le (dimension i).bits.length) (Finset.mem_univ d)
  unfold widthCap
  omega

theorem row_length_le_cap (k : ℕ) (base : Data k) (d : Width k) :
    (base.stacks (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d))).length ≤ rowCap k base := by
  have h := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Nat.zero_le (base.stacks (ExecCNFWidthLoad.bank k (dimension i) (dimension_le i))).length)
    (Finset.mem_univ d)
  unfold rowCap
  omega

theorem costFrame_after_stage {k : ℕ} (base a b : Data k) (d : Width k)
    (hc : CostFrame k base a) (hf : StageFrame k a b)
    (h14 : b.stacks (low k 14) = (dimension d).bits)
    (h15 : b.stacks (low k 15) = a.stacks (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d))) :
    CostFrame k base b := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi8 hi13 hi14 hi15 hi17 hi21
    exact (hf i hi8 hi13 hi14 hi15 hi17 hi21).trans
      (hc.1 i hi8 hi13 hi14 hi15 hi17 hi21)
  · rw [h14]
    exact dimension_length_le_cap k base d
  · rw [h15, hc.1.bank d]
    exact row_length_le_cap k base d

theorem stageBound_le_uniform {k : ℕ} (base a : Data k) (d : Width k)
    (F : Formula) (limit : List Bool) (hc : CostFrame k base a) :
    stageBound k d F limit a ≤ uniformStageBound k d F limit base := by
  have hbank := hc.1.bank d
  have hwidth := hc.1.indexWidth
  have h14 : (a.stacks (ExecCNFWidthLoad.low k 14)).length ≤ widthCap k base := hc.2.1
  have h15 : (a.stacks (ExecCNFWidthLoad.low k 15)).length ≤ rowCap k base := hc.2.2
  simp only [stageBound, uniformStageBound, searchCost, ExecCNFWidthLoad.bound]
  rw [hbank, hwidth]
  omega

def scanBound (k : ℕ) (ds : List (Width k)) (F : Formula) (limit : List Bool) (base : Data k) : ℕ :=
  (ds.map (fun d => uniformStageBound k d F limit base)).sum + 2 * (ds.length + 1)

/-- Every actual stage is priced at a fixed bound computed from the initial
parameter bank and initial old-word lengths. Guard and terminal tests are
included even if the scan stops after an early success. -/
theorem scan_exists_bound (k : ℕ) (ds : List (Width k)) (F : Formula) (limit : List Bool)
    (base a : Data k) (ha : a.stacks (low k 21) = [] → Ready F limit a)
    (hcost : CostFrame k base a) :
    ∃ (visited : List (Width k)) (n : ℕ) (b : Data k), Visits k ds visited n a b ∧
      n ≤ scanBound k ds F limit base ∧
      (b.stacks (low k 21) = [] → Ready F limit b) ∧ CostFrame k base b := by
  induction ds generalizing a with
  | nil => exact ⟨[], 0, a, .done a, Nat.zero_le _, ha, hcost⟩
  | cons d ds ih =>
    by_cases hw : a.stacks (low k 21) = []
    · have hpa : Ready F limit (peeked a) :=
        ExecCNFWidthInvariant.ready_of_stacks_eq F limit a (peeked a) (ha hw) rfl
      have hpcost : CostFrame k base (peeked a) := hcost
      obtain ⟨ns, b, hstage, hns, h14, h15, _, _, _, hframe, hb, _⟩ :=
        stage_eval k d F limit (peeked a) hpa
      have hbcost := costFrame_after_stage base (peeked a) b d hpcost hframe h14 h15
      have hns' := hns.trans (stageBound_le_uniform base (peeked a) d F limit hpcost)
      obtain ⟨visited, nt, c, htail, hnt, hc, hccost⟩ := ih b hb hbcost
      refine ⟨d :: visited, ns + nt + 2, c, .step hw hstage htail, ?_, hc, hccost⟩
      simp only [scanBound, List.map_cons, List.sum_cons, List.length_cons] at hnt ⊢
      omega
    · refine ⟨[], 2, peeked a, .stopped hw, ?_, fun h => False.elim (hw h), hcost⟩
      simp only [scanBound, List.length_cons]
      omega

def totalBound (k : ℕ) (F : Formula) (limit : List Bool) (a : Data k) : ℕ :=
  scanBound k (List.finRange (k - 1)) F limit a + 1

/-- Keep the concrete width log and its measured trace together, so the
semantic minimum-width proof and the runtime bound apply to the same run. -/
theorem program_runs_costed (k : ℕ) (F : Formula) (limit : List Bool)
    (a : Data k) (ha : Ready F limit a) :
    ∃ (visited : List (Width k)) (n : ℕ) (b : Data k),
      Trace (program k) (n + 1)
        (a.withPC (some (program k).entry)) (b.withPC none) ∧
      n + 1 ≤ totalBound k F limit a ∧
      Visits k (List.finRange (k - 1)) visited n a b ∧
      visited <+: List.finRange (k - 1) ∧
      (b.stacks (low k 21) = [] → Ready F limit b) ∧ StageFrame k a b := by
  obtain ⟨visited, n, b, hlog, hn, hb, hf⟩ :=
    scan_exists_bound k (List.finRange (k - 1)) F limit a a (fun _ => ha) (costFrame_refl k a)
  exact ⟨visited, n, b, compiled_halt_trace hlog.eval (low k 16) (low k 21),
    by unfold totalBound; omega, hlog, hlog.visited_prefix, hb, hf.1⟩

theorem program_runs_bound (k : ℕ) (F : Formula) (limit : List Bool)
    (a : Data k) (ha : Ready F limit a) :
    ∃ (visited : List (Width k)) (b : Data k), RunsIn (program k) (totalBound k F limit a)
      (a.withPC (some (program k).entry)) (b.withPC none) ∧
      visited <+: List.finRange (k - 1) ∧
      (b.stacks (low k 21) = [] → Ready F limit b) ∧ StageFrame k a b := by
  obtain ⟨visited, n, b, hlog, hn, hb, hf⟩ :=
    scan_exists_bound k (List.finRange (k - 1)) F limit a a (fun _ => ha) (costFrame_refl k a)
  exact ⟨visited, b, ⟨n + 1, by unfold totalBound; omega,
    compiled_halt_trace hlog.eval (low k 16) (low k 21)⟩, hlog.visited_prefix, hb, hf.1⟩

end SubexponentialSAT.ExecCNFWidthDriver

end OAI.Algorithms
