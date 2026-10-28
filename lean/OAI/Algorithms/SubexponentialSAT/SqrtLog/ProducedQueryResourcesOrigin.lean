import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblySelectedGuards
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyHighMask

namespace OAI.Algorithms

/-! Actual selector provenance for a query.  This package includes every
trial (successful or not), the final selected rows, and an optional mark.
It carries no resource inequality about the resulting query. -/
namespace SubexponentialSAT.SqrtLog.ProducedQueryResources
open Filter
open scoped Topology
open Asymptotic HashSelectProgram LeafQueryFrontend LeafScopeResourceBounds HighIncidenceProgram

noncomputable section

abbrev ambient (q : Query) := BinaryArithmetic.toNat q.ambient

/-- Inputs and exact row identity of an actual generated selector query. -/
structure Origin (q : Query) (k B : ℕ) where
  nonempty : 0 < q.clauses.length
  width : ∀ i, (q.codes i).length ≤ k
  shifts : SparseCode.SuppliedShifts q.clauses.length B
  localCode : SparseCode.SuppliedLocal q.clauses.length B
  countWord : List Bool
  score : Records → List Bool → List Bool
  seed : List Bool
  rest : Records
  count : CounterPrograms.value countWord = 3*q.clauses.length
  family : generatedPayloads (SubexpAlphabetProgram.alphabetWords countWord)
    (SparseCode.distanceDenom q.clauses.length B) = seed :: rest
  rows : let initial := initialPayloads countWord.length
            (CodeRowsProgram.serializedRows q.clauses.length shifts localCode)
         let decode := rawDecode q.clauses.length countWord.length nonempty
         (∃ round bits, round ≤ HashSelect.loopCap (ambient q) q.clauses.length ∧
           bits ∈ seed :: rest ∧ q.rows = trial decode score seed rest initial round bits) ∨
         q.rows = (selected score seed rest initial
           (HashSelect.loopCap (ambient q) q.clauses.length)).map decode

/-- Numerical output from the actual neutral-completed scan and high mask. -/
structure ScanBounds (q : Query) (k exponent : ℕ) : Prop where
  guard : LeafParametersProgram.Guard (q.input k)
  residual : (q.input k).freeCount ≤ ambient q ∧ ambient q ≤ 2*(q.input k).freeCount
  factors : (q.input k).factors ≤ 4*ambient q+HashSelect.loopCap (ambient q) q.clauses.length+2
  occurrence : (q.input k).occurrence ≤ L (q.input k).freeCount^exponent
  arity : (q.input k).arity ≤ L (q.input k).freeCount^exponent
  branch : (Branches.trueCount (highMask q.scopeRows (ambient q)) : ℝ) ≤
    (ambient q : ℝ)/Real.sqrt (L (ambient q) : ℝ)

private theorem input_as_scan (q : Query) (k : ℕ) (hv : q.Valid) :
    q.input k = CostAssembly.measuredParameterInput q.scopeRows
      (LeafScopeResourceBounds.forwardMask q.scopeRows
        (HighIncidenceProgram.Prepare.cut q.scopeRows q.ambient
          (EarlyThreshold.threshold (ambient q)).bits) (ambient q)) q.clauses.length k := by
  rw [q.input_eq_measured k hv.2.2.2.2.2.1]
  congr 1
  simp only [Query.forward, highMask, LeafScopeResourceBounds.forwardMask,
    HighIncidenceProgram.Prepare.cut, ArithmeticExpressionSupport.bits_value, ambient]

/-- One cutoff for all generated queries and marks. No cardinality, rank,
head-size, or runtime premise is hidden in selector provenance. -/
theorem eventually_scan_bounds (k qi : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (q : Query) (B : ℕ), q.Valid → ambient q=n →
      Origin q k B → 0 < B → q.clauses.length ≤ n*B → B ≤ L n^qi →
      ScanBounds q k (LeafScopeResourceBounds.resourceExponent qi+1) := by
  filter_upwards [CostAssembly.eventually_generated_trial_guards k qi,
    CostAssembly.eventually_generated_selected_guards k qi] with n htrial hselected q B hv hn o hB hm hBL
  have ht : BinaryArithmetic.toNat (EarlyThreshold.threshold (ambient q)).bits = Nat.sqrt (L n)+1 := by
    rw [ArithmeticExpressionSupport.bits_value]
    simp only [EarlyThreshold.threshold,hn]
  have hscan := input_as_scan q k hv
  have hout : LeafParametersProgram.Guard (q.input k) ∧
      LeafParametersProgram.passes (q.input k)=true ∧
      LeafParametersProgram.dispatch (q.input k)=.sparse ∧
      (q.input k).freeCount ≤ n ∧ n ≤ 2*(q.input k).freeCount ∧
      (q.input k).factors ≤ 4*n+HashSelect.loopCap n q.clauses.length+2 ∧
      (q.input k).occurrence ≤ L (q.input k).freeCount^(LeafScopeResourceBounds.resourceExponent qi+1) ∧
      (q.input k).arity ≤ L (q.input k).freeCount^(LeafScopeResourceBounds.resourceExponent qi+1) := by
    rcases o.rows with hrows | hrows
    · obtain ⟨round,bits,hr,hbits,hrows⟩ := hrows
      have hh := htrial B 1 0 round q.clauses o.nonempty q.codes o.shifts o.localCode
        o.countWord o.score o.seed o.rest bits q.mark q.ambient
        (EarlyThreshold.threshold (ambient q)).bits o.width o.count o.family hbits
        hB hm hBL (by simpa only [hn] using hr) hn ht
      rw [hscan]
      simpa only [Query.scopeRows,hrows,hn] using hh
    · have hh := hselected B 1 0 q.clauses o.nonempty q.codes o.shifts o.localCode
        o.countWord o.score o.seed o.rest q.mark q.ambient
        (EarlyThreshold.threshold (ambient q)).bits o.width o.count o.family hB hm hBL hn ht
      rw [hscan]
      simpa only [Query.scopeRows,hrows,hn] using hh
  refine ⟨hout.1,?_,?_,hout.2.2.2.2.2.2.1,hout.2.2.2.2.2.2.2,?_⟩
  · simpa only [hn] using And.intro hout.2.2.2.1 hout.2.2.2.2.1
  · simpa only [hn] using hout.2.2.2.2.2.1
  · exact CostAssembly.highBranchCount_le_sqrt q.scopeRows (ambient q) hv.2.1

end
end SubexponentialSAT.SqrtLog.ProducedQueryResources

end OAI.Algorithms
