import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutExecution
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutChoicesTrace
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutRowsTrace

namespace OAI.Algorithms

/-! The complete layout execution with the actual intermediate traces used
by every summand of its bound. This is additive to the semantic execution
interface and does not change the fixed program. -/

namespace SubexponentialSAT.SubexpMainLayoutTrace

open BitProgram StructuredCalls SubexpMainProgram Subexp
open SubexpLayoutPorts (Allocation ordinary master)
open SubexpMainLayoutExecution

variable {er es p r Δ R D : ℕ} [Fact p.Prime] [NeZero r]

structure StageTrace (alloc : Allocation es) (hregs : 16 ≤ er)
    (a factorState assignmentState start coefficientState packingState middle out : MainState er es)
    {hr : 0 < r} {hQ : 0 < p^4 - 1} {scopes : List (List ℕ)}
    {hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ}
    {tables : List (List Bool)}
    (result : Result hregs alloc a middle out p r Δ R D hr hQ scopes hd tables)
    (factorBudget : ℕ) : Prop where
  choices : SubexpMainLayoutChoicesTrace.StageTrace alloc hregs a factorState assignmentState
    start coefficientState packingState middle result.choices factorBudget
  rows : SubexpMainLayoutRowsTrace.StageTrace (List.ofFn result.choices.coefficients)
    result.choices.packing.packing scopes hd result.rows

/-- The fixed choices and row programs execute in sequence. All storage
and semantic inputs to the row producer are derived from earlier outputs. -/
theorem execution (alloc : Allocation es) (hregs : 16 ≤ er) (a : MainState er es)
    (p r Δ R k B : ℕ) [Fact p.Prime] [NeZero r]
    (hr : 0 < r) (hQ : 0 < p^4 - 1) (h2 : (2 : ZMod p) ≠ 0)
    (hell : 0 < CounterPrograms.value (SubexpMainLayout.Factors.sourceInputs alloc a).counts.ell)
    (hwidth : CounterPrograms.value (SubexpMainLayout.Factors.sourceInputs alloc a).counts.ell ≤
      (SubexpMainLayout.Factors.sourceInputs alloc a).counts.modulus.length)
    (hp : 0 < BinaryArithmetic.toNat (SubexpMainLayout.Factors.sourceInputs alloc a).counts.modulus)
    (G : SubexpLeafData.Leaf
      (SubexpLayoutConstruction.variableCount (SubexpMainLayout.Factors.sourceInputs alloc a)))
    (hG : (G.map ExecCNF.clauseSet).Nodup)
    (hsource : (SubexpMainLayout.Factors.sourceInputs alloc a).leaf =
      Encoding.encodeList SubexpClauseRowProgram.clauseBytes G)
    (hD : SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a) =
      ChunkPartition.count
        (SubexpLayoutConstruction.variableCount (SubexpMainLayout.Factors.sourceInputs alloc a))
        (CounterPrograms.value (SubexpMainLayout.Factors.sourceInputs alloc a).counts.ell))
    (hcap : 2 ^ CounterPrograms.value (SubexpMainLayout.Factors.sourceInputs alloc a).counts.ell ≤ p)
    (hk : 1 ≤ k) (hw : SAT.WidthAtMost k (ExecCNF.formulaSet G))
    (ho : SAT.OccurrenceAtMost B (ExecCNF.formulaSet G)) (hne : [] ∉ G)
    (hdelta : 1 + CounterPrograms.value (SubexpMainLayout.Factors.sourceInputs alloc a).counts.ell * B ≤ Δ)
    (hmeta : ∀ i, CounterPrograms.value
      (a.stacks (persistent es (SubexpMainAssignment.metadataIndex i))) =
      (![r, p^4 - 1, Δ, SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)] :
        Fin 4 → ℕ) i)
    (hzero : ∀ i : Fin 672, a.stacks (ordinary alloc i) = [])
    (hpw : CounterPrograms.value (a.stacks (persistent es 6)) = p)
    (hrw : CounterPrograms.value (a.stacks (persistent es 21)) = r)
    (hQw : CounterPrograms.value (a.stacks (persistent es 17)) = p^4 - 1)
    (hRw : CounterPrograms.value (a.stacks (persistent es 25)) = R)
    (hprecision : BinaryArithmetic.toNat (a.stacks (persistent es 22)) =
      SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a) + 1)
    (hexp : BinaryArithmetic.toNat (a.stacks (persistent es 29)) = p^4 - 2) :
    let hv := SubexpLayoutConstruction.family_valid
      (SubexpMainLayout.Factors.sourceInputs alloc a) hp hell hwidth hD
    let scopes := SubexpLayoutScopeOrder.orderedScopes
      (SubexpMainLayout.Factors.sourceInputs alloc a) G hG hell
    ∃ hd : ∀ v : Fin (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)),
        IncidencePlanSpec.degree scopes v.val ≤ Δ,
      ∃ factorState assignmentState start coefficientState packingState middle out n,
        ∃ result : Result hregs alloc a middle out p r Δ R
          (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a))
          hr hQ scopes hd
          (SubexpLayoutConstruction.tables (SubexpMainLayout.Factors.sourceInputs alloc a) hv G),
          n ≤ SubexpMainLayoutPrefix.runtimeBound alloc a factorState assignmentState hv G hG hell r (p^4 - 1) Δ +
            SubexpMainLayoutChoices.tailBound alloc hregs a start coefficientState packingState middle result.choices +
            SubexpMainLayoutRows.runtimeBound (List.ofFn result.choices.coefficients)
              result.choices.packing.packing scopes hd result.rows + 2 ∧
          StageTrace alloc hregs a factorState assignmentState start coefficientState packingState middle out
            result (SubexpMainLayout.Factors.runtimeBound alloc a hv G) ∧
          SubexpMainLayoutChoices.EntryFacts alloc a packingState ∧
          Eval (SubexpMainLayoutProgram.procedure er hregs alloc).invoke n a out := by
  dsimp only
  obtain ⟨hd, factorState, assignmentState, start, coefficientState, packingState,
    middle, nc, hc, hnc, hct, hentry, hec⟩ := SubexpMainLayoutChoicesTrace.execution alloc hregs a
      p r (p^4 - 1) Δ R k B hr hQ h2 hell hwidth hp G hG hsource hD hcap
      hk hw ho hne hdelta hmeta hzero hpw hrw hQw hRw
  obtain ⟨out, hs, nr, hnr, her, hrt⟩ := SubexpMainLayoutRowsTrace.execution
    (List.ofFn hc.coefficients) hc.packing.packing _ hd hregs alloc middle
    (choices_staticInputs hc hRw) (choices_workspaceReady hc)
    (by rw [hc.prefixResult.persistent]; simpa only [CounterPrograms.value_eq_toNat] using hpw)
    (by rw [hc.prefixResult.persistent]; exact hprecision)
    (by rw [hc.prefixResult.persistent]; exact hexp)
    (orderedScopes_valid _ G hG hell hD) h2
  let result : Result hregs alloc a middle out p r Δ R _ hr hQ _ hd _ := ⟨hc, hs⟩
  refine ⟨hd, factorState, assignmentState, start, coefficientState, packingState,
    middle, out, nc + nr + 1, result, ?_, ⟨hct, hrt⟩, hentry, ?_⟩
  · dsimp only [result]
    omega
  · exact SubexpProcedureCompose.sequence_invoke _ _ hec her


end SubexponentialSAT.SubexpMainLayoutTrace


end OAI.Algorithms
