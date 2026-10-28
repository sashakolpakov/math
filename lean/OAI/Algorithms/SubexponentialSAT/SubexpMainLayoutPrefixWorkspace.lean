import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutPrefix

namespace OAI.Algorithms

/-!
# Cleared workspace after the actual Main layout prefix

The published factor, assignment and type procedures are unchanged.  Their
actual output and frame contracts imply that initially empty ordinary words
below640 remain empty, while the generated outputs are retained above640.
-/

namespace SubexponentialSAT.SubexpMainLayoutPrefixWorkspace

open BitProgram StructuredCalls SubexpMainProgram SubexpMainLayout Subexp
open SubexpLayoutPorts (Allocation master ordinary)

def WorkspaceEmpty {er es : ℕ} (alloc : Allocation es) (a : MainState er es) : Prop :=
  ∀ i : Fin 640, a.stacks (ordinary alloc (i.castAdd 32)) = []

theorem factors_work_frame {er es : ℕ} {alloc : Allocation es}
    {a b : MainState er es} {scopes tables : List (List Bool)}
    (h : Factors.Result alloc a b scopes tables) (j : Fin (totalStacks es))
    (hlo : 48 ≤ j.val) (hhi : j.val < 640) : b.stacks j = a.stacks j := by
  apply h.frame
  rintro ⟨i, hi⟩
  by_cases hm : 35 ≤ (Factors.permutation i).val ∧ (Factors.permutation i).val < 42
  · have hl := Factors.highPort_large alloc ⟨(Factors.permutation i).val - 35, by omega⟩
    simp only [Factors.stackMap, Factors.baseMap, dite_eq_left hm] at hi
    rw [hi] at hl
    omega
  · have hv := congrArg (fun z : Fin (totalStacks es) => z.val) hi
    have hb := (Factors.permutation i).isLt
    simp only [Factors.stackMap, Factors.baseMap, dite_eq_right hm, ordinary] at hv
    omega

theorem types_workspace {er es : ℕ} {alloc : Allocation es}
    {a b : MainState er es} {r Q Δ : ℕ}
    (h : SubexpMainUniversalTypes.Result alloc a b r Q Δ)
    (ha : WorkspaceEmpty alloc a) : WorkspaceEmpty alloc b := by
  intro i
  by_cases h9 : i.val < 9
  · exact h.scratch ⟨i.val, h9⟩
  by_cases h12 : i.val = 12
  · have he : i.castAdd 32 = (12 : Fin 672) := Fin.ext h12
    rw [he]
    exact h.temporary
  apply (h.frame _ ?_).trans (ha i)
  rintro ⟨j, hj⟩
  have hv := congrArg (fun z : Fin (totalStacks es) => z.val) hj
  by_cases hw : j.val < 9 ∨ j.val = 12
  · simp only [SubexpMainUniversalTypes.stackMap, dite_eq_left hw, ordinary,
      Fin.val_castAdd] at hv
    rcases hw with hw | hw <;> omega
  · simp only [SubexpMainUniversalTypes.stackMap, dite_eq_right hw,
      SubexpLayoutPorts.master_val, ordinary, Fin.val_castAdd] at hv
    omega

theorem workspace_of_stages {er es : ℕ} {alloc : Allocation es}
    {a b c d : MainState er es} {r Q Δ D : ℕ} {scopes : List (List ℕ)}
    {hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ}
    {first : MulticolorTypes.Word r Q} {tail : List (MulticolorTypes.Word r Q)}
    {scopeRecords tables : List (List Bool)}
    (hf : Factors.Result alloc a b scopeRecords tables)
    (ha : SubexpMainAssignment.Result alloc b c r Q Δ D scopes hd first tail)
    (hu : SubexpMainUniversalTypes.Result alloc c d r Q Δ)
    (hzero : WorkspaceEmpty alloc a) : WorkspaceEmpty alloc d := by
  apply types_workspace hu
  intro i
  by_cases hi : i.val < 51
  · exact ha.scratch ⟨i.val, hi⟩
  · exact (ha.work_frame _ (by change 51 ≤ i.val; omega) (by exact i.isLt)).trans
      ((factors_work_frame hf _ (by change 48 ≤ i.val; omega) (by exact i.isLt)).trans (hzero i))

/-- The same actual prefix execution and semantic result, together with the
cleared low-workspace fact needed by the next Main procedure. -/
theorem execution_workspace {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (r Q Δ : ℕ) [NeZero r]
    (hell : 0 < CounterPrograms.value (Factors.sourceInputs alloc a).counts.ell)
    (hwidth : CounterPrograms.value (Factors.sourceInputs alloc a).counts.ell ≤
      (Factors.sourceInputs alloc a).counts.modulus.length)
    (hv : SubexpClauseFamilyProgram.Valid
      (SubexpLayoutConstruction.familyInputs (Factors.sourceInputs alloc a))
      (SubexpLayoutConstruction.dimension (Factors.sourceInputs alloc a))
      (SubexpLayoutConstruction.variableCount (Factors.sourceInputs alloc a)))
    (G : SubexpLeafData.Leaf (SubexpLayoutConstruction.variableCount (Factors.sourceInputs alloc a)))
    (hG : (G.map ExecCNF.clauseSet).Nodup)
    (hsource : (Factors.sourceInputs alloc a).leaf =
      Encoding.encodeList SubexpClauseRowProgram.clauseBytes G)
    (hD : SubexpLayoutConstruction.dimension (Factors.sourceInputs alloc a) =
      ChunkPartition.count (SubexpLayoutConstruction.variableCount (Factors.sourceInputs alloc a))
        (CounterPrograms.value (Factors.sourceInputs alloc a).counts.ell))
    (hd : ∀ v : Fin (SubexpLayoutConstruction.dimension (Factors.sourceInputs alloc a)),
      IncidencePlanSpec.degree
        (SubexpLayoutScopeOrder.orderedScopes (Factors.sourceInputs alloc a) G hG hell) v.val ≤ Δ)
    (hmeta : ∀ i, CounterPrograms.value
      (a.stacks (persistent es (SubexpMainAssignment.metadataIndex i))) =
      (![r, Q, Δ, SubexpLayoutConstruction.dimension (Factors.sourceInputs alloc a)] : Fin 4 → ℕ) i)
    (hzero : WorkspaceEmpty alloc a) :
    ∃ b c, ∃ first : MulticolorTypes.Word r Q, ∃ tail : List (MulticolorTypes.Word r Q),
      ∃ n ≤ SubexpMainLayoutPrefix.runtimeBound alloc a b c hv G hG hell r Q Δ, ∃ d,
      (first :: tail).Nodup ∧ (∀ w, w ∈ first :: tail) ∧
      Eval (SubexpMainLayoutPrefix.procedure er alloc).invoke n a d ∧
      SubexpMainLayoutPrefix.Result alloc a d r Q Δ
        (SubexpLayoutConstruction.dimension (Factors.sourceInputs alloc a))
        (SubexpLayoutScopeOrder.orderedScopes (Factors.sourceInputs alloc a) G hG hell)
        hd first tail (SubexpLayoutConstruction.tables (Factors.sourceInputs alloc a) hv G) ∧
      WorkspaceEmpty alloc d := by
  obtain ⟨nf, hnf, b, hef, hrf⟩ := Factors.execution alloc a hell hwidth hv G hsource
  have hs : b.stacks (master alloc 0) = SubexpPlanAlphabetBase.scopeBytes
      (SubexpLayoutScopeOrder.orderedScopes (Factors.sourceInputs alloc a) G hG hell) :=
    hrf.scopes.trans (SubexpLayoutScopeOrder.scope_stream_eq _ hv G hG hell hD)
  have hm (i : Fin 4) : CounterPrograms.value
      (b.stacks (persistent es (SubexpMainAssignment.metadataIndex i))) =
      (![r, Q, Δ, SubexpLayoutConstruction.dimension (Factors.sourceInputs alloc a)] : Fin 4 → ℕ) i := by
    rw [SubexpMainLayoutPrefix.factors_persistent_frame hrf]
    exact hmeta i
  obtain ⟨first, tail, na, hna, c, hn, hall, hea, hra⟩ :=
    SubexpMainAssignment.execution alloc b r Q Δ
      (SubexpLayoutConstruction.dimension (Factors.sourceInputs alloc a))
      (SubexpLayoutScopeOrder.orderedScopes (Factors.sourceInputs alloc a) G hG hell) hd hm hs
  have hdelta : c.stacks (master alloc 7) = List.replicate Δ true := hra.headers 2
  obtain ⟨nu, hnu, d, heu, hru⟩ :=
    SubexpMainUniversalTypes.execution alloc c r Q Δ hra.alphabet hdelta
  refine ⟨b, c, first, tail, nf + (na + nu + 1) + 1, ?_, d, hn, hall, ?_, ?_, ?_⟩
  · unfold SubexpMainLayoutPrefix.runtimeBound
    omega
  · exact SubexpProcedureCompose.sequence_invoke _ _ hef
      (SubexpProcedureCompose.sequence_invoke _ _ hea heu)
  · exact SubexpMainLayoutPrefix.result_of_stages hrf hs hra hru
  · exact workspace_of_stages hrf hra hru hzero

theorem bounded_execution_workspace {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (r Q Δ p k B : ℕ) [NeZero r] [Fact p.Prime]
    (hell : 0 < CounterPrograms.value (Factors.sourceInputs alloc a).counts.ell)
    (hwidth : CounterPrograms.value (Factors.sourceInputs alloc a).counts.ell ≤
      (Factors.sourceInputs alloc a).counts.modulus.length)
    (hp : 0 < BinaryArithmetic.toNat (Factors.sourceInputs alloc a).counts.modulus)
    (G : SubexpLeafData.Leaf (SubexpLayoutConstruction.variableCount (Factors.sourceInputs alloc a)))
    (hG : (G.map ExecCNF.clauseSet).Nodup)
    (hsource : (Factors.sourceInputs alloc a).leaf =
      Encoding.encodeList SubexpClauseRowProgram.clauseBytes G)
    (hD : SubexpLayoutConstruction.dimension (Factors.sourceInputs alloc a) =
      ChunkPartition.count (SubexpLayoutConstruction.variableCount (Factors.sourceInputs alloc a))
        (CounterPrograms.value (Factors.sourceInputs alloc a).counts.ell))
    (hcap : 2 ^ CounterPrograms.value (Factors.sourceInputs alloc a).counts.ell ≤ p)
    (hk : 1 ≤ k) (hw : SAT.WidthAtMost k (ExecCNF.formulaSet G))
    (ho : SAT.OccurrenceAtMost B (ExecCNF.formulaSet G)) (hne : [] ∉ G)
    (hdelta : 1 + CounterPrograms.value (Factors.sourceInputs alloc a).counts.ell * B ≤ Δ)
    (hmeta : ∀ i, CounterPrograms.value
      (a.stacks (persistent es (SubexpMainAssignment.metadataIndex i))) =
      (![r, Q, Δ, SubexpLayoutConstruction.dimension (Factors.sourceInputs alloc a)] : Fin 4 → ℕ) i)
    (hzero : WorkspaceEmpty alloc a) :
    let hv := SubexpLayoutConstruction.family_valid (Factors.sourceInputs alloc a) hp hell hwidth hD
    ∃ hd, ∃ b c, ∃ first : MulticolorTypes.Word r Q, ∃ tail : List (MulticolorTypes.Word r Q),
      ∃ n ≤ SubexpMainLayoutPrefix.runtimeBound alloc a b c hv G hG hell r Q Δ, ∃ d,
      (first :: tail).Nodup ∧ (∀ w, w ∈ first :: tail) ∧
      Eval (SubexpMainLayoutPrefix.procedure er alloc).invoke n a d ∧
      SubexpMainLayoutPrefix.Result alloc a d r Q Δ
        (SubexpLayoutConstruction.dimension (Factors.sourceInputs alloc a))
        (SubexpLayoutScopeOrder.orderedScopes (Factors.sourceInputs alloc a) G hG hell)
        hd first tail (SubexpLayoutConstruction.tables (Factors.sourceInputs alloc a) hv G) ∧
      WorkspaceEmpty alloc d := by
  dsimp only
  have hd (v : Fin (SubexpLayoutConstruction.dimension (Factors.sourceInputs alloc a))) :
      IncidencePlanSpec.degree
        (SubexpLayoutScopeOrder.orderedScopes (Factors.sourceInputs alloc a) G hG hell) v.val ≤ Δ :=
    (SubexpLayoutScopeOrder.degree_le (Factors.sourceInputs alloc a) G hG hell hD
      hcap hk hw ho hne v).trans hdelta
  exact ⟨hd, execution_workspace alloc a r Q Δ hell hwidth
    (SubexpLayoutConstruction.family_valid (Factors.sourceInputs alloc a) hp hell hwidth hD)
    G hG hsource hD hd hmeta hzero⟩

end SubexponentialSAT.SubexpMainLayoutPrefixWorkspace

end OAI.Algorithms
