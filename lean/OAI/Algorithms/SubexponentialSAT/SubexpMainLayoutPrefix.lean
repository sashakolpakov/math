import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayout
import OAI.Algorithms.SubexponentialSAT.SubexpMainAssignment
import OAI.Algorithms.SubexponentialSAT.SubexpMainUniversalTypes
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutScopeOrder
import OAI.Algorithms.SubexponentialSAT.SubexpProcedureCompose

namespace OAI.Algorithms

/-!
# The concrete factor, assignment, and universal-type prefix

The three fixed programs run in sequence on the same physical Main state.
The scope stream used by assignment is derived from the bytes produced by
the factor program. Its incidence bound is obtained from the typed leaf.
The generated assignment order, rather than a separately chosen order, is
retained in the conclusion. Later layout stages extend this prefix.
-/

namespace SubexponentialSAT.SubexpMainLayoutPrefix

open BitProgram StructuredCalls SubexpMainProgram SubexpMainLayout Subexp
open SubexpLayoutPorts (Allocation master ordinary)

attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The factor program only reads its five persistent inputs. All other
persistent words are outside its actual stack map. -/
theorem factors_persistent_frame {er es : ℕ} {alloc : Allocation es}
    {a b : MainState er es} {scopes tables : List (List Bool)}
    (h : Factors.Result alloc a b scopes tables) (i : Fin 32) :
    b.stacks (persistent es i) = a.stacks (persistent es i) := by
  classical
  have hh (j : Fin 7) (hj : Factors.highPort alloc j = persistent es i) :
      b.stacks (persistent es i) = a.stacks (persistent es i) := by
    fin_cases j
    · have hi : (2 : Fin 32) = i := persistent_injective es hj
      subst i
      exact h.inputs 0
    · have hi : (5 : Fin 32) = i := persistent_injective es hj
      subst i
      exact h.inputs 1
    · have hi : (6 : Fin 32) = i := persistent_injective es hj
      subst i
      exact h.inputs 2
    · have hi : (19 : Fin 32) = i := persistent_injective es hj
      subst i
      exact h.inputs 3
    · have hi : (9 : Fin 32) = i := persistent_injective es hj
      subst i
      exact h.inputs 4
    · exact False.elim (SubexpLayoutPorts.master_ne_persistent alloc 0 i hj)
    · exact False.elim (SubexpLayoutPorts.master_ne_persistent alloc 1 i hj)
  by_cases hi : ∃ j, Factors.stackMap alloc j = persistent es i
  · obtain ⟨j, hj⟩ := hi
    by_cases hm : 35 ≤ (Factors.permutation j).val ∧ (Factors.permutation j).val < 42
    · apply hh ⟨(Factors.permutation j).val - 35, by omega⟩
      simpa only [Factors.stackMap, Factors.baseMap, dite_eq_left hm] using hj
    · have hv := congrArg (fun z : Fin (totalStacks es) => z.val) hj
      have hb := alloc.enough.trans alloc.within
      have hjlt := (Factors.permutation j).isLt
      simp only [Factors.stackMap, Factors.baseMap, dite_eq_right hm,
        SubexpLayoutPorts.ordinary, persistent, Fin.val_natAdd] at hv
      omega
  · exact h.frame _ hi

noncomputable def procedure (er : ℕ) {es : ℕ} (alloc : Allocation es) : Procedure er es :=
  SubexpProcedureCompose.sequence (Factors.procedure er alloc)
    (SubexpProcedureCompose.sequence (SubexpMainAssignment.procedure er alloc)
      (SubexpMainUniversalTypes.procedure er alloc))

noncomputable def program (er : ℕ) {es : ℕ} (alloc : Allocation es) :=
  ProgramLinking.liftProgram (procedure er alloc).program
    (procedure er alloc).registerMap (procedure er alloc).stack

/-- Final bytes of this concrete prefix. The proof-only `first` and `tail`
name the alphabet order actually used by the assignment program. -/
structure Result {er es : ℕ} (alloc : Allocation es) (a d : MainState er es)
    (r Q Δ D : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (first : MulticolorTypes.Word r Q) (tail : List (MulticolorTypes.Word r Q))
    (tables : List (List Bool)) : Prop where
  wordOrder : (first :: tail).map ReadPlan.encodeWord = AssignmentAlphabetSemantics.wordBytes r Q
  scopeBytes : d.stacks (master alloc 0) = SubexpPlanAlphabetBase.scopeBytes scopes
  tableBytes : d.stacks (master alloc 1) = Encoding.encodeList id tables
  assignment : d.stacks (master alloc 2) =
    SubexpAssignmentStaging.assignedBytes Δ D scopes hd first tail
  alphabet : d.stacks (master alloc 3) =
    ProgramEncoding.encodeRecords (AssignmentAlphabetSemantics.wordBytes r Q)
  width : (d.stacks (master alloc 4)).length = Q * r
  headers : ∀ i, d.stacks (master alloc (SubexpMainAssignment.headerIndex i)) =
    List.replicate ((![r, Q, Δ, D] : Fin 4 → ℕ) i) true
  universal : d.stacks (master alloc 10) =
    ProgramEncoding.encodeRecords (TypeEnumeration.universalBytes r Q Δ)
  persistent : ∀ i, d.stacks (SubexpMainProgram.persistent es i) =
    a.stacks (SubexpMainProgram.persistent es i)
  controls : ∀ i, d.regs (controlRegister er i) = a.regs (controlRegister er i)

theorem result_of_stages {er es : ℕ} {alloc : Allocation es}
    {a b c d : MainState er es} {r Q Δ D : ℕ} {scopes : List (List ℕ)}
    {hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ}
    {first : MulticolorTypes.Word r Q} {tail : List (MulticolorTypes.Word r Q)}
    {scopeRecords tables : List (List Bool)}
    (hf : Factors.Result alloc a b scopeRecords tables)
    (hs : b.stacks (master alloc 0) = SubexpPlanAlphabetBase.scopeBytes scopes)
    (ha : SubexpMainAssignment.Result alloc b c r Q Δ D scopes hd first tail)
    (hu : SubexpMainUniversalTypes.Result alloc c d r Q Δ) :
    Result alloc a d r Q Δ D scopes hd first tail tables := by
  refine ⟨ha.wordOrder, ?_, ?_, ?_, ?_, ?_, ?_, hu.output, ?_, ?_⟩
  · exact (hu.master_frame 0 (by decide)).trans ((ha.inputs 4).trans hs)
  · exact (hu.master_frame 1 (by decide)).trans
      ((ha.master_frame 1 (by decide)).trans hf.tables)
  · exact (hu.master_frame 2 (by decide)).trans ha.assignment
  · exact hu.alphabet.trans ha.alphabet
  · rw [hu.master_frame 4 (by decide)]
    exact ha.width
  · intro i
    rw [hu.master_frame (SubexpMainAssignment.headerIndex i) (by
      intro he
      have hv := congrArg (fun j : Fin 32 => j.val) he
      simp only [SubexpMainAssignment.headerIndex, Fin.val_mk, Fin.coe_ofNat_eq_mod] at hv
      omega)]
    exact ha.headers i
  · intro i
    exact (hu.persistent_frame i).trans
      ((ha.persistent_frame i).trans (factors_persistent_frame hf i))
  · intro i
    exact (hu.controls i).trans ((ha.controls i).trans (hf.controls i))

noncomputable def runtimeBound {er es : ℕ} (alloc : Allocation es) (a b c : MainState er es)
    (hv : SubexpClauseFamilyProgram.Valid
      (SubexpLayoutConstruction.familyInputs (Factors.sourceInputs alloc a))
      (SubexpLayoutConstruction.dimension (Factors.sourceInputs alloc a))
      (SubexpLayoutConstruction.variableCount (Factors.sourceInputs alloc a)))
    (G : SubexpLeafData.Leaf (SubexpLayoutConstruction.variableCount (Factors.sourceInputs alloc a)))
    (hG : (G.map ExecCNF.clauseSet).Nodup)
    (hell : 0 < CounterPrograms.value (Factors.sourceInputs alloc a).counts.ell)
    (r Q Δ : ℕ) : ℕ :=
  Factors.runtimeBound alloc a hv G +
    SubexpMainAssignment.runtimeBound alloc b r Q Δ
      (SubexpLayoutConstruction.dimension (Factors.sourceInputs alloc a))
      (SubexpLayoutScopeOrder.orderedScopes (Factors.sourceInputs alloc a) G hG hell) +
    SubexpMainUniversalTypes.runtimeBound alloc c r Q Δ + 2

/-- Measured execution of all three concrete programs. The intermediate
states in the cost are their actual successive outputs. -/
theorem execution {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
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
      (![r, Q, Δ, SubexpLayoutConstruction.dimension (Factors.sourceInputs alloc a)] : Fin 4 → ℕ) i) :
    ∃ b c, ∃ first : MulticolorTypes.Word r Q, ∃ tail : List (MulticolorTypes.Word r Q),
      ∃ n ≤ runtimeBound alloc a b c hv G hG hell r Q Δ, ∃ d,
      (first :: tail).Nodup ∧ (∀ w, w ∈ first :: tail) ∧
      Eval (procedure er alloc).invoke n a d ∧
      Result alloc a d r Q Δ (SubexpLayoutConstruction.dimension (Factors.sourceInputs alloc a))
        (SubexpLayoutScopeOrder.orderedScopes (Factors.sourceInputs alloc a) G hG hell)
        hd first tail (SubexpLayoutConstruction.tables (Factors.sourceInputs alloc a) hv G) := by
  obtain ⟨nf, hnf, b, hef, hrf⟩ := Factors.execution alloc a hell hwidth hv G hsource
  have hs : b.stacks (master alloc 0) = SubexpPlanAlphabetBase.scopeBytes
      (SubexpLayoutScopeOrder.orderedScopes (Factors.sourceInputs alloc a) G hG hell) :=
    hrf.scopes.trans (SubexpLayoutScopeOrder.scope_stream_eq _ hv G hG hell hD)
  have hm (i : Fin 4) : CounterPrograms.value
      (b.stacks (persistent es (SubexpMainAssignment.metadataIndex i))) =
      (![r, Q, Δ, SubexpLayoutConstruction.dimension (Factors.sourceInputs alloc a)] : Fin 4 → ℕ) i := by
    rw [factors_persistent_frame hrf]
    exact hmeta i
  obtain ⟨first, tail, na, hna, c, hn, hf, hea, hra⟩ :=
    SubexpMainAssignment.execution alloc b r Q Δ
      (SubexpLayoutConstruction.dimension (Factors.sourceInputs alloc a))
      (SubexpLayoutScopeOrder.orderedScopes (Factors.sourceInputs alloc a) G hG hell) hd hm hs
  have hdelta : c.stacks (master alloc 7) = List.replicate Δ true := hra.headers 2
  obtain ⟨nu, hnu, d, heu, hru⟩ :=
    SubexpMainUniversalTypes.execution alloc c r Q Δ hra.alphabet hdelta
  refine ⟨b, c, first, tail, nf + (na + nu + 1) + 1, ?_, d, hn, hf, ?_, ?_⟩
  · unfold runtimeBound
    omega
  · exact SubexpProcedureCompose.sequence_invoke _ _ hef
      (SubexpProcedureCompose.sequence_invoke _ _ hea heu)
  · exact result_of_stages hrf hs hra hru

/-- The degree premise of `execution` follows from the bounded typed leaf.
The family-validity premise follows from its actual scalar words. -/
theorem bounded_execution {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
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
      (![r, Q, Δ, SubexpLayoutConstruction.dimension (Factors.sourceInputs alloc a)] : Fin 4 → ℕ) i) :
    let hv := SubexpLayoutConstruction.family_valid (Factors.sourceInputs alloc a) hp hell hwidth hD
    ∃ hd, ∃ b c, ∃ first : MulticolorTypes.Word r Q, ∃ tail : List (MulticolorTypes.Word r Q),
      ∃ n ≤ runtimeBound alloc a b c hv G hG hell r Q Δ, ∃ d,
      (first :: tail).Nodup ∧ (∀ w, w ∈ first :: tail) ∧
      Eval (procedure er alloc).invoke n a d ∧
      Result alloc a d r Q Δ (SubexpLayoutConstruction.dimension (Factors.sourceInputs alloc a))
        (SubexpLayoutScopeOrder.orderedScopes (Factors.sourceInputs alloc a) G hG hell)
        hd first tail (SubexpLayoutConstruction.tables (Factors.sourceInputs alloc a) hv G) := by
  dsimp only
  have hd (v : Fin (SubexpLayoutConstruction.dimension (Factors.sourceInputs alloc a))) :
      IncidencePlanSpec.degree
        (SubexpLayoutScopeOrder.orderedScopes (Factors.sourceInputs alloc a) G hG hell) v.val ≤ Δ :=
    (SubexpLayoutScopeOrder.degree_le (Factors.sourceInputs alloc a) G hG hell hD
      hcap hk hw ho hne v).trans hdelta
  exact ⟨hd, execution alloc a r Q Δ hell hwidth
    (SubexpLayoutConstruction.family_valid (Factors.sourceInputs alloc a) hp hell hwidth hD)
    G hG hsource hD hd hmeta⟩

end SubexponentialSAT.SubexpMainLayoutPrefix

end OAI.Algorithms
