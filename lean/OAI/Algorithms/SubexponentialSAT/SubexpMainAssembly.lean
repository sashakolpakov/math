import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainBoot
import OAI.Algorithms.SubexponentialSAT.SubexpMainController
import OAI.Algorithms.SubexponentialSAT.SubexpLeafContract

namespace OAI.Algorithms

/-!
# Connecting the actual boot and guarded leaf executions

The remaining producer obligation is stated explicitly as `StageProvider`.
This module discharges the record encoding, sparse-leaf validity, Boolean
disjunction, and actual controller wiring. It does not produce the missing
layout/moment/reconstruction executions or a final uniform time bound.
-/

namespace SubexponentialSAT.SubexpMainAssembly

open SubexpMainProgram SubexpSetupProgram

def occurrence (cfg : Config) (n : ℕ) : ℕ :=
  SparsificationConstants.occurrenceCap (DyadicSchedule.M cfg.T n) cfg.k

def validLeaf (cfg : Config) (n : ℕ) (G : SubexpLeafSemantics.Leaf n) : Prop :=
  SubexpLeafSemantics.Sparse cfg.k (occurrence cfg n) G ∧ ExecSparsifyObserved.Ready cfg.k G

variable {cfg : Config} {er n : ℕ} {hr : 32 ≤ workRegs er} {F : SAT.CNF (Fin n)}

theorem valid_leaf (run : SubexpMainBoot.Run cfg hr F)
    (G : SubexpLeafSemantics.Leaf n) (hG : G ∈ run.leaves) : validLeaf cfg n G := by
  have hc := run.outcome.correct.clause_nodup G hG
  have hl := run.outcome.correct.literal_nodup G hG
  have hw := run.outcome.correct.width G hG
  refine ⟨⟨hc, hw, run.outcome.correct.occurrence G hG⟩, hc, hl, ?_⟩
  intro C hC
  have hwidth := hw (ExecCNF.clauseSet C) (ExecCNF.mem_formulaSet.mpr ⟨C, hC, rfl⟩)
  simpa only [ExecCNF.clauseSet, List.toFinset_card_of_nodup (hl C hC)] using hwidth

theorem records_eq (run : SubexpMainBoot.Run cfg hr F) :
    run.records = run.leaves.map ExecQuantitativeSparsify.encodeRawFormula := by
  apply List.map_congr_left
  intro G _
  exact ExecSparsifyEncoding.words_encodeRawFormula G

theorem valid_records (run : SubexpMainBoot.Run cfg hr F) :
    ∀ bits ∈ run.records, SubexpLeafSemantics.validPayload n (validLeaf cfg n) bits := by
  intro bits hb
  rw [records_eq] at hb
  obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hb
  exact ⟨G, valid_leaf run G hG, rfl⟩

theorem correct (run : SubexpMainBoot.Run cfg hr F) :
    run.records.any (SubexpLeafSemantics.test n) = true ↔ SAT.Satisfiable F := by
  rw [records_eq]
  exact (SubexpLeafContract.records_any_test run.leaves).trans run.satisfiable.symm

def leafCost (er count n ell p : ℕ) (prefixLimit : List Bool → ℕ) (bits : List Bool) : ℕ :=
  SubexpLeafContract.leafBound er count (SubexpLeafContract.wordWidth n ell p)
    (prefixLimit bits) bits + 200 * (bits.length + 1)

/-- Actual controller execution, conditional on the still-explicit concrete
leaf-stage provider and its invariant. The boot and record semantics are
already provided by their checked programs; the reference Boolean is never
inserted as a machine instruction. -/
noncomputable def execution (run : SubexpMainBoot.Run cfg hr F)
    (phases : Phases er (mainExtraStacks cfg))
    (hsetup : phases.setup = mainProcedure cfg er)
    (hsparsify : phases.sparsify = SubexpActualSparsify.procedure cfg hr)
    (count : ℕ) (hcount : count ≤ workStacks (mainExtraStacks cfg)) (hguard : 9 ≤ count)
    (hdecode : phases.decode = SubexpMainReady.procedure er (mainExtraStacks cfg) count hcount)
    {ell p Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
    (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (hn : 0 < n)
    (invariant : MainState er (mainExtraStacks cfg) → Prop) (prefixLimit : List Bool → ℕ)
    (initial : invariant run.afterSparsify)
    (ready : ∀ base, invariant base → SubexpMainReady.StorageReady count base ∧
      base.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 9) = [] ∧
      base.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 10) = [])
    (provider : SubexpLeafContract.StageProvider (k := cfg.k) (Δ := Δ) (r := r) (tau := tau)
      phases count hcount hell hcap (validLeaf cfg n) invariant prefixLimit) :
    SubexpMainController.Execution phases (SubexpEmptyClauseGuard.leafCallback phases) F where
  afterPrefix := run.before
  prefixSteps := run.prefixSteps
  prefixTrace := run.prefixTrace
  boot := run.boot phases hsetup hsparsify
  records := run.records
  test := SubexpLeafSemantics.test n
  cost := leafCost er count n ell p prefixLimit
  invariant := invariant
  validPayload := SubexpLeafSemantics.validPayload n (validLeaf cfg n)
  callback := SubexpLeafContract.guarded_callback_contract phases count hcount hguard hdecode
    hell hcap hn (validLeaf cfg n) invariant prefixLimit ready provider
  validRecords := valid_records run
  valid := initial
  source := run.source
  payload := run.persistent_empty 8 (by decide) (by decide)
  correct := correct run

end SubexponentialSAT.SubexpMainAssembly

end OAI.Algorithms
