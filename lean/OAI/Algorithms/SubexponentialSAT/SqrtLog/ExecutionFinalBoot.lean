import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionBoot
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramObserved
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparsifyBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.AsymptoticResidual

namespace OAI.Algorithms

/-! Data and size facts about the actual emitted splitter stream. -/
namespace SubexponentialSAT.SqrtLog.Execution.Final
open SubexponentialSAT BitProgram StructuredCalls SubexpMainProgram
open LeafOuterProgram
open scoped BigOperators

def occurrence (c : SubexponentialSAT.SubexpSetupProgram.Config) (n : ℕ) :=
  SparsifyDyadic.occurrenceBound c.k c.T (Asymptotic.s n)

theorem occurrence_pos (c : SubexponentialSAT.SubexpSetupProgram.Config) (n : ℕ) : 0 < occurrence c n := by
  have h1 : 1 ∈ Finset.range (c.k+1) := Finset.mem_range.mpr (by have:=c.width_ge_two; omega)
  have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.range (c.k+1)) =>
    Nat.zero_le (SparsificationConstants.L (SparsificationBudgetProgram.dyadicM c.T (Asymptotic.s n)) j)) h1
  change 0 < 2*∑ j ∈ Finset.range (c.k+1),
    SparsificationConstants.L (SparsificationBudgetProgram.dyadicM c.T (Asymptotic.s n)) j
  simp only [SparsificationConstants.L_one] at hh
  omega

theorem occurrence_power (c : SubexponentialSAT.SubexpSetupProgram.Config) : ∃ q : ℕ, ∀ n, occurrence c n ≤ Asymptotic.L n^q := by
  obtain ⟨q,hq⟩ := SparsifyBounds.occurrence_le_log_power c.k c.T
  refine ⟨2*q,?_⟩
  intro n
  have hL := Asymptotic.L_pos n
  have hL2 : 2 ≤ Asymptotic.L n := by
    have hreal : (4 : ℝ) < Asymptotic.L n :=
      (Asymptotic.four_le_logSize n).trans_lt (Asymptotic.logSize_lt_L n)
    have hnat : 4 < Asymptotic.L n := by exact_mod_cast hreal
    omega
  have hb : Asymptotic.L n+2 ≤ Asymptotic.L n^2 := by nlinarith
  exact (hq n).trans ((Nat.pow_le_pow_left hb q).trans_eq (by rw [←pow_mul]))

theorem boot_ambient {c : SubexponentialSAT.SubexpSetupProgram.Config} {er n : ℕ} {hr : 32 ≤ workRegs er}
    {F : SubexpOrderedRawPrefix.Formula n} (r : Boot c er hr F) :
    BinaryArithmetic.toNat (r.final.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 2))=n := by
  rw [r.outcome.persistent_frame 2 (by decide) (by decide),SetupRun.afterSetup,
    r.startup.frame 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact r.startup.facts.variableCount

theorem boot_occurrence {c : SubexponentialSAT.SubexpSetupProgram.Config} {er n : ℕ} {hr : 32 ≤ workRegs er}
    {F : SubexpOrderedRawPrefix.Formula n} (r : Boot c er hr F) :
    BinaryArithmetic.toNat (r.final.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 24))=occurrence c n := by
  rw [r.outcome.persistent_frame 24 (by decide) (by decide)]
  change BinaryArithmetic.toNat
    (((Setup.Complete.procedure c er).install r.startup.before r.startup.out).stacks
      (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 24))=occurrence c n
  rw [←SubexpSetupProgram.mainStack_persistent c 24]
  rw [show (((Setup.Complete.procedure c er).install r.startup.before r.startup.out).stacks
      (SubexpSetupProgram.mainStack c (SubexpSetupProgram.persistent c 24)))=
      r.startup.out.stacks (SubexpSetupProgram.persistent c 24) from
    embedState_stack (Setup.Complete.procedure c er).registerMap
      (Setup.Complete.procedure c er).stack r.startup.before r.startup.out
      (Setup.Complete.procedure c er).stack.injective (SubexpSetupProgram.persistent c 24)]
  exact r.startup.values.banks.occurrence

theorem boot_leaf_count {c : SubexponentialSAT.SubexpSetupProgram.Config} {er n : ℕ} {hr : 32 ≤ workRegs er}
    {F : SubexpOrderedRawPrefix.Formula n} (r : Boot c er hr F)
    (G : ExecSparsifyObserved.Formula n) (hG : G ∈ r.leaves) (he : [] ∉ G) :
    G.length ≤ n*occurrence c n := by
  have hc : (ExecCNF.formulaSet G).card=G.length := by
    change (G.map ExecCNF.clauseSet).toFinset.card=G.length
    rw [List.toFinset_card_of_nodup (r.outcome.correct.clause_nodup G hG),List.length_map]
  rw [←hc]
  apply Sparsify.clause_count_le_of_occurrence _ _ (r.outcome.correct.occurrence G hG)
  intro hempty
  obtain ⟨C,hC,hzero⟩ := ExecCNF.mem_formulaSet.mp hempty
  apply he
  have hz : C=[] := by
    have hcard := congrArg Finset.card hzero
    apply List.length_eq_zero_iff.mp
    simpa only [ExecCNF.clauseSet,List.toFinset_card_of_nodup
      (r.outcome.correct.literal_nodup G hG C hC),Finset.card_empty] using hcard
  exact hz ▸ hC

theorem boot_wordBound {c : SubexponentialSAT.SubexpSetupProgram.Config} {er n : ℕ} {hr : 32 ≤ workRegs er}
    {F : SubexpOrderedRawPrefix.Formula n} (r : Boot c er hr F) :
    SubexponentialSAT.SubexpSetupStorage.WordBound (SubexpOrderedRawPrefix.bitLength F+r.startup.prefixSteps+
      r.startup.setupSteps+r.steps) r.final := by
  have h0 := SubexpSetupMainRuntime.initial_wordBound er (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c)
    (SubexpOrderedRawPrefix.encode F)
  have h1 := SubexpSetupBoundSpec.eval_wordBound h0 r.startup.prefixTrace
  have h2 := SubexpSetupBoundSpec.eval_wordBound h1 r.startup.setupTrace
  exact SubexpSetupBoundSpec.eval_wordBound h2 r.trace

private theorem record_length_le (records : List (List Bool)) (bits : List Bool)
    (h : bits ∈ records) : bits.length ≤ (Encoding.encodeList id records).length := by
  induction records with
  | nil => cases h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp only [Encoding.encodeList,List.length_cons,List.length_append,Encoding.length_frame,id_eq]
      omega
    · have hh := ih h
      simp only [Encoding.encodeList,List.length_cons,List.length_append]
      omega

theorem boot_payload_bound {c : SubexponentialSAT.SubexpSetupProgram.Config} {er n : ℕ} {hr : 32 ≤ workRegs er}
    {F : SubexpOrderedRawPrefix.Formula n} (r : Boot c er hr F) (bits : List Bool)
    (h : bits ∈ r.records) : bits.length ≤ SubexpOrderedRawPrefix.bitLength F+
      r.startup.prefixSteps+r.startup.setupSteps+r.steps := by
  have hb := boot_wordBound r (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 7)
  rw [r.source] at hb
  exact (record_length_le r.records bits h).trans hb

theorem observed_body_le_input {n : ℕ} (F : SubexpOrderedRawPrefix.Formula n) :
    (ExecSparsifyObserved.encode F).length ≤ SubexpOrderedRawPrefix.bitLength F := by
  change (SubexpOrderedRawPrefix.body F).length ≤
    (Encoding.encodeNat n ++ SubexpOrderedRawPrefix.body F).length
  simp only [List.length_append]
  omega

end SubexponentialSAT.SqrtLog.Execution.Final

end OAI.Algorithms
