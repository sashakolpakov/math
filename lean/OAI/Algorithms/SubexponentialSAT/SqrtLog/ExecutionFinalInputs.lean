import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionFinalContract

namespace OAI.Algorithms

/-! A sparse-leaf service theorem can be applied to the actual normalized
splitter leaves without a new syntactic or dimension promise. -/
namespace SubexponentialSAT.SqrtLog.Execution.Final
open SubexponentialSAT BitProgram StructuredCalls SubexpMainProgram Filter
open LeafOuterProgram
open scoped Topology

theorem boot_raw_width {c : SubexponentialSAT.SubexpSetupProgram.Config} {n : ℕ}
    {F : SubexpOrderedRawPrefix.Formula n} (r : FinalBoot c F)
    (G : ExecSparsifyObserved.Formula n) (hG : G ∈ r.leaves) :
    ExecSunflowerSearch.RawWidthAtMost c.k G := by
  intro C hC
  have hm : ExecCNF.clauseSet C ∈ ExecCNF.formulaSet G :=
    ExecCNF.mem_formulaSet.mpr ⟨C,hC,rfl⟩
  have hw := r.outcome.correct.width G hG (ExecCNF.clauseSet C) hm
  simpa only [ExecCNF.clauseSet,List.toFinset_card_of_nodup
    (r.outcome.correct.literal_nodup G hG C hC)] using hw

theorem observedHistoryContract_of_sparse
    (c : SubexponentialSAT.SubexpSetupProgram.Config) (mass acceptedCount : Cmd 40 896)
    (Ct At : ℝ) (dt q : ℕ) (hq : ∀ n, occurrence c n ≤ Asymptotic.L n^q)
    (hservice : ∀ᶠ n : ℕ in atTop,
      ∀ (G : ExecSparsifyObserved.Formula n) B (nw Bw : List Bool),
      ExecSunflowerSearch.RawWidthAtMost c.k G →
      BinaryArithmetic.toNat nw=n → BinaryArithmetic.toNat Bw=B →
      0 < B → B ≤ Asymptotic.L n^q → G.length ≤ n*B →
      G≠[] → [] ∉ G → ∀ a : Data,
      MainAdapter.CoreInput a (inputBits G) nw Bw →
      HistorySupply G B mass acceptedCount a (tailCost Ct At dt n nw Bw (inputBits G))) :
    ObservedHistoryContract c mass acceptedCount Ct At dt := by
  filter_upwards [hservice] with n hn
  intro F _ r G hG a hin hne hno
  exact hn G (occurrence c n) _ _ (boot_raw_width r G hG)
    (boot_ambient r) (boot_occurrence r) (occurrence_pos c n) (hq n)
    (boot_leaf_count r G hG hno) hne hno a hin

end SubexponentialSAT.SqrtLog.Execution.Final

end OAI.Algorithms
