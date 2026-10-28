import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramHistoryCore

namespace OAI.Algorithms

/-! The large-input core theorem only charges sparse nontrivial leaves.
Empty clauses and empty formulas are handled by the existing real classifier. -/
namespace SubexponentialSAT.SqrtLog.Execution.Final
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage Filter
open scoped Topology
open LeafOuterProgram

theorem historySupply_mono {n : ℕ} {F : ExecCNF.Formula (SAT.Literal (Fin n))} {B : ℕ}
    {mass acceptedCount : Cmd 40 896} {a : Data} {s t : ℕ}
    (h : HistorySupply F B mass acceptedCount a s) (hst : s ≤ t) :
    HistorySupply F B mass acceptedCount a t := by
  intro ni p shifts Q he hp hs hQ hr hf
  obtain ⟨svc,hsvc⟩ := h ni p shifts Q he hp hs hQ hr hf
  exact ⟨svc,hsvc.trans hst⟩

theorem eventually_command_nontrivial_sparse :
    ∃ C d p : ℕ, ∀ q : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ (F : ExecCNF.Formula (SAT.Literal (Fin n))) B (nw Bw : List Bool)
        (mass acceptedCount : Cmd 40 896) (a : Data) tailLimit,
      MainAdapter.CoreInput a (inputBits F) nw Bw →
      BinaryArithmetic.toNat nw=n → BinaryArithmetic.toNat Bw=B →
      0 < B → ([] ∉ F → F.length ≤ n*B) → B ≤ Asymptotic.L n^q →
      (F≠[] → [] ∉ F → HistorySupply F B mass acceptedCount a tailLimit) →
      ∃ steps b bit, Eval (command mass acceptedCount) steps a b ∧
      steps ≤ 100*((a.stacks 784).length+1)+7+
        CodeSetupOuterCost.setupMajorant C d q n*
          ((inputBits F).length+nw.length+Bw.length+2)^p+tailLimit ∧
      b.stacks 787=[bit] ∧ (bit=true ↔ SAT.Satisfiable (ExecCNF.formulaSet F)) := by
  obtain ⟨C,d,p,hmain⟩ := eventually_command_history_eval
  refine ⟨C,d,p,?_⟩
  intro q
  filter_upwards [hmain q] with n hn
  intro F B nw Bw mass acceptedCount a tailLimit hin hnv hBv hB hm hBq hsupply
  by_cases he : [] ∈ F ∨ F=[]
  · have hf : a.stacks 784=Encoding.encodeList id (formulaRecords F) := by
      simp only [hin 784]; rfl
    have ha : a.stacks 787=[] := by simp only [hin 787]; rfl
    obtain ⟨steps,b,bit,ht,hcost,hbit,hsat⟩ := command_of_nontrivial F mass acceptedCount a
      (CodeSetupOuterCost.setupMajorant C d q n*((inputBits F).length+nw.length+Bw.length+2)^p+tailLimit)
      hf (coreInput_classifier hin) ha (by
        intro hne hno
        exact False.elim (he.elim hno hne))
    exact ⟨steps,b,bit,ht,by omega,hbit,hsat⟩
  · have hno : [] ∉ F := fun hh => he (Or.inl hh)
    have hne : F≠[] := fun hh => he (Or.inr hh)
    exact hn F B nw Bw mass acceptedCount a tailLimit hin hnv hBv hB (hm hno) hBq
      (hsupply hne hno)

theorem eventually_core_nontrivial_sparse :
    ∃ C d p : ℕ, ∀ q : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ B (nw Bw : List Bool) (mass acceptedCount : Cmd 40 896)
        (admissible : ExecCNF.Formula (SAT.Literal (Fin n)) → Prop)
        (tailCost : List Bool → ℕ),
      BinaryArithmetic.toNat nw=n → BinaryArithmetic.toNat Bw=B →
      0 < B → B ≤ Asymptotic.L n^q →
      (∀ F, admissible F → [] ∉ F → F.length ≤ n*B) →
      (∀ F, admissible F → ∀ a,
        MainAdapter.CoreInput a (inputBits F) nw Bw →
        (F≠[] → [] ∉ F → HistorySupply F B mass acceptedCount a (tailCost (inputBits F)))) →
      MainAdapter.CoreContract (command mass acceptedCount) (inputTest n)
        (coreLimit (CodeSetupOuterCost.setupMajorant C d q n) p nw Bw tailCost)
        (validInput admissible) nw Bw := by
  obtain ⟨C,d,p,hcomplete⟩ := eventually_command_nontrivial_sparse
  refine ⟨C,d,p,?_⟩
  intro q
  filter_upwards [hcomplete q] with n hn
  intro B nw Bw mass acceptedCount admissible tailCost hnw hBw hB hBq hm hsupply bits hvalid a hin
  obtain ⟨F,hF,rfl⟩ := hvalid
  obtain ⟨steps,b,bit,he,hsteps,hbit,hsat⟩ :=
    hn F B nw Bw mass acceptedCount a (tailCost (inputBits F)) hin hnw hBw hB
      (hm F hF) hBq (hsupply F hF a hin)
  have hformula : a.stacks 784=inputBits F := by simp only [hin 784]; rfl
  have hanswer : bit=inputTest n (inputBits F) := by
    have htest := inputTest_spec F
    have heq : (bit=true) ↔ (inputTest n (inputBits F)=true) := hsat.trans htest.symm
    cases bit <;> cases hh : inputTest n (inputBits F)
    · rfl
    · have hbad : (false : Bool)=true := heq.mpr hh
      cases hbad
    · have hbad : (false : Bool)=true := hh ▸ heq.mp rfl
      cases hbad
    · rfl
  refine ⟨steps,?_,b,he,?_⟩
  · simpa only [hformula,coreLimit,inputBits] using hsteps
  · simpa only [hanswer] using hbit


end SubexponentialSAT.SqrtLog.Execution.Final

end OAI.Algorithms
