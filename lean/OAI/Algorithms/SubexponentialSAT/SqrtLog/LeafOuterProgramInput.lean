import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramBoundary

namespace OAI.Algorithms

/-! Exact ordered-clause input semantics and the native trivial dispatch.
No clause order, repeated clause, or unused ambient coordinate is removed. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls

def formulaRecords {n : ℕ} (F : ExecCNF.Formula (SAT.Literal (Fin n))) : List (List Bool) :=
  F.map (Encoding.encodeList ExecSunflowerCodeTransport.literalWord)

def formulaClauses {n : ℕ} (F : ExecCNF.Formula (SAT.Literal (Fin n))) :
    Fin F.length → SAT.Clause (Fin n) :=
  fun i => ExecCNF.clauseSet (F.get i)

theorem formulaRecords_length {n : ℕ} (F : ExecCNF.Formula (SAT.Literal (Fin n))) :
    (formulaRecords F).length=F.length := List.length_map _

theorem formulaRecords_empty_clause {n : ℕ} (F : ExecCNF.Formula (SAT.Literal (Fin n))) :
    [false] ∈ formulaRecords F ↔ [] ∈ F :=
  SubexpEmptyClauseProgram.empty_record_iff _ _

theorem formulaClauses_models {n : ℕ} (F : ExecCNF.Formula (SAT.Literal (Fin n)))
    (x : Fin n → Bool) :
    (∀ i, (formulaClauses F i).eval x=true) ↔ SAT.CNF.eval x (ExecCNF.formulaSet F)=true := by
  rw [SAT.CNF.eval_eq_true]
  constructor
  · intro h C hC
    obtain ⟨D,hD,rfl⟩ := ExecCNF.mem_formulaSet.mp hC
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hD
    exact h i
  · intro h i
    exact h _ (ExecCNF.mem_formulaSet.mpr ⟨F.get i,List.get_mem _ _,rfl⟩)

theorem formulaClauses_satisfiable {n : ℕ} (F : ExecCNF.Formula (SAT.Literal (Fin n))) :
    (∃ x, ∀ i, (formulaClauses F i).eval x=true) ↔ SAT.Satisfiable (ExecCNF.formulaSet F) := by
  exact exists_congr (formulaClauses_models F)

/-- The real classifier handles both exceptional cases; only the nonempty,
empty-clause-free arm needs the main native evaluator. -/
theorem command_of_nontrivial {n : ℕ} (F : ExecCNF.Formula (SAT.Literal (Fin n)))
    (mass acceptedCount : Cmd 40 896) (a : Data) (cost : ℕ)
    (hformula : a.stacks 784=Encoding.encodeList id (formulaRecords F))
    (hready : SubexpEmptyClauseProgram.Ready
      (projectState LeafProgram.Dispatch.registers LeafProgram.Dispatch.stackMap a))
    (hanswer : a.stacks 787=[])
    (hmain : F≠[] → [] ∉ F → ∃ steps b bit,
      Eval (nontrivial mass acceptedCount) steps (classified a (formulaRecords F)) b ∧
      steps ≤ cost ∧ b.stacks 787=[bit] ∧
      (bit=true ↔ SAT.Satisfiable (ExecCNF.formulaSet F))) :
    ∃ steps b bit, Eval (command mass acceptedCount) steps a b ∧
      steps ≤ 100*((a.stacks 784).length+1)+7+cost ∧ b.stacks 787=[bit] ∧
      (bit=true ↔ SAT.Satisfiable (ExecCNF.formulaSet F)) := by
  have hi : LeafProgram.Dispatch.install a
      (projectState LeafProgram.Dispatch.registers LeafProgram.Dispatch.stackMap a)=a :=
    embedState_project _ _ a LeafProgram.Dispatch.registers_injective
      LeafProgram.Dispatch.stackMap_injective
  by_cases he : [] ∈ F
  · obtain ⟨steps,hsteps,hrun⟩ := LeafProgram.Dispatch.empty_clause_run
      (nontrivial mass acceptedCount) a
      (projectState LeafProgram.Dispatch.registers LeafProgram.Dispatch.stackMap a)
      (formulaRecords F) hformula hready ((formulaRecords_empty_clause F).mpr he)
    rw [hi] at hrun
    change steps ≤ 100*((a.stacks 784).length+1)+6 at hsteps
    have hsat : ¬SAT.Satisfiable (ExecCNF.formulaSet F) :=
      SAT.not_satisfiable_of_empty_mem (ExecCNF.mem_formulaSet.mpr ⟨[],he,rfl⟩)
    refine ⟨steps,_,false,hrun,by omega,?_,by simp [hsat]⟩
    change false::(classified a (formulaRecords F)).stacks 787=[false]
    rw [classified_stacks,hanswer]
  · by_cases hf : F=[]
    · subst F
      obtain ⟨steps,hsteps,hrun⟩ := LeafProgram.Dispatch.empty_formula_run
        (nontrivial mass acceptedCount) a
        (projectState LeafProgram.Dispatch.registers LeafProgram.Dispatch.stackMap a)
        hformula hready
      rw [hi] at hrun
      change steps ≤ 100*((a.stacks 784).length+1)+7 at hsteps
      refine ⟨steps,_,true,hrun,by omega,?_,?_⟩
      · change true::(classified a []).stacks 787=[true]
        rw [classified_stacks,hanswer]
      · constructor
        · intro _; exact SAT.satisfiable_empty
        · intro _; rfl
    · obtain ⟨steps,b,bit,hrun,hsteps,hbit,hsat⟩ := hmain hf he
      have hr : formulaRecords F≠[] := by
        intro h
        have hl := congrArg List.length h
        simp only [formulaRecords,List.length_map,List.length_nil] at hl
        exact hf (List.length_eq_zero_iff.mp hl)
      obtain ⟨total,htotal,htrace⟩ := dispatch_nontrivial mass acceptedCount a
        (formulaRecords F) hformula hready
        (fun h => he ((formulaRecords_empty_clause F).mp h)) hr hrun
      exact ⟨total,b,bit,htrace,by omega,hbit,hsat⟩

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
