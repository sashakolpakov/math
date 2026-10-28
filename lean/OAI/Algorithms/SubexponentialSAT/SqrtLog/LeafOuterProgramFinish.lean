import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramBoundary
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramInitial

namespace OAI.Algorithms

/-! The final native scan turns the physically computed accepted-model count
into exactly the SAT bit. Its incoming numerical equality is supplied by the
native unmarked count service, not used as a machine instruction. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem finish_eval {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (rows : List (Fin m → ZMod 3)) (a : Data) (hempty : a.stacks 787=[])
    (hcount : BinaryArithmetic.toNat (a.stacks 788)=HashSelect.acceptedCount (HashSelect.cnfRowAccept clauses) rows)
    (hmodels : ∀ x, HashSelect.accepts (HashSelect.cnfRowAccept clauses) rows x=true ↔
      ∀ e, (clauses e).eval x=true) :
    ∃ steps b bit, Eval decideCount steps a b ∧
      steps ≤ 5*(a.stacks 788).length+11 ∧ b.stacks 787=[bit] ∧ b.stacks 788=[] ∧
      (bit=true ↔ ∃ x, ∀ e, (clauses e).eval x=true) ∧
      (∀ i, i≠787 → i≠788 → b.stacks i=a.stacks i) := by
  obtain ⟨steps,b,he,hn,hbit,hclear,hframe⟩ := decideCount_eval a hempty
  refine ⟨steps,b,PositiveWordProgram.positive (a.stacks 788),he,hn,hbit,hclear,?_,hframe⟩
  rw [LeafProgram.Decision.answer_iff _ _ hcount,HashSelect.acceptedCount_pos_iff]
  exact exists_congr hmodels

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
