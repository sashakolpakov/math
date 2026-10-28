import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramCost
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramControllerPreprocess
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramPreprocessBounds

namespace OAI.Algorithms

/-! Input-only budget for the actual signed-row preprocessing plus complete
bucket machine. No precomputed unsigned matrix is a premise. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram
open SubexponentialSAT.BitProgram

theorem shiftedMatrix_entries_bound {W : List Bool} {xs : List (List SignedWord)}
    {ys : List (List (List Bool))}
    (hy : List.Forall₂ (List.Forall₂ (shiftedWord W)) xs ys)
    (L : ℕ) (hW : W.length ≤ L) (hb : ∀ row∈xs,preWordsBounded L row) :
    ∀ row∈ys,∀ word∈row,word.length ≤ 3*L+1 := by
  induction hy with
  | nil => simp
  | @cons row out rows outs hrow htail ih =>
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact shiftedWords_length_bound hrow L hW (hb row (by simp))
      · exact ih (fun r hr => hb r (by simp [hr])) z hz

theorem shiftedMatrix_integer {W : List Bool} {xs : List (List SignedWord)}
    {ys : List (List (List Bool))}
    (hy : List.Forall₂ (List.Forall₂ (shiftedWord W)) xs ys)
    (hb : ∀ row∈xs,∀ a∈row,SubexponentialSAT.BinaryArithmetic.toNat a.2 ≤ SubexponentialSAT.BinaryArithmetic.toNat W) :
    List.Forall₂ (List.Forall₂ (fun a y => (SubexponentialSAT.BinaryArithmetic.toNat y : ℤ)=
      (SubexponentialSAT.BinaryArithmetic.toNat W : ℤ)+
        ((SubexponentialSAT.BinaryArithmetic.toNat a.1 : ℤ)-(SubexponentialSAT.BinaryArithmetic.toNat a.2 : ℤ)))) xs ys := by
  induction hy with
  | nil => exact .nil
  | @cons row out rows outs hrow htail ih =>
      exact .cons (shiftedWords_integer hrow (hb row (by simp)))
        (ih (fun r hr => hb r (by simp [hr])))

namespace Cost

def signedTotal (W : List Bool) (h m L n : ℕ) : ℕ :=
  10000*(m+1)*(h+1)*(L+1)^2 + total W h m (3*L+1) n + 1

theorem signedProgram_runsIn (regs : Fin 10 → Bool) (W : List Bool)
    (rows : List (List SignedWord)) (js : List ℕ) (n h L : ℕ)
    (hW : W.length ≤ L) (hrows : ∀ row∈rows,row.length=h)
    (hb : ∀ row∈rows,preWordsBounded L row) (hlen : js.length=h) (hjs : ∀ j∈js,j < n) :
    ∃ rf ys, List.Forall₂ (List.Forall₂ (shiftedWord W)) rows ys ∧
      RunsIn Controller.signedProgram (signedTotal W h rows.length L n)
        ((Controller.signedInitial regs W rows js n h).withPC (some Controller.signedProgram.entry))
        ((Controller.signedFinal rf W ys js n h).withPC none) := by
  obtain ⟨rf,ys,hy,t,ht,he⟩ := Controller.signedProgram_runsIn regs W rows js n h hrows hlen hjs
  have hpre := preMatrixCost_polynomial W rows L h hW
    (fun row hr => ⟨hb row hr,(hrows row hr).le⟩)
  have hout := shiftedMatrix_entries_bound hy L hW hb
  have hw := shiftedMatrix_rowWidth hy h hrows
  have hc := controller_cost_bound W ys js n h (3*L+1) hw hout hlen hjs
  have hl : rows.length=ys.length := hy.length_eq
  rw [←hl] at hc
  exact ⟨rf,ys,hy,t,by unfold signedTotal; omega,he⟩

theorem signedProgram_primitive (regs : Fin 10 → Bool) (W : List Bool)
    (rows : List (List SignedWord)) (js : List ℕ) (n h L : ℕ)
    (hW : W.length ≤ L) (hrows : ∀ row∈rows,row.length=h)
    (hb : ∀ row∈rows,preWordsBounded L row) (hlen : js.length=h) (hjs : ∀ j∈js,j < n) :
    ∃ rf ys, List.Forall₂ (List.Forall₂ (shiftedWord W)) rows ys ∧
      SubexponentialSAT.Computation.RunsIn (primitive Controller.signedProgram).step
        (primitiveOverhead Controller.signedProgram*signedTotal W h rows.length L n)
        (primitiveCfg Controller.signedProgram
          ((Controller.signedInitial regs W rows js n h).withPC (some Controller.signedProgram.entry)))
        (primitiveCfg Controller.signedProgram
          ((Controller.signedFinal rf W ys js n h).withPC none)) := by
  obtain ⟨rf,ys,hy,he⟩ := signedProgram_runsIn regs W rows js n h L hW hrows hb hlen hjs
  exact ⟨rf,ys,hy,primitive_execution Controller.signedProgram he⟩

end Cost
end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
