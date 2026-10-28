import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramArrayStage
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramCleanup
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramPreparedTable

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls SubexpQuarticRing
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

abbrev finishCommand : Cmd 8 41 := .seq nativeTable (.seq arrayStage preparationCleanup)

def finishedStacks (s : Fin 41 → List Bool) (t : ℕ) (table : List Bool) : Fin 41 → List Bool :=
  fun i => if i ∈ preparationDiscard then [] else (arrayStacks (Function.update s 22 table) t) i

def finishBudget (t B W : ℕ) : ℕ :=
  Scan.tableBudget (3*t) (200*(3*t+B+1)) +500*(3*t+1)*(B+1)+30*(2*W+3)

theorem finishCommand_eval (t : ℕ) (ht : 0 < t) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t)
    (d : Data) (hp : Scalar.Prepared t M cache u d) (W : ℕ)
    (h37 : d.stacks 37=List.replicate (3*t) true)
    (h26 : d.stacks 26=[]) (h22 : d.stacks 22=[])
    (h32 : d.stacks 32=[]) (h33 : d.stacks 33=[])
    (h34 : d.stacks 34=[]) (h35 : d.stacks 35=[]) (h36 : d.stacks 36=[])
    (hW : ∀ p ∈ preparationDiscard, (d.stacks p).length ≤ W) :
    ∃ cost e, cost ≤ finishBudget t (SubexpLiftRing.baseWidth 3 t) W ∧
      Eval finishCommand cost d e ∧
      e.stacks = finishedStacks d.stacks t
        (IdempotentProgram.tableTape (IdempotentProgram.tableCode (t := t) (RingProgram.scalarProgram 3 t M cache))) := by
  let table := IdempotentProgram.tableTape (IdempotentProgram.tableCode (t := t) (RingProgram.scalarProgram 3 t M cache))
  obtain ⟨nt,rt,hnt,het⟩ := prepared_nativeTable_eval t M cache u d hp h37 h26 h22
  let a : Data := ⟨rt,Function.update d.stacks 22 table⟩
  have hzero : (d.stacks 17).length = SubexpLiftRing.baseWidth 3 t := by
    rw [prepared_zero t M cache u d hp]
    exact cache.zero.property
  have hp1 : d.stacks (1 : Fin 41) = [] := by
    change d.stacks (Fin.castAdd 33 (1 : Fin 8)) = []
    simpa only [Scalar.low, ite_eq_right (show (1 : Fin 8) ≠ 5 by decide)] using hp.rest.1 (1 : Fin 8)
  have hp2 : d.stacks (2 : Fin 41) = [] := by
    change d.stacks (Fin.castAdd 33 (2 : Fin 8)) = []
    simpa only [Scalar.low, ite_eq_right (show (2 : Fin 8) ≠ 5 by decide)] using hp.rest.1 (2 : Fin 8)
  obtain ⟨na,ra,hna,hea⟩ := arrayStage_eval a t (SubexpLiftRing.baseWidth 3 t) ht
    (by simpa [a] using h37) (by simpa [a] using hp1)
    (by simpa [a] using hp2) (by simpa [a] using h32)
    (by simpa [a] using h33) (by simpa [a] using h34)
    (by simpa [a] using h35) (by simpa [a] using h36)
    (by simpa [a] using hzero) (by simp [a,hp.half,u.property])
    (by simp [a,hp.minusOne,cache.minusOne.property])
    (by simp only [a,Function.update_of_ne (by decide : (30:Fin 41)≠22),hp.twice]
        exact (SubexpPreparedQuartic.wordAdd 3 t M u u).1.property)
    (by simp only [a,Function.update_of_ne (by decide : (31:Fin 41)≠22),hp.minusThree]
        exact (SubexpPreparedQuartic.wordMul 3 t M
          (SubexpPreparedQuartic.wordAdd 3 t M (SubexpPreparedQuartic.wordAdd 3 t M u u).1 u).1
          cache.minusOne).1.property)
  let b : Data := ⟨ra,arrayStacks a.stacks t⟩
  have hb : ∀ p ∈ preparationDiscard, b.stacks p=d.stacks p := by
    intro p hmem
    have hp22 : p ≠ (22 : Fin 41) := by
      intro h; subst p; norm_num [preparationDiscard] at hmem
    have hp32 : p ≠ (32 : Fin 41) := by
      intro h; subst p; norm_num [preparationDiscard] at hmem
    have hp33 : p ≠ (33 : Fin 41) := by
      intro h; subst p; norm_num [preparationDiscard] at hmem
    have hp34 : p ≠ (34 : Fin 41) := by
      intro h; subst p; norm_num [preparationDiscard] at hmem
    have hp35 : p ≠ (35 : Fin 41) := by
      intro h; subst p; norm_num [preparationDiscard] at hmem
    have hp36 : p ≠ (36 : Fin 41) := by
      intro h; subst p; norm_num [preparationDiscard] at hmem
    simp [b, a, arrayStacks, hp22, hp32, hp33, hp34, hp35, hp36]
  obtain ⟨nc,e,hnc,hec,hs⟩ := preparationCleanup_eval b W (by
    intro p hmem
    rw [hb p hmem]
    exact hW p hmem)
  refine ⟨nt+(na+nc),e,?_,het.seq (hea.seq hec),?_⟩
  · dsimp [finishBudget]; omega
  · funext i
    rw [hs]
    rfl

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
