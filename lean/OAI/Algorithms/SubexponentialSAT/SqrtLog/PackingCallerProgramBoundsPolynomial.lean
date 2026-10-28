import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramBoundsCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramBoundsOutput

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds
open CostAssembly.Polynomial
open SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

private theorem planEnvelope_ordinary : Ordinary planEnvelope := by
  unfold planEnvelope
  exact (ordinary_add (ordinary_const 1) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 16) (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_const 24)) ordinary_id))

private theorem pairEnvelope_ordinary : Ordinary pairEnvelope := by
  unfold pairEnvelope
  exact (ordinary_add (ordinary_const 1) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 32) (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_const 1))) (ordinary_const 14)) (ordinary_pow ordinary_id 2)))

private theorem alphabetEnvelope_ordinary : Ordinary alphabetEnvelope := by
  unfold alphabetEnvelope
  exact (ordinary_add (ordinary_const 1) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_pow ordinary_id 2)) (ordinary_const 2)) ordinary_id))

private theorem seedEnvelope_ordinary : Ordinary seedEnvelope := by
  unfold seedEnvelope
  exact (ordinary_add (ordinary_const 1) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_const 2)) (ordinary_mul (ordinary_const 2) ordinary_id)))

private theorem extentEnvelope_ordinary : Ordinary extentEnvelope := by
  unfold extentEnvelope
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_const 1) ordinary_id) ordinary_id) (ordinary_const 0)) ordinary_id) ordinary_id) (ordinary_const 1)) (ordinary_const 2)) (ordinary_pow ordinary_id 2)) (ordinary_mul (ordinary_const 2) ordinary_id)) ordinary_id) (ordinary_add (ordinary_const 1) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_const 2)) ordinary_id))) alphabetEnvelope_ordinary) (ordinary_pow ordinary_id 2)) (ordinary_mul ordinary_id (ordinary_pow ordinary_id 2))) seedEnvelope_ordinary) pairEnvelope_ordinary)

private theorem sourceEnvelope_ordinary : Ordinary sourceEnvelope := by
  unfold sourceEnvelope
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add ordinary_id (ordinary_const 1)) ordinary_id) (ordinary_pow ordinary_id 2)) (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_pow ordinary_id 2))) alphabetEnvelope_ordinary) planEnvelope_ordinary) (ordinary_const 1))

private theorem loaderEnvelope_ordinary : Ordinary loaderEnvelope := by
  unfold loaderEnvelope
  exact (ordinary_mul (ordinary_const 22000) (ordinary_pow (ordinary_add (ordinary_add extentEnvelope_ordinary (ordinary_mul (ordinary_const 11) ordinary_id)) (ordinary_const 1)) 4))

private theorem readyEnvelope_ordinary : Ordinary readyEnvelope := by
  unfold readyEnvelope
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) extentEnvelope_ordinary) extentEnvelope_ordinary) (ordinary_mul (ordinary_const 4) ordinary_id)) (ordinary_const 4))

private theorem scoreEnvelope_ordinary : Ordinary scoreEnvelope := by
  unfold scoreEnvelope
  exact (ordinary_add (ordinary_mul (ordinary_pow (ordinary_mul ordinary_id ordinary_id) 2) (ordinary_mul (ordinary_pow ordinary_id 2) (ordinary_pow ordinary_id 4))) (ordinary_mul (ordinary_mul (ordinary_const 8) (ordinary_pow (ordinary_mul ordinary_id ordinary_id) 2)) (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_pow ordinary_id 2))))

private theorem controllerEnvelope_ordinary : Ordinary controllerEnvelope := by
  unfold controllerEnvelope PackingProgram.Assembly.uniformBudget
    PackingProgram.Assembly.headBudgetBound SequentialProgram.selectionBudget
    SequentialProgram.minimumBudget SequentialProgram.recordBudget SequentialProgram.updateBudget
  exact (ordinary_add (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_mul (ordinary_mul (ordinary_const 10000) (ordinary_pow (ordinary_const 31) 6)) (ordinary_pow (ordinary_add (ordinary_mul (ordinary_const 32) (ordinary_pow (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_pow ordinary_id 2)) ordinary_id) (ordinary_pow ordinary_id 2)) (ordinary_const 1)) 2)) (ordinary_const 1)) 12)) (ordinary_pow ordinary_id 4)) (ordinary_mul (ordinary_const 12) (ordinary_mul (ordinary_const 4) ordinary_id))) (ordinary_const 48)) (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 80) (ordinary_pow (ordinary_add (ordinary_add (ordinary_add ordinary_id (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_mul (ordinary_const 4) ordinary_id)) (ordinary_const 1)) 2)) (ordinary_const 1)) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_mul (ordinary_const 24) (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_pow ordinary_id 2)) (ordinary_mul (ordinary_const 25) (ordinary_mul (ordinary_const 2) ordinary_id))) (ordinary_mul (ordinary_const 13) (ordinary_pow ordinary_id 2))) (ordinary_const 48))) (ordinary_const 1)) (ordinary_add (ordinary_mul (ordinary_const 7) (ordinary_add (ordinary_const 1) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_pow ordinary_id 2)) (ordinary_const 2)) ordinary_id))) (ordinary_const 5))) (ordinary_const 16)) (ordinary_add (ordinary_mul ordinary_id (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_mul (ordinary_const 43) (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_pow ordinary_id 2)) (ordinary_mul (ordinary_const 20) (ordinary_mul (ordinary_const 2) ordinary_id))) (ordinary_mul (ordinary_const 17) (ordinary_pow ordinary_id 2))) (ordinary_const 66))) (ordinary_const 22))) (ordinary_mul (ordinary_const 3) (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_add (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_pow ordinary_id 2)) (ordinary_mul (ordinary_const 2) ordinary_id))) (ordinary_const 3))))) (ordinary_mul (ordinary_const 500) (ordinary_pow (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_mul (ordinary_const 4) ordinary_id)) (ordinary_const 4)) 2))) (ordinary_const 1)) (ordinary_mul (ordinary_mul (ordinary_mul (ordinary_const 500) (ordinary_add ordinary_id (ordinary_const 1))) (ordinary_add (ordinary_add (ordinary_mul (ordinary_pow ordinary_id 2) (ordinary_pow ordinary_id 2)) (ordinary_mul (ordinary_mul (ordinary_const 8) (ordinary_pow ordinary_id 2)) (ordinary_pow ordinary_id 2))) (ordinary_const 1))) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_mul (ordinary_const 4) ordinary_id)) (ordinary_const 6)) (ordinary_add (ordinary_mul (ordinary_pow ordinary_id 2) (ordinary_pow ordinary_id 4)) (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_pow ordinary_id 2)))) (ordinary_const 1)))) (ordinary_mul (ordinary_const 6) (ordinary_add (ordinary_mul ordinary_id (ordinary_add (ordinary_mul (ordinary_mul (ordinary_const 4) (ordinary_add (ordinary_mul (ordinary_pow ordinary_id 2) (ordinary_pow ordinary_id 2)) (ordinary_mul (ordinary_mul (ordinary_const 8) (ordinary_pow ordinary_id 2)) (ordinary_pow ordinary_id 2)))) (ordinary_add (ordinary_mul (ordinary_pow ordinary_id 2) (ordinary_pow ordinary_id 4)) (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_pow ordinary_id 2)))) (ordinary_const 2))) (ordinary_const 1)))) (ordinary_mul (ordinary_const 4) (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_mul (ordinary_const 4) ordinary_id)) (ordinary_const 6)))) (ordinary_const 14)) (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_const 9) (ordinary_mul (ordinary_const 500) (ordinary_pow (ordinary_mul ordinary_id (ordinary_add scoreEnvelope_ordinary (ordinary_const 1))) 2))) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul ordinary_id (ordinary_add (ordinary_mul (ordinary_const 14) (ordinary_pow ordinary_id 2)) (ordinary_const 10))) (ordinary_mul (ordinary_const 15) (ordinary_pow ordinary_id 2))) (ordinary_const 16)) (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 7) (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_const 5)) (ordinary_add (ordinary_add (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_add (ordinary_mul (ordinary_const 14) (ordinary_pow ordinary_id 2)) (ordinary_const 10))) (ordinary_mul (ordinary_const 20) (ordinary_pow ordinary_id 2))) (ordinary_const 21))))) (ordinary_mul (ordinary_const 9) (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_mul ordinary_id scoreEnvelope_ordinary)) (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_const 1)) (ordinary_mul (ordinary_const 500) (ordinary_pow (ordinary_mul ordinary_id (ordinary_add scoreEnvelope_ordinary (ordinary_const 1))) 2))) (ordinary_pow ordinary_id 2))) (ordinary_const 3)))) (ordinary_const 2))) (ordinary_const 3))) (ordinary_const 3))

private theorem selectionEnvelope_ordinary : Ordinary selectionEnvelope := by
  unfold selectionEnvelope
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 7) readyEnvelope_ordinary) (ordinary_const 5)) (ordinary_add (ordinary_mul (ordinary_const 7) readyEnvelope_ordinary) (ordinary_const 5))) controllerEnvelope_ordinary) (ordinary_add (ordinary_mul (ordinary_const 7) (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_pow ordinary_id 2))) (ordinary_const 5))) (ordinary_mul (ordinary_const 48) (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 48) readyEnvelope_ordinary) (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_pow ordinary_id 2))) (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_const 1))) (ordinary_const 3))))

private theorem produceEnvelope_ordinary : Ordinary produceEnvelope := by
  unfold produceEnvelope
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 4000) (ordinary_pow (ordinary_add (ordinary_mul (ordinary_const 3) ordinary_id) (ordinary_const 1)) 3)) (ordinary_const 1)) (ordinary_add (ordinary_mul (ordinary_const 7) planEnvelope_ordinary) (ordinary_const 5))) (ordinary_add (ordinary_const 4) (ordinary_mul (ordinary_const 100) (ordinary_add (ordinary_add (ordinary_mul (ordinary_mul (ordinary_const 2400) (ordinary_pow (ordinary_add ordinary_id (ordinary_const 1)) 2)) (ordinary_add (ordinary_mul (ordinary_const 24) (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_const 34))) (ordinary_const 11)) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 16) (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_const 24)) ordinary_id)))))

private theorem prepareEnvelope_ordinary : Ordinary prepareEnvelope := by
  unfold prepareEnvelope
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 7) ordinary_id) (ordinary_const 6)) (ordinary_mul (ordinary_mul (ordinary_const 32) (ordinary_add ordinary_id (ordinary_const 1))) (ordinary_add ordinary_id (ordinary_const 1)))) (ordinary_const 1)) (ordinary_const 4)) (ordinary_mul (ordinary_const 7) (ordinary_add (ordinary_add (ordinary_add planEnvelope_ordinary (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_pow ordinary_id 2))) (ordinary_pow ordinary_id 2)) alphabetEnvelope_ordinary))) (ordinary_const 20))

private theorem suffixEnvelope_ordinary : Ordinary suffixEnvelope := by
  unfold suffixEnvelope
  exact (ordinary_add (ordinary_add (ordinary_add prepareEnvelope_ordinary (ordinary_mul (ordinary_const 81000000) (ordinary_pow sourceEnvelope_ordinary 12))) (ordinary_add (ordinary_mul (ordinary_const 7) (ordinary_mul (ordinary_const 34) (ordinary_pow sourceEnvelope_ordinary 4))) (ordinary_const 5))) (ordinary_mul (ordinary_const 48) (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_mul (ordinary_const 34) (ordinary_pow sourceEnvelope_ordinary 4))) (ordinary_const 3))))

private theorem coreEnvelope_ordinary : Ordinary coreEnvelope := by
  unfold coreEnvelope
  exact (ordinary_add (ordinary_add (ordinary_add produceEnvelope_ordinary loaderEnvelope_ordinary) selectionEnvelope_ordinary) suffixEnvelope_ordinary)

private theorem outputEnvelope_ordinary : Ordinary outputEnvelope := by
  unfold outputEnvelope
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add ordinary_id (ordinary_pow ordinary_id 2)) alphabetEnvelope_ordinary) planEnvelope_ordinary) (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_pow ordinary_id 2))) (ordinary_mul (ordinary_const 34) (ordinary_pow sourceEnvelope_ordinary 4)))

theorem coreBudget_polynomial : ∃ C d : ℕ, ∀ (outside : Store) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)), Parameters outside p →
    (w::tail).map ReadPlan.encodeWord=AssignmentAlphabetSemantics.wordBytes p.r p.Q →
    coreBudget outside p w tail ≤ C*(scalarSize outside p+1)^d := by
  obtain ⟨C,d,h⟩ := coreEnvelope_ordinary
  exact ⟨C,d,fun outside p w tail hp hw =>
    (coreBudget_le (scalarSize_cap outside p) hp w tail hw).trans (h _)⟩

theorem bankOutput_word_polynomial : ∃ C d : ℕ, ∀ (a : Wide.Data) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) (i : Fin 64),
    ((bankOutput a p w tail).stacks i).length ≤
      C*(scalarSize (Wide.parameterStore (Wide.project a)) p+1)^d := by
  obtain ⟨C,d,h⟩ := ordinary_add ordinary_id outputEnvelope_ordinary
  exact ⟨C,d,fun a p w tail i => (bankOutput_word_le a p w tail i).trans (h _)⟩

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds

end OAI.Algorithms
