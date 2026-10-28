import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramStorage
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgramFullTable
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgramRun

namespace OAI.Algorithms

/-! Actual original/factor ID selection from the common full word table.
The input masters are copied into an isolated lookup program, and its output
records are copied back before the entire lookup workspace is cleared. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev unary (n : ℕ) := List.replicate n true
abbrev zeros (n : ℕ) := List.replicate n false

def headInputs : List (Fin 768 × Fin 64) :=
  [(128,30),(134,31),(649,32),(133,33),(132,38)]
def headOutputs : List (Fin 64 × Fin 768) := [(0,650),(1,651)]
def heads : Code := stage HeadIdentifierProgram.FullTable.program id (by decide) headInputs headOutputs

theorem headInputs_protected : ∀ p ∈ headInputs,Protected p.1 := by simp [headInputs,Protected,temporary]
theorem headOutputs_protected : ∀ p ∈ headOutputs,Protected p.2 := by simp [headOutputs,Protected,temporary]

def headResult (a : Data) (n : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ) : Data :=
  returned id (by decide) headInputs headOutputs a
    (HeadIdentifierProgram.FullTable.result n rows low W z)
def headCost (a : Data) (n : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ) :=
  stageCost id (by decide) headInputs headOutputs a
    (HeadIdentifierProgram.FullTable.result n rows low W z)
    (HeadIdentifierProgram.FullTable.budget n rows.length W low.length z)

theorem heads_eval (a : Data) (n : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ)
    (hn : a.stacks 128=unary n) (hlow : a.stacks 134=low)
    (hz : a.stacks 649=unary z) (hrows : a.stacks 133=rows.flatten)
    (hW : a.stacks 132=unary W) (hw : ∀ row∈rows,row.length=W) (hsize : n ≤ rows.length) :
    ∃ t ≤ headCost a n rows low W z,Eval heads t a (headResult a n rows low W z) := by
  let regs := (prepared (by decide) headInputs a).regs
  have hp : projectState id (workPort (by decide)) (prepared (by decide) headInputs a)=
      HeadIdentifierProgram.FullTable.input regs n rows low W z := by
    apply prepared_eq id (by decide) headInputs a _ headInputs_protected (by decide)
    · intro j; rfl
    · intro p hp
      simp only [headInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl <;>
        simp [HeadIdentifierProgram.FullTable.input,HeadIdentifierProgram.FullTable.baseStacks,
          hn,hlow,hz,hrows,hW,unary]
    · intro j hj
      have h30 : j≠30 := hj (128,30) (by simp [headInputs])
      have h31 : j≠31 := hj (134,31) (by simp [headInputs])
      have h32 : j≠32 := hj (649,32) (by simp [headInputs])
      have h33 : j≠33 := hj (133,33) (by simp [headInputs])
      have h38 : j≠38 := hj (132,38) (by simp [headInputs])
      simp [HeadIdentifierProgram.FullTable.input,HeadIdentifierProgram.FullTable.baseStacks,
        h30,h31,h32,h33,h38]
  obtain ⟨t,ht,he⟩ := HeadIdentifierProgram.FullTable.program_runsIn regs n rows low W z hw hsize
  have hc := stage_eval HeadIdentifierProgram.FullTable.program id Function.injective_id
    (by decide) headInputs headOutputs a _ _ headInputs_protected headOutputs_protected hp he
  refine ⟨_,?_,hc⟩
  unfold headCost stageCost
  omega

theorem headResult_ids (a : Data) (n : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ) :
    (headResult a n rows low W z).stacks 650=
      HeadScatterProgram.indices (HeadIdentifierProgram.chosenIds
        (HeadIdentifierProgram.predicate rows low z) n) := by
  exact returned_word id (by decide) headInputs headOutputs a _ headOutputs_protected
    (by decide) (0,650) (by simp [headOutputs])

theorem headResult_count (a : Data) (n : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ) :
    (headResult a n rows low W z).stacks 651=
      zeros (HeadIdentifierProgram.count (HeadIdentifierProgram.predicate rows low z) n) := by
  exact returned_word id (by decide) headInputs headOutputs a _ headOutputs_protected
    (by decide) (1,651) (by simp [headOutputs])

theorem headResult_frame (a : Data) (n : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ)
    (i : Fin 768) (hi : Protected i) (h650 : i≠650) (h651 : i≠651) :
    (headResult a n rows low W z).stacks i=a.stacks i := by
  apply returned_frame id (by decide) headInputs headOutputs a _ i hi
  intro p hp
  simp only [headOutputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl <;> assumption

def factorInputs : List (Fin 768 × Fin 64) :=
  [(129,30),(128,31),(649,32),(133,33),(132,38)]
def factorOutputs : List (Fin 64 × Fin 768) := [(0,671)]
def factors : Code := stage LeafHeadFactorsProgram.program id (by decide) factorInputs factorOutputs

theorem factorInputs_protected : ∀ p ∈ factorInputs,Protected p.1 := by simp [factorInputs,Protected,temporary]
theorem factorOutputs_protected : ∀ p ∈ factorOutputs,Protected p.2 := by simp [factorOutputs,Protected,temporary]

def factorResult (a : Data) (A N : ℕ) (rows : List (List Bool)) (W z : ℕ) : Data :=
  returned id (by decide) factorInputs factorOutputs a
    (LeafHeadFactorsProgram.result rows A N W z)
def factorCost (a : Data) (A N : ℕ) (rows : List (List Bool)) (W z : ℕ) :=
  stageCost id (by decide) factorInputs factorOutputs a
    (LeafHeadFactorsProgram.result rows A N W z)
    (LeafHeadFactorsProgram.budget A N rows.length W z)

theorem factors_eval (a : Data) (A N : ℕ) (rows : List (List Bool)) (W z : ℕ)
    (hN : a.stacks 129=unary N) (hA : a.stacks 128=unary A)
    (hz : a.stacks 649=unary z) (hrows : a.stacks 133=rows.flatten)
    (hW : a.stacks 132=unary W) (hw : ∀ row∈rows,row.length=W) (hsize : A+N ≤ rows.length) :
    ∃ t ≤ factorCost a A N rows W z,Eval factors t a (factorResult a A N rows W z) := by
  let regs := (prepared (by decide) factorInputs a).regs
  have hp : projectState id (workPort (by decide)) (prepared (by decide) factorInputs a)=
      LeafHeadFactorsProgram.input regs rows A N W z := by
    apply prepared_eq id (by decide) factorInputs a _ factorInputs_protected (by decide)
    · intro j; rfl
    · intro p hp
      simp only [factorInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl <;>
        simp [LeafHeadFactorsProgram.input,LeafHeadFactorsProgram.baseStacks,hN,hA,hz,hrows,hW,unary]
    · intro j hj
      have h30 : j≠30 := hj (129,30) (by simp [factorInputs])
      have h31 : j≠31 := hj (128,31) (by simp [factorInputs])
      have h32 : j≠32 := hj (649,32) (by simp [factorInputs])
      have h33 : j≠33 := hj (133,33) (by simp [factorInputs])
      have h38 : j≠38 := hj (132,38) (by simp [factorInputs])
      simp [LeafHeadFactorsProgram.input,LeafHeadFactorsProgram.baseStacks,h30,h31,h32,h33,h38]
  obtain ⟨t,ht,he⟩ := LeafHeadFactorsProgram.program_runsIn regs rows A N W z hw hsize
  have hc := stage_eval LeafHeadFactorsProgram.program id Function.injective_id (by decide)
    factorInputs factorOutputs a _ _ factorInputs_protected factorOutputs_protected hp he
  refine ⟨_,?_,hc⟩
  unfold factorCost stageCost
  omega

theorem factorResult_ids (a : Data) (A N : ℕ) (rows : List (List Bool)) (W z : ℕ) :
    (factorResult a A N rows W z).stacks 671=ProgramEncoding.encodeRecords
      ((LeafHeadFactorsProgram.chosenIds (LeafHeadFactorsProgram.predicate rows A z) N).map
        SubexponentialSAT.Encoding.encodeNat) := by
  exact returned_word id (by decide) factorInputs factorOutputs a _ factorOutputs_protected
    (by decide) (0,671) (by simp [factorOutputs])

theorem factorResult_frame (a : Data) (A N : ℕ) (rows : List (List Bool)) (W z : ℕ)
    (i : Fin 768) (hi : Protected i) (h671 : i≠671) :
    (factorResult a A N rows W z).stacks i=a.stacks i := by
  apply returned_frame id (by decide) factorInputs factorOutputs a _ i hi
  intro p hp
  simp only [factorOutputs,List.mem_singleton] at hp
  subst p
  exact h671

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
