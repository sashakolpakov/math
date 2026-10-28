import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramSelection
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramSupport

namespace OAI.Algorithms

/-! The complete head-selection stage. All three objects consumed by the
matrix/bucket phase are computed from runtime masters by fixed programs. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def selectedHeads (n : ℕ) (rows : List (List Bool)) (low : List Bool) (z : ℕ) : List ℕ :=
  HeadIdentifierProgram.chosenIds (HeadIdentifierProgram.predicate rows low z) n

def prepareHead : Code := .seq heads (.seq support factors)

def preparedHead (a : Data) (regs : Fin 8 → Bool) (n N : ℕ) (rows : List (List Bool))
    (low : List Bool) (W z : ℕ) : Data :=
  factorResult (scatterResult (countResult (headResult a n rows low W z)) regs n
    (selectedHeads n rows low z)) n N rows W z

def prepareHeadCost (a : Data) (regs : Fin 8 → Bool) (n N : ℕ) (rows : List (List Bool))
    (low : List Bool) (W z : ℕ) : ℕ :=
  let b := headResult a n rows low W z
  let c := countResult b
  let d := scatterResult c regs n (selectedHeads n rows low z)
  headCost a n rows low W z+countCost b+scatterCost c regs n (selectedHeads n rows low z)+
    factorCost d n N rows W z

theorem prepareHead_eval (a : Data) (n N : ℕ) (rows : List (List Bool))
    (low : List Bool) (W z : ℕ)
    (hn : a.stacks 128=unary n) (hN : a.stacks 129=unary N)
    (hlow : a.stacks 134=low) (hz : a.stacks 649=unary z)
    (hrows : a.stacks 133=rows.flatten) (hW : a.stacks 132=unary W)
    (hw : ∀ row∈rows,row.length=W) (hsize : n+N ≤ rows.length) :
    ∃ regs t,t ≤ prepareHeadCost a regs n N rows low W z ∧
      Eval prepareHead t a (preparedHead a regs n N rows low W z) := by
  let js := selectedHeads n rows low z
  let b := headResult a n rows low W z
  let c := countResult b
  obtain ⟨t1,ht1,h1⟩ := heads_eval a n rows low W z hn hlow hz hrows hW hw (by omega)
  have hbi : b.stacks 650=HeadScatterProgram.indices js := headResult_ids a n rows low W z
  have hbc : (b.stacks 651).length=js.length := by
    rw [headResult_count]
    simp [zeros,js,selectedHeads,HeadIdentifierProgram.count]
  have hbn : b.stacks 128=List.replicate n true :=
    (headResult_frame a n rows low W z 128 (by decide) (by decide) (by decide)).trans hn
  obtain ⟨regs,t2,ht2,h2⟩ := support_eval b n js hbi hbc hbn
    (HeadIdentifierProgram.chosenIds_bound _ _)
  let d := scatterResult c regs n js
  have hdframe (i : Fin 768) (hi : Protected i) (h650 : i≠650) (h651 : i≠651)
      (h652 : i≠652) (h670 : i≠670) : d.stacks i=a.stacks i :=
    (scatterResult_frame c regs n js i hi h670).trans
      ((countResult_frame b i hi h652).trans
        (headResult_frame a n rows low W z i hi h650 h651))
  obtain ⟨t3,ht3,h3⟩ := factors_eval d n N rows W z
    ((hdframe 129 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hN)
    ((hdframe 128 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hn)
    ((hdframe 649 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hz)
    ((hdframe 133 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hrows)
    ((hdframe 132 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hW) hw hsize
  refine ⟨regs,t1+(t2+t3),?_,h1.seq (h2.seq h3)⟩
  change t1+(t2+t3) ≤ headCost a n rows low W z+countCost b+scatterCost c regs n js+factorCost d n N rows W z
  change t2 ≤ countCost b+scatterCost c regs n js at ht2
  omega

theorem preparedHead_ids (a : Data) (regs : Fin 8 → Bool) (n N : ℕ)
    (rows : List (List Bool)) (low : List Bool) (W z : ℕ) :
    (preparedHead a regs n N rows low W z).stacks 650=
      HeadScatterProgram.indices (selectedHeads n rows low z) := by
  rw [preparedHead,factorResult_frame _ _ _ _ _ _ _ (by decide) (by decide),
    scatterResult_frame _ _ _ _ _ (by decide) (by decide),
    countResult_frame _ _ (by decide) (by decide)]
  exact headResult_ids _ _ _ _ _ _

theorem preparedHead_count (a : Data) (regs : Fin 8 → Bool) (n N : ℕ)
    (rows : List (List Bool)) (low : List Bool) (W z : ℕ) :
    (preparedHead a regs n N rows low W z).stacks 651=
      List.replicate (selectedHeads n rows low z).length false := by
  rw [preparedHead,factorResult_frame _ _ _ _ _ _ _ (by decide) (by decide),
    scatterResult_frame _ _ _ _ _ (by decide) (by decide),
    countResult_frame _ _ (by decide) (by decide),headResult_count]
  rfl

theorem preparedHead_mask (a : Data) (regs : Fin 8 → Bool) (n N : ℕ)
    (rows : List (List Bool)) (low : List Bool) (W z : ℕ) :
    (preparedHead a regs n N rows low W z).stacks 670=HeadScatterProgram.mask n
      (selectedHeads n rows low z) (List.replicate (selectedHeads n rows low z).length true) := by
  rw [preparedHead,factorResult_frame _ _ _ _ _ _ _ (by decide) (by decide)]
  exact scatterResult_value _ _ _ _

theorem preparedHead_context (a : Data) (regs : Fin 8 → Bool) (n N : ℕ)
    (rows : List (List Bool)) (low : List Bool) (W z : ℕ) :
    (preparedHead a regs n N rows low W z).stacks 671=ProgramEncoding.encodeRecords
      ((LeafHeadFactorsProgram.chosenIds (LeafHeadFactorsProgram.predicate rows n z) N).map SubexponentialSAT.Encoding.encodeNat) :=
  factorResult_ids _ _ _ _ _ _

theorem preparedHead_frame (a : Data) (regs : Fin 8 → Bool) (n N : ℕ)
    (rows : List (List Bool)) (low : List Bool) (W z : ℕ) (i : Fin 768)
    (hi : Protected i) (h650 : i≠650) (h651 : i≠651) (h652 : i≠652) (h670 : i≠670) (h671 : i≠671) :
    (preparedHead a regs n N rows low W z).stacks i=a.stacks i := by
  rw [preparedHead,factorResult_frame _ _ _ _ _ _ _ hi h671,
    scatterResult_frame _ _ _ _ _ hi h670,countResult_frame _ _ hi h652]
  exact headResult_frame _ _ _ _ _ _ _ hi h650 h651

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end
end OAI.Algorithms
