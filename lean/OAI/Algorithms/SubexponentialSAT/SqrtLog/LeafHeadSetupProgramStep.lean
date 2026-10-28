import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramMatrixRun

namespace OAI.Algorithms

/-! One actual head visit, from the common assignment table through the
integer matrix and attained buckets to the updated Cartesian table. The
integer-entry contract remains explicit pending its concrete instantiation. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

def selectedMask (n : ℕ) (rows : List (List Bool)) (low : List Bool) (z : ℕ) : List Bool :=
  HeadScatterProgram.mask n (selectedHeads n rows low z)
    (List.replicate (selectedHeads n rows low z).length true)
def selectedContext (n N : ℕ) (rows : List (List Bool)) (z : ℕ) : List Bool :=
  ProgramEncoding.encodeRecords ((LeafHeadFactorsProgram.chosenIds
    (LeafHeadFactorsProgram.predicate rows n z) N).map SubexponentialSAT.Encoding.encodeNat)



def headStepResult (a : Data) (rp : Fin 8 → Bool) (mb : State 16 288) (rt : Fin 10 → Bool)
    (n N W z : ℕ) (rows prior : List (List Bool)) (low : List Bool)
    (shifted : List (List (List Bool))) : Data :=
  let js := selectedHeads n rows low z
  let p := preparedHead a rp n N rows low W z
  let m := returned id (by decide) matrixInputs matrixOutputs p mb
  let bs := BucketTupleProgram.actualBuckets (a.stacks 141) shifted js n js.length
  let q := tupleResult m rt prior (selectedMask n rows low z) (selectedContext n N rows z) bs
  SubexponentialSAT.Subexp.TupleProgram.pushedState (649 : Fin 768) (0 : Fin 16) true
    (clearManyState [650,651,652,669,670,671] q)

def headStepCost (a : Data) (rp : Fin 8 → Bool) (mb : State 16 288) (rt : Fin 10 → Bool)
    (n N D W z T B : ℕ) (rows prior : List (List Bool)) (low : List Bool)
    (matrixRows : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) : ℕ :=
  let js := selectedHeads n rows low z
  let p := preparedHead a rp n N rows low W z
  let m := returned id (by decide) matrixInputs matrixOutputs p mb
  let bs := BucketTupleProgram.actualBuckets (a.stacks 141) shifted js n js.length
  let q := tupleResult m rt prior (selectedMask n rows low z) (selectedContext n N rows z) bs
  prepareHeadCost a rp n N rows low W z+
    stageCost id (by decide) matrixInputs matrixOutputs p mb
      (LayoutMatrixProgram.commandCost T B D n js+BucketProgram.preMatrixCost (a.stacks 141) matrixRows+
        BucketProgram.Controller.cost (a.stacks 141) shifted js n js.length+3)+
    tupleCost m rt prior (selectedMask n rows low z) (selectedContext n N rows z) bs+
    clearManyCost [650,651,652,669,670,671] q+2

theorem headStep_eval (entry : Cmd 16 256) (a : Data) (n N D W z : ℕ)
    (rows prior : List (List Bool)) (low : List Bool)
    (hn : a.stacks 128=unary n) (hN : a.stacks 129=unary N)
    (hW : a.stacks 132=unary W) (hrows : a.stacks 133=rows.flatten)
    (hlow : a.stacks 134=low) (hD : a.stacks 647=unary D) (hz : a.stacks 649=unary z)
    (hp : a.stacks 660=ProgramEncoding.encodeRecords prior) (hmark : a.stacks 665=[false])
    (hw : ∀ row∈rows,row.length=W) (hsize : n+N ≤ rows.length)
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop) (T B : ℕ)
    (hc : ∀ regs,LayoutMatrixProgram.EntryContract entry
      (matrixBase (preparedHead a regs n N rows low W z)) Valid Rel T B)
    (hv : ∀ j < D,∀ v∈selectedHeads n rows low z,Valid j v) :
    ∃ matrixRows shifted t e,
      LayoutMatrixProgram.MatrixRel Rel B D (selectedHeads n rows low z) matrixRows ∧
      List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (a.stacks 141))) matrixRows shifted ∧
      Eval (headStep entry) t a e ∧
      e.stacks 660=ProgramEncoding.encodeRecords
        (BucketTupleProgram.Expand.nextRows prior (selectedMask n rows low z)
          (selectedContext n N rows z)
          (BucketTupleProgram.actualBuckets (a.stacks 141) shifted (selectedHeads n rows low z)
            n (selectedHeads n rows low z).length)) ∧
      e.stacks 649=unary (z+1) ∧ e.stacks 648=a.stacks 648 ∧
      (∀ i∈([650,651,652,669,670,671] : List (Fin 768)),e.stacks i=[]) ∧
      (∀ i,Protected i→i∉([649,650,651,652,660,669,670,671] : List (Fin 768))→
        e.stacks i=a.stacks i) ∧
      (∃ rp mb rt,
        MatrixExecution entry (preparedHead a rp n N rows low W z) D n
          (selectedHeads n rows low z) T B matrixRows shifted mb ∧
        e=headStepResult a rp mb rt n N W z rows prior low shifted ∧
        t ≤ headStepCost a rp mb rt n N D W z T B rows prior low matrixRows shifted) := by
  let js := selectedHeads n rows low z
  obtain ⟨rp,tp,htp,hep⟩ := prepareHead_eval a n N rows low W z hn hN hlow hz hrows hW hw hsize
  let p := preparedHead a rp n N rows low W z
  have pf (i : Fin 768) (hi : Protected i) (h650 : i≠650) (h651 : i≠651)
      (h652 : i≠652) (h670 : i≠670) (h671 : i≠671) : p.stacks i=a.stacks i :=
    preparedHead_frame a rp n N rows low W z i hi h650 h651 h652 h670 h671
  have pn : p.stacks 128=unary n :=
    (pf 128 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hn
  have pD : p.stacks 647=unary D :=
    (pf 647 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hD
  have p141 : p.stacks 141=a.stacks 141 :=
    pf 141 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨mr,ys,mb,tm,m,hmr,hys,htm,hem,hemdef,hmout,mf,hmrun⟩ := matrixBuckets_eval entry p D n js pD pn
    (preparedHead_ids a rp n N rows low W z) (preparedHead_count a rp n N rows low W z)
    (HeadIdentifierProgram.chosenIds_bound _ _) Valid Rel T B (hc rp) hv
  rw [p141] at hys hmout htm
  let bs := BucketTupleProgram.actualBuckets (a.stacks 141) ys js n js.length
  have m660 : m.stacks 660=ProgramEncoding.encodeRecords prior :=
    (mf 660 (by decide) (by decide)).trans
      ((pf 660 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hp)
  have m665 : m.stacks 665=[false] :=
    (mf 665 (by decide) (by decide)).trans
      ((pf 665 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hmark)
  have m670 : m.stacks 670=selectedMask n rows low z :=
    (mf 670 (by decide) (by decide)).trans (preparedHead_mask a rp n N rows low W z)
  have m671 : m.stacks 671=selectedContext n N rows z :=
    (mf 671 (by decide) (by decide)).trans (preparedHead_context a rp n N rows low W z)
  obtain ⟨rt,tt,htt,het⟩ := appendHead_eval m prior (selectedMask n rows low z)
    (selectedContext n N rows z) bs m660 m665 hmout m670 m671
  let q := tupleResult m rt prior (selectedMask n rows low z) (selectedContext n N rows z) bs
  let cleared := clearManyState ([650,651,652,669,670,671] : List (Fin 768)) q
  let e := SubexponentialSAT.Subexp.TupleProgram.pushedState (649 : Fin 768) (0 : Fin 16) true cleared
  have hec : Eval clearHead (clearManyCost [650,651,652,669,670,671] q) q cleared :=
    clearMany_eval _ _
  have hea := SubexponentialSAT.Subexp.TupleProgram.pushConst_eval (649 : Fin 768) (0 : Fin 16) true cleared
  have q649 : q.stacks 649=unary z :=
    (tupleResult_frame m rt prior _ _ bs 649 (by decide) (by decide)).trans
      ((mf 649 (by decide) (by decide)).trans
        ((pf 649 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hz))
  have q648 : q.stacks 648=a.stacks 648 :=
    (tupleResult_frame m rt prior _ _ bs 648 (by decide) (by decide)).trans
      ((mf 648 (by decide) (by decide)).trans
        (pf 648 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))
  refine ⟨mr,ys,_,e,hmr,hys,hep.seq (hem.seq (het.seq (hec.seq hea))),?_,?_,?_,?_,?_,?_⟩
  · simpa [e,cleared,SubexponentialSAT.Subexp.TupleProgram.pushedState,clearMany_stacks] using
      tupleResult_value m rt prior (selectedMask n rows low z) (selectedContext n N rows z) bs
  · simp [e,cleared,clearMany_stacks,q649,unary,List.replicate_succ]
  · simpa [e,cleared,SubexponentialSAT.Subexp.TupleProgram.pushedState,clearMany_stacks] using q648
  · intro i hi
    have h649 : i≠649 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    simp [e,cleared,clearMany_stacks,hi,h649]

  · intro i hi hne
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hne
    rcases hne with ⟨h649,h650,h651,h652,h660,h669,h670,h671⟩
    have qf : q.stacks i=a.stacks i :=
      (tupleResult_frame m rt prior _ _ bs i hi h660).trans
        ((mf i hi h669).trans (pf i hi h650 h651 h652 h670 h671))
    simpa [e,cleared,SubexponentialSAT.Subexp.TupleProgram.pushedState,clearMany_stacks,
      h649,h650,h651,h652,h669,h670,h671] using qf

  · refine ⟨rp,mb,rt,hmrun,?_,?_⟩
    · dsimp [headStepResult]
      rw [←hemdef]
    · have hm : m=returned id (by decide) matrixInputs matrixOutputs p mb := hemdef
      dsimp [headStepCost]
      rw [←hm]
      change tp+(tm+(tt+(clearManyCost [650,651,652,669,670,671] q+2))) ≤ _
      dsimp [p,js,bs,q] at htm htt ⊢
      omega

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end
end OAI.Algorithms
