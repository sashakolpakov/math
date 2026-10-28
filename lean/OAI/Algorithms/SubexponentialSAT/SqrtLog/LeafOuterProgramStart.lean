import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramBoundary
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramPrepare

namespace OAI.Algorithms

/-! Closed outer-leaf startup: count the actual clause records, compute the
numeric hash parameters, and preserve the exact binary decoder width. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

private theorem selector_port_val (j : Fin 14) :
    (LeafProgram.HashParameters.ports.hash.stack j).val=768+j.val := by
  fin_cases j <;> rfl

def startBudget (W : ℕ) (records : List (List Bool)) : ℕ :=
  let c := LeafProgram.ClauseCount.budget records+1
  let h := prepareHashBudget (W+c)
  c+h+9*(W+c+h)+8

structure StartReady (a : Data) (n m B : ℕ) : Prop where
  worker : WorkerEmpty a
  hash : Execution.HashInputs.Ready (projectState
    LeafProgram.HashParameters.ports.hash.register LeafProgram.HashParameters.ports.hash.stack a)
  ambient : BinaryArithmetic.toNat (a.stacks 785)=n
  clauses : BinaryArithmetic.toNat (a.stacks 782)=m
  occurrence : BinaryArithmetic.toNat (a.stacks 786)=B
  count : BinaryArithmetic.toNat (a.stacks 768)=3*m
  depth : BinaryArithmetic.toNat (a.stacks 773)=SparseCode.distanceDenom m B
  rounds : BinaryArithmetic.toNat (a.stacks 774)=HashSelect.loopCap n m
  width : a.stacks 783=a.stacks 768

theorem start_eval (a : Data) (W : ℕ) (records : List (List Bool))
    (hW : WordBound W a) (hempty : ∀ i : Fin 896, i.val ≤ 782 → a.stacks i=[])
    (hformula : a.stacks 784=Encoding.encodeList id records) (hm : records≠[]) :
    ∃ t ≤ startBudget W records, ∃ b, Eval start t a b ∧
      StartReady b (BinaryArithmetic.toNat (a.stacks 785)) records.length
        (BinaryArithmetic.toNat (a.stacks 786)) ∧
      (∀ i : Fin 896, 784 ≤ i.val → b.stacks i=a.stacks i) := by
  let C := LeafProgram.ClauseCount.budget records+1
  obtain ⟨nc,c,hec,hnc,hcm,_,hcf⟩ := clauseCount_eval a records hformula
    (fun i hi => hempty i (by omega)) (hempty 782 (by decide))
  have hcW : WordBound (W+C) c := SubexpSetupBoundSpec.wordBound_mono
    (SubexpSetupBoundSpec.eval_wordBound hW hec) (by omega)
  have hcr : Execution.HashInputs.Ready (projectState
      LeafProgram.HashParameters.ports.hash.register LeafProgram.HashParameters.ports.hash.stack c) := by
    intro j _ _ _ _
    change c.stacks (LeafProgram.HashParameters.ports.hash.stack j)=[]
    have hj := selector_port_val j
    rw [hcf _ (by intro h; have hh:=congrArg Fin.val h; have:=j.isLt; omega)]
    exact hempty _ (by have:=j.isLt; omega)
  have hc767 : c.stacks 767=[] := (hcf 767 (by decide)).trans (hempty 767 (by decide))
  have hcm0 : BinaryArithmetic.toNat (c.stacks 782)≠0 := by
    rw [hcm]
    exact Nat.ne_of_gt (List.length_pos_of_ne_nil hm)
  obtain ⟨nh,hnh,h,heh,hwh,hrh,h0,h5,h6,_,hhf⟩ := prepareHash_eval c (W+C) hcW hcr hcm0 hc767
  let H := prepareHashBudget (W+C)
  have hhW : WordBound (W+C+H) h := SubexpSetupBoundSpec.wordBound_mono
    (SubexpSetupBoundSpec.eval_wordBound hcW heh) (by omega)
  let b := routed (768,783) h
  have hsave := saveWidth_eval h (hwh 767)
  have hb768 : b.stacks 768=h.stacks 768 := saveWidth_frame h 768 (by decide)
  have bf (i : Fin 896) (hi : 784 ≤ i.val) : b.stacks i=a.stacks i := by
    rw [saveWidth_frame h i (by intro he; have hv:=congrArg Fin.val he; change i.val=783 at hv; omega),hhf i (by omega),hcf i]
    intro he; have hv:=congrArg Fin.val he; change i.val=782 at hv; omega
  have hc785 : c.stacks 785=a.stacks 785 := hcf 785 (by decide)
  have hc786 : c.stacks 786=a.stacks 786 := hcf 786 (by decide)
  refine ⟨nc+(nh+(2*(h.stacks 783).length+7*(h.stacks 768).length+8)),?_,b,
    hec.seq (heh.seq hsave),?_,bf⟩
  · have h783 := hhW 783
    have h768 := hhW 768
    dsimp only [startBudget]
    change nh ≤ H at hnh
    change nc ≤ C at hnc
    dsimp only [C,H] at *
    omega
  · constructor
    · intro i
      rw [saveWidth_frame h (workerStack i) (by
        intro he; have hh:=congrArg Fin.val he
        simp only [workerStack,Fin.val_castAdd] at hh
        have:=i.isLt; omega)]
      exact hwh i
    · intro j h0 h5 h6 h9
      change b.stacks (LeafProgram.HashParameters.ports.hash.stack j)=[]
      rw [saveWidth_frame h _ (by
        intro he; have hh:=congrArg Fin.val he
        have hj:=selector_port_val j; have:=j.isLt; omega)]
      exact hrh j h0 h5 h6 h9
    · rw [bf 785 (by decide)]
    · rw [saveWidth_frame h 782 (by decide),hhf 782 (by decide),hcm]
    · rw [bf 786 (by decide)]
    · rw [hb768,h0,hcm]
    · rw [saveWidth_frame h 773 (by decide),h5,hcm,hc786]
    · rw [saveWidth_frame h 774 (by decide),h6,hc785,hcm]
    · exact (saveWidth_value h).trans hb768.symm

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
