import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgramSource

namespace OAI.Algorithms

/-! One actual matrix coefficient call followed by physical signed framing. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- Prepend the two little-endian component frames, preserving coefficient order. -/
def emitPair : Code 288 := .seq (frame 280 284 286 (by decide)) (frame 279 284 286 (by decide))

theorem emitPair_eval (base : Fin 288 → List Bool) (hb : base 286=[])
    (regs : Fin 16 → Bool) (q : Store) :
    ∃ rf, Eval emitPair (8*(q.positive.length+q.negative.length)+18)
      (state base regs q) (state base rf {q with positive:=[],negative:=[], row:=Encoding.frame q.positive++Encoding.frame q.negative++q.row}) := by
  obtain ⟨a,ha,hsa⟩ := frame_eval (280 : Fin 288) 284 286
    (by decide) (by decide) (by decide) (state base regs q) (by simp [state,hb])
  let qa : Store := {q with negative:=[],row:=Encoding.frame q.negative++q.row}
  have hea : a=state base a.regs qa := by
    apply congrArg (StructuredProgram.State.mk a.regs)
    rw [hsa]
    simp only [state]
    change Function.update (Function.update (state base regs q).stacks 280 []) 284
      (Encoding.frame q.negative++q.row)=(state base a.regs qa).stacks
    rw [update_negative,update_row]
    rfl
  rw [hea] at ha
  obtain ⟨b,hb',hsb⟩ := frame_eval (279 : Fin 288) 284 286
    (by decide) (by decide) (by decide) (state base a.regs qa) (by simp [state,hb])
  have heb : b=state base b.regs {q with positive:=[],negative:=[], row:=Encoding.frame q.positive++Encoding.frame q.negative++q.row} := by
    apply congrArg (StructuredProgram.State.mk b.regs)
    rw [hsb]
    change Function.update (Function.update (state base a.regs qa).stacks 279 []) 284
      (Encoding.frame q.positive++qa.row)=_
    rw [update_positive,update_row]
    simp [state,qa,List.append_assoc]
  rw [heb] at hb'
  refine ⟨b.regs,?_⟩
  convert ha.seq hb' using 1
  all_goals first | rfl | (simp [state, qa]; omega)

def clearColumn : Code 288 := .call (StackRoutines.clearProgram 278 0 1)

theorem clearColumn_eval (base : Fin 288 → List Bool) (regs : Fin 16 → Bool) (q : Store) :
    Eval clearColumn (2*q.columnIndex.length+3) (state base regs q)
      (state base (readRegs regs 0 1 none) {q with columnIndex:=[]}) := by
  have h := Subexp.TupleProgram.clear_eval (278 : Fin 288) (0 : Fin 16) 1 (state base regs q)
  unfold clearColumn
  rw [show (state base regs q).stacks 278 = q.columnIndex by simp [state]] at h
  convert h using 1
  apply congrArg (StructuredProgram.State.mk (readRegs regs 0 1 none))
  exact (update_columnIndex base regs q []).symm

def coefficientStep (entry : Code 256) : Code 288 :=
  .seq (entryCall entry) (.seq emitPair clearColumn)

theorem coefficientStep_eval (entry : Code 256) (base : Fin 288 → List Bool)
    (hb : base 286=[]) (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → Pair → Prop) (T B : ℕ)
    (hc : EntryContract entry base Valid Rel T B) (regs : Fin 16 → Bool) (q : Store)
    (j v : ℕ) (hv : Valid j v) (hj : q.rowIndex=List.replicate j true)
    (hcol : q.columnIndex=List.replicate v true) (hp : q.positive=[]) (hn : q.negative=[]) :
    ∃ t ≤ T+8*B+2*v+22, ∃ rf result,
      Eval (coefficientStep entry) t (state base regs q)
        (state base rf {q with columnIndex:=[],positive:=[],negative:=[], row:=Encoding.frame result.1++Encoding.frame result.2++q.row}) ∧
      Rel j v result ∧ pairLength result ≤ B := by
  obtain ⟨t,ht,r,result,he,hr,hl⟩ := entryCall_eval entry base Valid Rel T B hc regs q j v hv hj hcol hp hn
  obtain ⟨r',hf⟩ := emitPair_eval base hb r {q with positive:=result.1,negative:=result.2}
  have hg := clearColumn_eval base r' {q with positive:=[],negative:=[], row:=Encoding.frame result.1++Encoding.frame result.2++q.row}
  refine ⟨t+((8*(result.1.length+result.2.length)+18)+(2*q.columnIndex.length+3)),?_,
    readRegs r' 0 1 none,result,he.seq (hf.seq hg),hr,hl⟩
  dsimp [pairLength] at hl
  rw [hcol,List.length_replicate]
  omega

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
