import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgramRowScan

namespace OAI.Algorithms

/-! Physical row preparation and output framing for all-D construction. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def copyRowIndex : Code 288 := .call (StackRoutines.copyProgram 281 277 285 0 1)
def copyIDs : Code 288 := .call (StackRoutines.copyProgram 282 283 285 0 1)
def emitRow : Code 288 := frame 284 24 286 (by decide)
def clearRowIndex : Code 288 := .call (StackRoutines.clearProgram 277 0 1)

theorem copyRowIndex_eval (base : Fin 288 → List Bool) (hb : base 285=[])
    (regs : Fin 16 → Bool) (q : Store) (hq : q.rowIndex=[]) :
    Eval copyRowIndex (7*q.remaining.length+5) (state base regs q)
      (state base (readRegs regs 0 1 none) {q with rowIndex:=q.remaining}) := by
  have h := Subexp.TupleProgram.copy_eval (281 : Fin 288) 277 285 (0 : Fin 16) 1
    (by decide) (by decide) (by decide) (by decide) (state base regs q) (by simp [state,hb])
  convert h using 1
  · rfl
  · simp [state]
  · apply congrArg (StructuredProgram.State.mk (readRegs regs 0 1 none))
    simp only [StackRoutines.copyStacks]
    simpa [state,hq] using (update_rowIndex base regs q q.remaining).symm

theorem copyIDs_eval (base : Fin 288 → List Bool) (hb : base 285=[])
    (regs : Fin 16 → Bool) (q : Store) (hq : q.todo=[]) :
    Eval copyIDs (7*q.reversedIDs.length+5) (state base regs q)
      (state base (readRegs regs 0 1 none) {q with todo:=q.reversedIDs}) := by
  have h := Subexp.TupleProgram.copy_eval (282 : Fin 288) 283 285 (0 : Fin 16) 1
    (by decide) (by decide) (by decide) (by decide) (state base regs q) (by simp [state,hb])
  convert h using 1
  · rfl
  · simp [state]
  · apply congrArg (StructuredProgram.State.mk (readRegs regs 0 1 none))
    simp only [StackRoutines.copyStacks]
    simpa [state,hq] using (update_todo base regs q q.reversedIDs).symm

theorem emitRow_eval (base : Fin 288 → List Bool) (hb : base 286=[])
    (regs : Fin 16 → Bool) (q : Store) :
    ∃ rf, Eval emitRow (8*q.row.length+9) (state base regs q)
      (state base rf {q with row:=[],matrix:=Encoding.frame q.row++q.matrix}) := by
  obtain ⟨e,he,hs⟩ := frame_eval (284 : Fin 288) 24 286
    (by decide) (by decide) (by decide) (state base regs q) (by simp [state,hb])
  have heq : e=state base e.regs {q with row:=[],matrix:=Encoding.frame q.row++q.matrix} := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    rw [hs]
    change Function.update (Function.update (state base regs q).stacks 284 []) 24
      (Encoding.frame q.row++q.matrix)=_
    rw [update_row,update_matrix]
    rfl
  rw [heq] at he
  exact ⟨e.regs,by simpa [emitRow,state] using he⟩

theorem clearRowIndex_eval (base : Fin 288 → List Bool) (regs : Fin 16 → Bool) (q : Store) :
    Eval clearRowIndex (2*q.rowIndex.length+3) (state base regs q)
      (state base (readRegs regs 0 1 none) {q with rowIndex:=[]}) := by
  have h := Subexp.TupleProgram.clear_eval (277 : Fin 288) (0 : Fin 16) 1 (state base regs q)
  convert h using 1
  · rfl
  · simp [state]
  · apply congrArg (StructuredProgram.State.mk (readRegs regs 0 1 none))
    exact (update_rowIndex base regs q []).symm

theorem pairWords_length_le {Rel : ℕ → Pair → Prop} {js : List ℕ} {ps : List Pair}
    {B : ℕ} (h : List.Forall₂ (fun v p => Rel v p ∧ pairLength p ≤ B) js ps) :
    (pairWords ps).length ≤ 2*js.length*B+2*js.length := by
  induction h with
  | nil => simp [pairWords]
  | @cons v p vs ps hp ht ih =>
    simp only [pairWords,List.length_append,Encoding.length_frame,List.length_cons]
    dsimp [pairLength] at hp
    nlinarith [hp.2]

def rowBody (entry : Code 256) : Code 288 :=
  .seq copyRowIndex (.seq copyIDs (.seq (rowScan entry) (.seq emitRow clearRowIndex)))

def rowBodyCost (T B n j H h : ℕ) : ℕ :=
  9*j+7*H+h*(T+24*B+8*n+45)+25

theorem rowBody_eval (entry : Code 256) (base : Fin 288 → List Bool)
    (hb : base 285=[]) (hb' : base 286=[])
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → Pair → Prop) (T B : ℕ)
    (hc : EntryContract entry base Valid Rel T B) (j n : ℕ) (js : List ℕ)
    (hvalid : ∀ v ∈ js, Valid j v) (hbound : ∀ v ∈ js, v ≤ n)
    (regs : Fin 16 → Bool) (q : Store)
    (hj : q.remaining=List.replicate j true) (hids : q.reversedIDs=ids js.reverse)
    (hr : q.rowIndex=[]) (hcol : q.columnIndex=[]) (hp : q.positive=[]) (hn : q.negative=[])
    (htodo : q.todo=[]) (hrow : q.row=[]) :
    ∃ t ≤ rowBodyCost T B n j (ids js.reverse).length js.length, ∃ rf ps,
      Eval (rowBody entry) t (state base regs q)
        (state base rf {q with rowIndex:=[],columnIndex:=[],positive:=[],negative:=[],todo:=[],row:=[], matrix:=Encoding.frame (pairWords ps)++q.matrix}) ∧
      List.Forall₂ (fun v p => Rel j v p ∧ pairLength p ≤ B) js ps := by
  have hcopy := copyRowIndex_eval base hb regs q hr
  let q₁ : Store := {q with rowIndex:=q.remaining}
  let r₁ := readRegs regs 0 1 none
  have hcopy' := copyIDs_eval base hb r₁ q₁ htodo
  let q₂ : Store := {q₁ with todo:=q.reversedIDs}
  let r₂ := readRegs r₁ 0 1 none
  obtain ⟨ts,hts,rs,ps,hes,hps⟩ := rowScan_eval entry base hb' Valid Rel T B hc j js.reverse
    (fun v hv => hvalid v (by simpa using hv)) r₂ q₂ hj hcol hp hn hids
  have hrel : List.Forall₂ (fun v p => Rel j v p ∧ pairLength p ≤ B) js ps.reverse := by
    simpa using List.rel_reverse hps
  have hlen := pairWords_length_le hrel
  let q₃ : Store := {q₂ with columnIndex:=[],positive:=[],negative:=[],todo:=[], row:=pairWords ps.reverse++q.row}
  obtain ⟨re,hee⟩ := emitRow_eval base hb' rs q₃
  let q₄ : Store := {q₃ with row:=[],matrix:=Encoding.frame q₃.row++q₃.matrix}
  have hec := clearRowIndex_eval base re q₄
  have hscan := rowScanCost_le T B n js.reverse (fun v hv => hbound v (by simpa using hv))
  refine ⟨(7*q.remaining.length+5)+((7*q.reversedIDs.length+5)+
    (ts+((8*q₃.row.length+9)+(2*q₄.rowIndex.length+3)))),?_,
    readRegs re 0 1 none,ps.reverse,?_,hrel⟩
  · simp only [List.length_reverse] at hscan
    dsimp [q₄,q₃,q₂,q₁,rowBodyCost]
    rw [hj,hids,hrow,List.append_nil,List.length_replicate]
    nlinarith
  · simpa [rowBody,q₄,q₃,q₂,q₁,r₂,r₁,hrow] using
      hcopy.seq (hcopy'.seq (hes.seq (hee.seq hec)))

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
