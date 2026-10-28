import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgramRow

namespace OAI.Algorithms

/-! Fixed nested traversal: descending unary rows and reversed original head
IDs, with prepending restoring the requested row and column order. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def rowsWords (rows : List (List Pair)) : List Bool :=
  Subexp.MatrixProgramSupport.words (rows.map pairWords)

@[simp] theorem rowsWords_append (a b : List (List Pair)) :
    rowsWords (a++b)=rowsWords a++rowsWords b := by
  simp [rowsWords,Subexp.MatrixProgramSupport.words_append]

def counter : UnaryForPrograms.Ports 16 288 := ⟨281,0,1⟩
def rowLoop (entry : Code 256) : Code 288 := UnaryForPrograms.forCmd counter (rowBody entry)

theorem popped_state (base : Fin 288 → List Bool) (regs : Fin 16 → Bool) (q : Store) :
    UnaryForPrograms.popped counter (state base regs q)=
      state base (readRegs regs 0 1 q.remaining.head?) {q with remaining:=q.remaining.tail} := by
  apply congrArg (StructuredProgram.State.mk (readRegs regs 0 1 q.remaining.head?))
  change Function.update (state base regs q).stacks 281 q.remaining.tail = _
  exact update_remaining base regs q q.remaining.tail

theorem rowLoop_visits (entry : Code 256) (base : Fin 288 → List Bool)
    (hb : base 285=[]) (hb' : base 286=[])
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → Pair → Prop) (T B : ℕ)
    (hc : EntryContract entry base Valid Rel T B) (D n : ℕ) (js : List ℕ)
    (hvalid : ∀ j < D, ∀ v ∈ js, Valid j v) (hbound : ∀ v ∈ js, v ≤ n)
    (k : ℕ) (hk : k ≤ D) (regs : Fin 16 → Bool) (q : Store)
    (hrem : q.remaining=List.replicate k true) (hids : q.reversedIDs=ids js.reverse)
    (hr : q.rowIndex=[]) (hcol : q.columnIndex=[]) (hp : q.positive=[]) (hn : q.negative=[])
    (htodo : q.todo=[]) (hrow : q.row=[]) :
    ∃ costs t rf rows,
      UnaryForPrograms.Visits counter (rowBody entry) costs t (state base regs q)
        (state base rf {q with remaining:=[],matrix:=rowsWords rows++q.matrix}) ∧
      List.Forall₂ (fun j row => List.Forall₂ (fun v p => Rel j v p ∧ pairLength p ≤ B) js row)
        (List.range k) rows ∧
      t ≤ k*(rowBodyCost T B n D (ids js.reverse).length js.length+2)+2 := by
  induction k generalizing regs q with
  | zero =>
    have hq : q.remaining=[] := by simpa using hrem
    refine ⟨[],2,readRegs regs 0 1 none,[],?_,.nil,by simp⟩
    have hv := UnaryForPrograms.Visits.done (p:=counter) (body:=rowBody entry)
      (state base regs q) (by simp [state,counter,hq])
    simpa [popped_state,hq,rowsWords,Subexp.MatrixProgramSupport.words] using hv
  | succ k ih =>
    let qp : Store := {q with remaining:=List.replicate k true}
    let rp := readRegs regs 0 1 (some true)
    have hpop : UnaryForPrograms.popped counter (state base regs q)=state base rp qp := by
      rw [popped_state,hrem]
      simp [rp,qp,List.replicate_succ]
    obtain ⟨tb,htb,rb,row,heb,hrel⟩ := rowBody_eval entry base hb hb' Valid Rel T B hc k n js
      (hvalid k (by omega)) hbound rp qp rfl hids hr hcol hp hn htodo hrow
    let qb : Store := {q with remaining:=List.replicate k true, matrix:=Encoding.frame (pairWords row)++q.matrix}
    have heb' : Eval (rowBody entry) tb (UnaryForPrograms.popped counter (state base regs q))
        (state base rb qb) := by
      rw [hpop]
      simpa [qp,qb,hr,hcol,hp,hn,htodo,hrow] using heb
    obtain ⟨costs,tt,rf,rows,hvis,hrels,htt⟩ := ih (by omega) rb qb rfl hids
      hr hcol hp hn htodo hrow
    refine ⟨tb::costs,tb+tt+2,rf,rows++[row],?_,?_,?_⟩
    · have hv := UnaryForPrograms.Visits.step
        (d:=state base regs q) (e:=state base rb qb)
        (by simp [state,counter,hrem,List.replicate_succ]) heb'
        (by rw [hpop]; rfl) hvis
      simpa [qb,rowsWords_append,rowsWords,Subexp.MatrixProgramSupport.words,Subexp.MatrixProgramSupport.words_append,List.append_assoc] using hv
    · simpa [List.range_succ] using List.rel_append hrels (List.Forall₂.cons hrel List.Forall₂.nil)
    · have hm : rowBodyCost T B n k (ids js.reverse).length js.length ≤
          rowBodyCost T B n D (ids js.reverse).length js.length := by
        unfold rowBodyCost
        omega
      nlinarith

theorem rowLoop_eval (entry : Code 256) (base : Fin 288 → List Bool)
    (hb : base 285=[]) (hb' : base 286=[])
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → Pair → Prop) (T B : ℕ)
    (hc : EntryContract entry base Valid Rel T B) (D n : ℕ) (js : List ℕ)
    (hvalid : ∀ j < D, ∀ v ∈ js, Valid j v) (hbound : ∀ v ∈ js, v ≤ n)
    (regs : Fin 16 → Bool) (q : Store)
    (hrem : q.remaining=List.replicate D true) (hids : q.reversedIDs=ids js.reverse)
    (hr : q.rowIndex=[]) (hcol : q.columnIndex=[]) (hp : q.positive=[]) (hn : q.negative=[])
    (htodo : q.todo=[]) (hrow : q.row=[]) :
    ∃ t ≤ D*(rowBodyCost T B n D (ids js.reverse).length js.length+2)+2, ∃ rf rows,
      Eval (rowLoop entry) t (state base regs q)
        (state base rf {q with remaining:=[],matrix:=rowsWords rows++q.matrix}) ∧
      List.Forall₂ (fun j row => List.Forall₂ (fun v p => Rel j v p ∧ pairLength p ≤ B) js row)
        (List.range D) rows := by
  obtain ⟨costs,t,rf,rows,hv,hr,ht⟩ := rowLoop_visits entry base hb hb' Valid Rel T B hc D n js
    hvalid hbound D le_rfl regs q hrem hids hr hcol hp hn htodo hrow
  exact ⟨t,ht,rf,rows,hv.eval,hr⟩

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
