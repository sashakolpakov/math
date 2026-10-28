import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgramRowStep

namespace OAI.Algorithms

/-! Paid traversal of the explicit original-column identifier records. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def ids (js : List ℕ) : List Bool :=
  ProgramEncoding.encodeRecords (js.map fun j => List.replicate j true)

def pairWords : List Pair → List Bool
  | [] => []
  | p::ps => Encoding.frame p.1 ++ Encoding.frame p.2 ++ pairWords ps

@[simp] theorem pairWords_append (ps qs : List Pair) :
    pairWords (ps++qs)=pairWords ps++pairWords qs := by
  induction ps with
  | nil => simp [pairWords]
  | cons p ps ih => simp [pairWords,ih,List.append_assoc]

def rowScan (entry : Code 256) : Code 288 :=
  .seq (parse 283 278 (by decide))
    (.while 2 (.seq (coefficientStep entry) (parse 283 278 (by decide))))

def rowScanCost (T B : ℕ) : List ℕ → ℕ
  | [] => 3
  | v::vs => T+8*B+8*v+29+rowScanCost T B vs

private theorem parsed_state (base : Fin 288 → List Bool) (regs rf : Fin 16 → Bool)
    (q : Store) (tail bits : List Bool) :
    parsed 283 278 (state base regs q) rf tail bits =
      state base rf {q with todo:=tail,columnIndex:=bits} := by
  apply congrArg (StructuredProgram.State.mk rf)
  change Function.update (Function.update (state base regs q).stacks 283 tail) 278 bits = _
  rw [update_todo,update_columnIndex]
  rfl

theorem rowScan_eval (entry : Code 256) (base : Fin 288 → List Bool) (hb : base 286=[])
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → Pair → Prop) (T B : ℕ)
    (hc : EntryContract entry base Valid Rel T B) (j : ℕ) (js : List ℕ)
    (hvalid : ∀ v ∈ js, Valid j v) (regs : Fin 16 → Bool) (q : Store)
    (hj : q.rowIndex=List.replicate j true) (hcol : q.columnIndex=[])
    (hp : q.positive=[]) (hn : q.negative=[]) (htodo : q.todo=ids js) :
    ∃ t ≤ rowScanCost T B js, ∃ rf ps,
      Eval (rowScan entry) t (state base regs q)
        (state base rf {q with columnIndex:=[],positive:=[],negative:=[],todo:=[], row:=pairWords ps.reverse++q.row}) ∧
      List.Forall₂ (fun v p => Rel j v p ∧ pairLength p ≤ B) js ps := by
  induction js generalizing regs q with
  | nil =>
    obtain ⟨rf,hg,he⟩ := parse_nil (283 : Fin 288) 278 (by decide) (state base regs q) []
      (by simpa [state,ids,ProgramEncoding.encodeRecords, Encoding.encodeList] using htodo)
      (by simpa [state] using hcol)
    rw [parsed_state] at he
    refine ⟨3,le_rfl,rf,[],?_,.nil⟩
    have hw := he.seq (Eval.while_false (body:=.seq (coefficientStep entry)
      (parse 283 278 (by decide))) hg)
    simpa [rowScan,pairWords,hp,hn] using hw
  | cons v vs ih =>
    obtain ⟨r₁,hg,hparse⟩ := parse_cons (283 : Fin 288) 278 (by decide)
      (state base regs q) (List.replicate v true) (ids vs)
      (by simpa [state,ids,ProgramEncoding.encodeRecords, Encoding.encodeList] using htodo)
      (by simpa [state] using hcol)
    rw [parsed_state] at hparse
    simp only [List.reverse_replicate] at hparse
    let q₁ : Store := {q with todo:=ids vs,columnIndex:=List.replicate v true}
    obtain ⟨ta,hta,r₂,p,he,hr,hl⟩ := coefficientStep_eval entry base hb Valid Rel T B hc r₁ q₁
      j v (hvalid v (by simp)) hj rfl hp hn
    let q₂ : Store := {q with todo:=ids vs,columnIndex:=[],positive:=[],negative:=[], row:=Encoding.frame p.1++Encoding.frame p.2++q.row}
    obtain ⟨tt,htt,r₃,ps,ht,hps⟩ := ih (fun w hw => hvalid w (by simp [hw])) r₂ q₂
      hj rfl rfl rfl rfl
    cases ht with
    | seq hnext hwhile =>
      rename_i tn tw between
      refine ⟨(6*v+6)+(ta+tn+tw+1),?_,r₃,p::ps,?_,.cons ⟨hr,hl⟩ hps⟩
      · simp only [rowScanCost] at htt ⊢
        omega
      · have hall := hparse.seq (Eval.while_true hg (he.seq hnext) hwhile)
        simpa [rowScan,q₁,q₂,pairWords,List.reverse_cons,List.append_assoc] using hall

theorem rowScanCost_le (T B n : ℕ) (js : List ℕ) (h : ∀ v ∈ js, v ≤ n) :
    rowScanCost T B js ≤ js.length*(T+8*B+8*n+29)+3 := by
  induction js with
  | nil => simp [rowScanCost]
  | cons v vs ih =>
    have hv := h v (by simp)
    have ht := ih (fun w hw => h w (by simp [hw]))
    simp only [rowScanCost,List.length_cons]
    nlinarith

theorem pairWords_length (ps : List Pair) :
    (pairWords ps).length = 2*(ps.map pairLength).sum+2*ps.length := by
  induction ps with
  | nil => simp [pairWords]
  | cons p ps ih =>
    simp [pairWords,Encoding.length_frame,pairLength,ih]
    omega

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
