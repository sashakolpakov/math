import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgramBranches

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def chooseMarked : Code := .ite 7 markedBranch neutralBranch
def foreignBranch : Code := .seq (test true) (.ite 3 chooseMarked neutralBranch)
def dispatch : Code := .seq (test false) (.ite 3 hashBranch foreignBranch)

def selectedPayload (rows clauses : List (List Bool)) (hasMarked : Bool) (m f : ℕ) : List Bool :=
  if f < rows.length then rows.getD f []
  else if hasMarked && decide (f=rows.length) then clauses.getD m [] else []

def branchBound (rows clauses : List (List Bool)) (m f : ℕ) :=
  2*f+7*m+23*((Encoding.encodeList id rows).length+(Encoding.encodeList id clauses).length)+38

def dispatchBound (rows clauses : List (List Bool)) (m f : ℕ) :=
  2*(13*f+9*rows.length+45)+branchBound rows clauses m f+3

def TestClean (d : Data) : Prop := d.stacks 8=[] ∧ d.stacks 9=[] ∧ d.stacks 14=[]

theorem Finished.rebase {d a e : Data} {isHash isMarked : Bool} {bits : List Bool}
    (hs : a.stacks=d.stacks) (hr : a.regs 7=d.regs 7) (h : Finished a e isHash isMarked bits) :
    Finished d e isHash isMarked bits := by
  rcases h with ⟨he,h5,h6,h7⟩
  exact ⟨by simpa [finishedStacks,hs] using he,h5,h6,h7.trans hr⟩

theorem dispatch_eval (d : Data) (rows clauses : List (List Bool))
    (hasMarked : Bool) (m f : ℕ)
    (hrows : d.stacks 0=Encoding.encodeList id rows)
    (hclauses : d.stacks 1=Encoding.encodeList id clauses)
    (hcount : d.stacks 3=unary rows.length)
    (hmark : hasMarked=true → d.stacks 4=Encoding.encodeNat m)
    (hid : d.stacks 6=Encoding.encodeNat f)
    (hflag : d.regs 7=hasMarked)
    (hvalid : hasMarked=true → m < clauses.length)
    (hc : FetchClean d) (ht : TestClean d) :
    ∃ n e, n ≤ dispatchBound rows clauses m f ∧ Eval dispatch n d e ∧
      Finished d e (decide (f < rows.length)) (hasMarked && decide (f=rows.length))
        (selectedPayload rows clauses hasMarked m f) := by
  obtain ⟨n1,a,hn1,he1,ha3,has,har⟩ := test_eval d f rows.length false hid hcount ht.1 ht.2.1 ht.2.2
  have ha7 : a.regs 7=d.regs 7 := har 7 (by decide)
  have hac : FetchClean a := by simpa [FetchClean,has] using hc
  have hat : TestClean a := by simpa [TestClean,has] using ht
  by_cases hf : f < rows.length
  · have haf : a.regs 3=true := by simpa [hf] using ha3
    let i : Fin rows.length := ⟨f,hf⟩
    obtain ⟨nb,e,hnb,heb,hfin⟩ := hashBranch_eval a rows i
      (by simpa [has] using hrows) (by simpa [has,i] using hid) hac
    refine ⟨n1+(nb+1),e,?_,he1.seq (Eval.ite_true haf heb),?_⟩
    · unfold dispatchBound branchBound; omega
    · have hr := hfin.rebase has ha7
      have hne : f≠rows.length := by omega
      simpa [selectedPayload,hf,hne,i,List.getD_eq_getElem _ _ hf] using hr
  · have haf : a.regs 3=false := by simpa [hf] using ha3
    obtain ⟨n2,b,hn2,he2,hb3,hbs,hbr⟩ := test_eval a f rows.length true
      (by simpa [has] using hid) (by simpa [has] using hcount) hat.1 hat.2.1 hat.2.2
    have hbs' : b.stacks=d.stacks := hbs.trans has
    have hb7 : b.regs 7=d.regs 7 := (hbr 7 (by decide)).trans ha7
    have hbc : FetchClean b := by simpa [FetchClean,hbs'] using hc
    by_cases heq : f=rows.length
    · have hbf : b.regs 3=true := by simpa [heq] using hb3
      cases hm : hasMarked with
      | false =>
        have hbm : b.regs 7=false := hb7.trans (hflag.trans hm)
        obtain ⟨e,he,hfin⟩ := neutralBranch_eval b f (by simpa [hbs'] using hid)
          (by simpa [hbs'] using hc 15 (by decide))
        refine ⟨n1+((n2+((2*f+7+1)+1))+1),e,?_,
          he1.seq (Eval.ite_false haf (he2.seq (Eval.ite_true hbf (Eval.ite_false hbm he)))),?_⟩
        · unfold dispatchBound branchBound; omega
        · have hr := hfin.rebase hbs' hb7
          simpa [selectedPayload,hf,hm] using hr
      | true =>
        have hbm : b.regs 7=true := hb7.trans (hflag.trans hm)
        let i : Fin clauses.length := ⟨m,hvalid hm⟩
        obtain ⟨nb,e,hnb,heb,hfin⟩ := markedBranch_eval b clauses i f
          (by simpa [hbs'] using hclauses) (by simpa [hbs'] using hid)
          (by simpa [hbs',i] using hmark hm) hbc (by simpa [hbs'] using ht.2.2)
        refine ⟨n1+((n2+((nb+1)+1))+1),e,?_,
          he1.seq (Eval.ite_false haf (he2.seq (Eval.ite_true hbf (Eval.ite_true hbm heb)))),?_⟩
        · dsimp [i] at hnb; unfold dispatchBound branchBound; omega
        · have hr := hfin.rebase hbs' hb7
          simpa [selectedPayload,hf,hm,heq,i,List.getElem?_eq_getElem (hvalid hm)] using hr
    · have hnle : ¬f < rows.length+1 := by omega
      have hbf : b.regs 3=false := by simpa [hnle] using hb3
      obtain ⟨e,he,hfin⟩ := neutralBranch_eval b f (by simpa [hbs'] using hid)
        (by simpa [hbs'] using hc 15 (by decide))
      refine ⟨n1+((n2+(2*f+7+1))+1),e,?_,
        he1.seq (Eval.ite_false haf (he2.seq (Eval.ite_false hbf he))),?_⟩
      · unfold dispatchBound branchBound; omega
      · have hr := hfin.rebase hbs' hb7
        simpa [selectedPayload,hf,heq] using hr

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
