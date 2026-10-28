import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgramTest

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def emit : Code := .seq (copy 39 34)
  (.seq (Subexp.SupportSelectionProgram.emit 0 (by decide)) (Subexp.TupleProgram.pushConst 1 0 false))

theorem emit_eval (d : Data) (j : ℕ) (hj : d.stacks 39=unary j) (hc : Clean d) :
    ∃ e, Eval emit (12*j+14) d e ∧
      e.stacks=Function.update (Function.update d.stacks 0 (record j++d.stacks 0))
        1 (false::d.stacks 1) := by
  let a := afterCopy d 39 34 0 1
  have h1 : Eval (copy 39 34) (7*j+5) d a := by
    have he := copy_eval d 39 34 42 0 1 (by decide) (by decide) (by decide) (by decide)
      (hc 42 (by decide))
    simpa [copy,Subexp.SupportSelectionProgram.copy,a,afterCopy,hj] using he
  have ha : a.stacks 34=unary j := by
    simp [a,afterCopy,StackRoutines.copyStacks,hj,hc 34 (by decide)]
  obtain ⟨b,h2,hb⟩ := Subexp.SupportSelectionProgram.emit_eval 0 (by decide) a j ha
  let e := Subexp.TupleProgram.pushedState 1 0 false b
  have h3 := Subexp.TupleProgram.pushConst_eval (1 : Fin 64) (0 : Fin 16) false b
  refine ⟨e,?_,?_⟩
  · have he := h1.seq (h2.seq h3)
    convert he using 1 <;> first | rfl | omega
  · funext i
    by_cases hi : i=34
    · subst i; simp [e,hb,a,afterCopy,StackRoutines.copyStacks,hc 34 (by decide)]
    · simp [e,hb,a,afterCopy,StackRoutines.copyStacks,
        Function.update_apply,hi,record]

def choose : Code := .ite 6 (.ite 4 emit (.base .skip)) (.base .skip)

theorem choose_eval (d : Data) (j : ℕ) (hj : d.stacks 39=unary j) (hc : Clean d) :
    ∃ ticks e, ticks ≤ 12*j+16 ∧ Eval choose ticks d e ∧
      e.stacks=Function.update (Function.update d.stacks 0
        (if d.regs 6 && d.regs 4 then record j++d.stacks 0 else d.stacks 0))
        1 (if d.regs 6 && d.regs 4 then false::d.stacks 1 else d.stacks 1) := by
  cases hl : d.regs 6 with
  | false =>
      refine ⟨1,d,by omega,Eval.ite_false hl (.base (.skip d)),?_⟩
      simp []
  | true =>
      cases hh : d.regs 4 with
      | false =>
          refine ⟨2,d,by omega,Eval.ite_true hl (Eval.ite_false hh (.base (.skip d))),?_⟩
          simp []
      | true =>
          obtain ⟨e,he,hs⟩ := emit_eval d j hj hc
          refine ⟨12*j+16,e,le_rfl,?_,?_⟩
          · simpa [choose,Nat.add_assoc] using Eval.ite_true hl (Eval.ite_true hh he)
          · simpa [hl,hh] using hs

def visit : Code := .seq test choose

def visitBound (j W L z : ℕ) := lookupCost j W+22*j+9*L+10*z+2*W+43

theorem visit_eval (d : Data) (earlier : List (List Bool)) (word rest : List Bool) (j : ℕ)
    (hs : d.stacks 33=earlier.flatten++(word++rest)) (hj : d.stacks 39=unary j)
    (hi : j=earlier.length) (hw : word.length=(d.stacks 38).length)
    (hr : ∀ row ∈ earlier,row.length=(d.stacks 38).length) (hc : Clean d) :
    ∃ ticks e, ticks ≤ visitBound j (d.stacks 38).length (d.stacks 31).length (d.stacks 32).length ∧
      Eval visit ticks d e ∧
      e.stacks=Function.update (Function.update d.stacks 0
        (if (d.stacks 31).getD j false && word.getD (d.stacks 32).length false
          then record j++d.stacks 0 else d.stacks 0))
        1 (if (d.stacks 31).getD j false && word.getD (d.stacks 32).length false
          then false::d.stacks 1 else d.stacks 1) := by
  let a := tested d ((d.stacks 31).getD j false) (word.getD (d.stacks 32).length false)
  have ht : Eval test
      (testCost (d.stacks 39) (d.stacks 31) (d.stacks 32) word (d.stacks 38).length) d a := by
    simpa [a,hj] using test_eval d earlier word rest hs (by simp [hj,hi]) hw hr hc
  obtain ⟨nc,e,hnc,he,hse⟩ := choose_eval a j hj hc
  refine ⟨_,e,?_,ht.seq he,?_⟩
  · have hb := testCost_bound (d.stacks 39) (d.stacks 31) (d.stacks 32) word _ hw
    have hlength : (d.stacks 39).length=j := by simp [hj]
    rw [hlength] at hb
    unfold visitBound
    omega
  · simpa [a,tested,readRegs] using hse

/-- Only outputs 0 and 1 change; the work invariant is restored. -/
theorem clean_outputs (d e : Data) (hc : Clean d) (xs ys : List Bool)
    (hs : e.stacks=Function.update (Function.update d.stacks 0 xs) 1 ys) : Clean e := by
  intro i hi
  have h0 : i ≠ 0 := by intro h; subst i; simp at hi
  have h1 : i ≠ 1 := by intro h; subst i; simp at hi
  simpa [hs,h0,h1] using hc i hi

def predicate (rows : List (List Bool)) (low : List Bool) (z j : ℕ) : Bool :=
  low.getD j false && (rows.getD j []).getD z false

/-- Row selection is by the original array index, including rows not covered
by a complete packing block. -/
theorem visit_row (rows : List (List Bool)) (low : List Bool) (W z j : ℕ) (d : Data)
    (hrows : ∀ row ∈ rows,row.length=W) (hlt : j < rows.length)
    (hs : d.stacks 33=rows.flatten) (hl : d.stacks 31=low)
    (hz : d.stacks 32=unary z) (hw : d.stacks 38=unary W)
    (hj : d.stacks 39=unary j) (hc : Clean d) :
    ∃ ticks e, ticks ≤ visitBound j W low.length z ∧ Eval visit ticks d e ∧
      e.stacks=Function.update (Function.update d.stacks 0
        (if predicate rows low z j then record j++d.stacks 0 else d.stacks 0))
        1 (if predicate rows low z j then false::d.stacks 1 else d.stacks 1) := by
  have hsplit := List.take_append_drop j rows
  rw [List.drop_eq_getElem_cons hlt] at hsplit
  have hsource : d.stacks 33=(rows.take j).flatten++(rows[j]++(rows.drop (j+1)).flatten) := by
    exact hs.trans (by
      simpa only [List.flatten_append,List.flatten_cons,List.append_assoc] using
        congrArg List.flatten hsplit.symm)
  have hlen : j=(rows.take j).length := by simp [List.length_take,Nat.min_eq_left hlt.le]
  have hword : rows[j].length=(d.stacks 38).length := by
    simpa [hw] using hrows rows[j] (List.getElem_mem hlt)
  have hearlier : ∀ row ∈ rows.take j,row.length=(d.stacks 38).length := by
    intro row hr
    simpa [hw] using hrows row (List.mem_of_mem_take hr)
  obtain ⟨ticks,e,ht,he,hs'⟩ := visit_eval d (rows.take j) rows[j] (rows.drop (j+1)).flatten j
    hsource hj hlen hword hearlier hc
  refine ⟨ticks,e,?_,he,?_⟩
  · simpa [hw,hl,hz] using ht
  · have hget : rows.getD j []=rows[j] := List.getD_eq_getElem _ _ hlt
    simpa only [predicate,hl,hz,List.length_replicate,hget] using hs'

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
