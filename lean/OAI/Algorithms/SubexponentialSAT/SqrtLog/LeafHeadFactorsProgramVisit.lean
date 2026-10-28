import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgramTest

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def natRecord (j : ℕ) : List Bool := true :: Encoding.frame (Encoding.encodeNat j)

theorem emitFrame_eval (d : Data) (bits : List Bool) (hv : d.stacks 34 = bits.reverse) :
    ∃ e, Eval (Subexp.SupportSelectionProgram.emit 0 (by decide)) (5 * bits.length + 7) d e ∧
      e.stacks = Function.update (Function.update d.stacks 34 []) 0
        ((true :: Encoding.frame bits) ++ d.stacks 0) := by
  let a := Subexp.TupleProgram.pushedState 0 0 false d
  let b := Subexp.TupleProgram.escapedState (Subexp.SupportSelectionProgram.emitPorts 0 (by decide)) a
  let e := Subexp.TupleProgram.pushedState 0 0 true b
  have h1 := Subexp.TupleProgram.pushConst_eval (0 : Fin 64) (0 : Fin 16) false d
  have h2 := Subexp.TupleProgram.escape_eval_state (Subexp.SupportSelectionProgram.emitPorts 0 (by decide)) a
  have h3 := Subexp.TupleProgram.pushConst_eval (0 : Fin 64) (0 : Fin 16) true b
  refine ⟨e, ?_, ?_⟩
  · have he := h1.seq (h2.seq h3)
    change Eval (Subexp.SupportSelectionProgram.emit 0 (by decide)) _ d e at he
    convert he using 1
    simp [a, Subexp.SupportSelectionProgram.emitPorts, hv]
    ; omega
  · funext i
    by_cases h0 : i = 0
    · subst i
      simp [e, b, a,
        Subexp.SupportSelectionProgram.emitPorts, hv, Subexp.TupleProgram.frame_eq_escaped,
        List.append_assoc]
    by_cases h34 : i = 34
    · subst i
      simp [e, b, a,
        Subexp.SupportSelectionProgram.emitPorts]
    · simp [e, b, a,
        Subexp.SupportSelectionProgram.emitPorts, h0, h34]

def emit : Code := .seq (copy 39 34)
  (.seq (Subexp.TupleProgram.pushConst 34 0 false)
    (.seq (Subexp.SupportSelectionProgram.emit 0 (by decide))
      (Subexp.TupleProgram.pushConst 1 0 false)))

theorem emit_eval (d : Data) (j : ℕ) (hj : d.stacks 39 = unary j) (hc : Clean d) :
    ∃ e, Eval emit (12 * j + 21) d e ∧
      e.stacks = Function.update (Function.update d.stacks 0 (natRecord j ++ d.stacks 0))
        1 (false :: d.stacks 1) := by
  let a := afterCopy d 39 34 0 1
  have h1 : Eval (copy 39 34) (7 * j + 5) d a := by
    simpa [copy,Subexp.SupportSelectionProgram.copy,a,afterCopy,hj] using
      copy_eval d 39 34 42 0 1 (by decide) (by decide) (by decide) (by decide)
        (hc 42 (by decide))
  let b := Subexp.TupleProgram.pushedState 34 0 false a
  have h2 := Subexp.TupleProgram.pushConst_eval (34 : Fin 64) (0 : Fin 16) false a
  have hb : b.stacks 34 = (Encoding.encodeNat j).reverse := by
    simp [b, a, afterCopy, StackRoutines.copyStacks,
      hj, hc 34 (by decide), Encoding.encodeNat, List.reverse_append]
  obtain ⟨c, h3, hcs⟩ := emitFrame_eval b (Encoding.encodeNat j) hb
  let e := Subexp.TupleProgram.pushedState 1 0 false c
  have h4 := Subexp.TupleProgram.pushConst_eval (1 : Fin 64) (0 : Fin 16) false c
  refine ⟨e, ?_, ?_⟩
  · have he := h1.seq (h2.seq (h3.seq h4))
    convert he using 1 <;> simp [emit] ; omega
  · funext i
    by_cases h34 : i = 34
    · subst i
      simp [e, hcs, b, a, afterCopy,
        StackRoutines.copyStacks, hc 34 (by decide)]
    · by_cases h0 : i = 0
      · subst i; simp [e, hcs, b, a, afterCopy,
          StackRoutines.copyStacks, natRecord]
      by_cases h1 : i = 1
      · subst i; simp [e, hcs, b, a, afterCopy,
          StackRoutines.copyStacks, natRecord]
      · simp [e, hcs, b, a, afterCopy,
          StackRoutines.copyStacks, h34, h0, h1, natRecord]

def choose : Code := .ite 4 emit (.base .skip)

theorem choose_eval (d : Data) (j : ℕ) (hj : d.stacks 39 = unary j) (hc : Clean d) :
    ∃ ticks e, ticks ≤ 12 * j + 22 ∧ Eval choose ticks d e ∧
      e.stacks = Function.update (Function.update d.stacks 0
        (if d.regs 4 then natRecord j ++ d.stacks 0 else d.stacks 0))
        1 (if d.regs 4 then false :: d.stacks 1 else d.stacks 1) := by
  cases hh : d.regs 4 with
  | false =>
    refine ⟨1, d, by omega, Eval.ite_false hh (.base (.skip d)), ?_⟩
    simp []
  | true =>
    obtain ⟨e, he, hs⟩ := emit_eval d j hj hc
    refine ⟨12 * j + 22, e, le_rfl, ?_, ?_⟩
    · simpa [choose, Nat.add_assoc] using Eval.ite_true hh he
    · simpa [hh] using hs

def visit : Code := .seq test choose
def visitBound (A j W z : ℕ) :=
  lookupCost (A + j) W + 9 * (A + j) + 12 * j + 10 * z + 2 * W + 46

theorem visit_eval (d : Data) (earlier : List (List Bool)) (word rest : List Bool) (A j : ℕ)
    (hs : d.stacks 33 = earlier.flatten ++ (word ++ rest))
    (hA : d.stacks 31 = unary A) (hj : d.stacks 39 = unary j)
    (hi : A + j = earlier.length) (hw : word.length = (d.stacks 38).length)
    (hr : ∀ row ∈ earlier, row.length = (d.stacks 38).length) (hc : Clean d) :
    ∃ ticks e, ticks ≤ visitBound A j (d.stacks 38).length (d.stacks 32).length ∧
      Eval visit ticks d e ∧
      e.stacks = Function.update (Function.update d.stacks 0
        (if word.getD (d.stacks 32).length false then natRecord j ++ d.stacks 0 else d.stacks 0))
        1 (if word.getD (d.stacks 32).length false then false :: d.stacks 1 else d.stacks 1) := by
  let a := tested d (word.getD (d.stacks 32).length false)
  have ht : Eval test (testCost A j (d.stacks 38).length (d.stacks 32) word) d a := by
    simpa [a, hA, hj] using test_eval d earlier word rest hs (by simpa [hA, hj] using hi) hw hr hc
  obtain ⟨nc, e, hnc, he, hse⟩ := choose_eval a j hj hc
  refine ⟨_, e, ?_, ht.seq he, ?_⟩
  · have hb := testCost_bound A j (d.stacks 38).length (d.stacks 32) word hw
    unfold visitBound
    omega
  · simpa [a, tested, readRegs] using hse

theorem clean_outputs (d e : Data) (hc : Clean d) (xs ys : List Bool)
    (hs : e.stacks = Function.update (Function.update d.stacks 0 xs) 1 ys) : Clean e := by
  intro i hi
  have h0 : i ≠ 0 := by intro h; subst i; simp at hi
  have h1 : i ≠ 1 := by intro h; subst i; simp at hi
  simpa [hs, h0, h1] using hc i hi

def predicate (rows : List (List Bool)) (A z j : ℕ) : Bool :=
  (rows.getD (A + j) []).getD z false

theorem visit_row (rows : List (List Bool)) (A W z j : ℕ) (d : Data)
    (hrows : ∀ row ∈ rows, row.length = W) (hlt : A + j < rows.length)
    (hs : d.stacks 33 = rows.flatten) (hA : d.stacks 31 = unary A)
    (hz : d.stacks 32 = unary z) (hw : d.stacks 38 = unary W)
    (hj : d.stacks 39 = unary j) (hc : Clean d) :
    ∃ ticks e, ticks ≤ visitBound A j W z ∧ Eval visit ticks d e ∧
      e.stacks = Function.update (Function.update d.stacks 0
        (if predicate rows A z j then natRecord j ++ d.stacks 0 else d.stacks 0))
        1 (if predicate rows A z j then false :: d.stacks 1 else d.stacks 1) := by
  have hsplit := List.take_append_drop (A + j) rows
  rw [List.drop_eq_getElem_cons hlt] at hsplit
  have hsource : d.stacks 33 = (rows.take (A + j)).flatten ++
      (rows[A + j] ++ (rows.drop (A + j + 1)).flatten) := by
    calc
      d.stacks 33 = rows.flatten := hs
      _ = (rows.take (A + j) ++ rows[A + j] :: rows.drop (A + j + 1)).flatten :=
        congrArg List.flatten hsplit.symm
      _ = _ := by simp only [List.flatten_append, List.flatten_cons]
  have hlen : A + j = (rows.take (A + j)).length := by
    simp [List.length_take, Nat.min_eq_left hlt.le]
  have hword : rows[A + j].length = (d.stacks 38).length := by
    simpa [hw] using hrows rows[A + j] (List.getElem_mem hlt)
  have hearlier : ∀ row ∈ rows.take (A + j), row.length = (d.stacks 38).length := by
    intro row hr
    simpa [hw] using hrows row (List.mem_of_mem_take hr)
  obtain ⟨ticks, e, ht, he, hs'⟩ := visit_eval d (rows.take (A + j)) rows[A + j]
    (rows.drop (A + j + 1)).flatten A j hsource hA hj hlen hword hearlier hc
  refine ⟨ticks, e, ?_, he, ?_⟩
  · simpa [hw, hz] using ht
  · have hp : predicate rows A z j = rows[A + j].getD z false := by
      unfold predicate
      rw [List.getD_eq_getElem _ _ hlt]
    simpa only [hp, hz, List.length_replicate] using hs'

end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
